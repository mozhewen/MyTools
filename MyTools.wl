(* ::Package:: *)

(* ::Text:: *)
(*Description:*)
(*	Utility functions for calculating loop integrals. *)
(**)
(*Author: Zhewen Mo (mozhewen@outlook.com, mozw@itp.ac.cn)*)
(**)
(*Mathematica version: 13.3*)
(**)
(*Last update: 2023.12.12*)
(**)
(*TODO:*)
(*	1. Check FP[] & TID[]. *)


(* ::Section:: *)
(*Begin*)


If[!ValueQ[Global`$IExprHome],
	Global`$IExprHome = $HomeDirectory <> "/Packages/IExpr"
]
Needs["IExpr`Feynman`", FileNameJoin[{Global`$IExprHome, "Feynman.wl"}]]


BeginPackage["MyTools`", {"IExpr`Feynman`", "IExpr`Minkowski`", "IExpr`NonAbelian`", "IExpr`SimpleContract`", "IExpr`Tensor`", "IExpr`Utils`"}]

Get[FileNameJoin[{DirectoryName[$InputFileName], "common.wl"}]]


$FIREHome = $HomeDirectory <> "/Packages/fire/FIRE6/"
$KiraExecutable = "/usr/local/bin/kira"
$FermatExecutable = $HomeDirectory <> "/Packages/ferm6/fer64"


(* Utilities *)
ClearAll[Coef012]
ClearAll[PropExplicit]
ClearAll[LinearIndepQ]
ClearAll[LinearReduce]
ClearAll[GatherTally]

(* Change representation *)
ClearAll[IExpr2Plain, Plain2IExpr]
ClearAll[SInt, TInt]
ClearAll[IExpr2Int]
ClearAll[II2SInt]
ClearAll[SInt2Explicit]

(* Statistics *)
ClearAll[RS]

(* Typesetting *)
ClearAll[DisplayInt]

(* Baikov representation & Tensor reduction *)
ClearAll[Gram]
ClearAll[Baikov]
ClearAll[TID, AutoTID]

(* Feynman & \[Alpha]-parameterization *)
ClearAll[\[Alpha]]
ClearAll[\[CapitalDelta]0, FP]
ClearAll[UF]
ClearAll[ZeroSIntQ]
ClearAll[COrdering]
ClearAll[AlphaStructure]
ClearAll[GroupEquivSInt]
ClearAll[Match2EquivSInt]
ClearAll[GuessTrans]
ClearAll[AP]

(* Reduction to a given basis *)
ClearAll[CompleteBasis]
ClearAll[ExpressByBasis, ExpressByBasisParallel]
ClearAll[ReExpressNumerators, ReExpressNumeratorsFool]

(* IBP *)
ClearAll[GenFIREFiles]
ClearAll[GetFIRETables]

ClearAll[GenKiraFiles]
ClearAll[GetKiraTables]


Begin["`Private`"]


(* Package directory *)
pd = DirectoryName[$InputFileName]


(* ::Section:: *)
(*Utilities*)


Coef012::usage =
"Coef012[expr, lList] gives the coefficients of the quadratic form expr with variables in lList. \
It returns a list {c, b, A} with A quadratic, b linear and c constant coefficients. "

Coef012::notpos = "Not possible. "

Coef012[list_List, lList_List] := Coef012[#, lList]& /@ list
Coef012[expr_, lList_List] :=
	Module[{
		exExpr = VecExpand@ContractIdx[expr],
		vars(* All scalar products *),
		coef(* Coefficients of vars *),
		idx(* indices of the momenta in lList *),
		A = Table[0, Length[lList], Length[lList]], b = Table[0, Length[lList]], c = 0
	},
		vars = Cases[Variables[exExpr], \[Delta][Vec[_?(Not@FreeQ[lList, #]&)], _Vec]];
		If[Length[vars] == 0, (* Deal with the special case *)
			c = exExpr,
			{c, coef} = CoefficientArrays[exExpr, vars]
		];
		Do[
			idx = Replace[vars[[i]], 
				\[Delta][Vec[k1_], Vec[k2_]] :> 
					{FirstPosition[lList, k1], FirstPosition[lList, k2]}
			];
			Switch[idx,
			{_?(Not@*MissingQ), _?(Not@*MissingQ)},
				A[[Sequence@@idx]] += coef[[i]]/2; A[[Sequence@@Reverse@idx]] += coef[[i]]/2,
			{_?(Not@*MissingQ), _?MissingQ},
				b[[idx[[1]]]] += coef[[i]] vars[[i]][[2]],
			{_?MissingQ, _?(Not@*MissingQ)},
				b[[idx[[2]]]] += coef[[i]] vars[[i]][[1]],
			{_?MissingQ, _?MissingQ},
				Message[Coef012::notpos];
			],
			{i, Length[vars]}
		];
		(*Return*){c, b, A}
	]


LinearIndepQ::usage =
"LinearIndepQ[{b1, b2, ...}, {l1, l2, ...}] check if the quadratic form basis {b1, b2, ...} is linear \
independent modulo constant terms. Momenta l1, l2, ... are used to define variable terms. \
Note that scalar products should be represented in the IExpr form \[Delta][Vec[l1], Vec[l2]] instead of \
the plain form l1 l2. It's a faster version of LinearReduce[] for only testing the independency \
without actually computing the coefficients. (These is a faster version of LinearReduce[] for full \
functionality by solving the lift problem. However Mathematica has not yet implement a \"lift\" function \
as Singular. )"

LinearIndepQ[basis_List, lList_List] :=
	Module[{
		basisEx = DeleteCases[VecExpand@ContractIdx[basis], _?(FreeQ[#, Alternatives@@lList]&)],
		primitives, gb
	},
		primitives = DeleteCases[Variables[basisEx], _?(FreeQ[#, Alternatives@@lList]&)];
		gb = GroebnerBasis[basisEx, primitives];
		If[Count[gb, _?(Not@FreeQ[#, Alternatives@@lList]&)] < Length[basis],
			Return[False],
			Return[True]
		]
	]


LinearReduce::usage =
"LinearReduce[expr, {b1, b2, ...}, {l1, l2, ...}] reduces the quadratic form expr into a linear combination \
of b1, b2, ... and constant terms (returned as {{c1, c2, ...}, const}). Momenta l1, l2, ... are used to \
define variable terms. Note that scalar products should be represented in the IExpr form \
\[Delta][Vec[l1], Vec[l2]] instead of the plain form l1 l2. "

LinearReduce::nosln = "No solution is found. "
LinearReduce::msln = "Solution is not unique. A particular one is chosen. "

LinearReduce[expr_, basis_List, lList_List] :=
	Module[{c, cList, eq, primitives, coefList, const, sln},
		cList = Array[c, Length[basis]];
		eq = VecExpand@ContractIdx[expr] - cList . VecExpand@ContractIdx[basis];
		primitives = DeleteCases[Variables[eq], _?(FreeQ[#, Alternatives@@lList]&)];
		coefList = CoefficientList[eq, primitives];
		const = coefList[[Sequence@@Table[1, Length[primitives]]]];
		coefList[[Sequence@@Table[1, Length[primitives]]]] = 0;  (* Delete constant terms *)
		sln = Solve[coefList == 0, cList];
		If[Length[sln] == 0, Message[LinearReduce::nosln]; Return[]];
		sln = sln[[1]];
		If[Length[sln] < Length[basis], Message[LinearReduce::msln]];
		{
			cList/.sln/.c[_] -> 0,
			const/.sln/.c[_] -> 0
		}
	]


GatherTally::usage =
"GatherTally[{{form1, a1}, {form1, a2}, {form2, a3}, ...}] gives {{form1, a1+a2}, {form2, a3}} for example. 
GatherTally[{...}, f] uses f[formi] to identify the equivalence of formi. "

GatherTally[list_List, f_:Identity] :=
	With[{a = Expand@Total[Last/@#]}, 
		If[a === 0,
			Nothing,
			{First@First[#], a}
		]
	]& /@ GatherBy[list, f@*First]


(* ::Section:: *)
(*Change representation*)


IExpr2Plain::usage =
"IExpr2Plain[expr] converts the quadratic form expr in IExpr's \[Delta][] form into the plain Times[] form. "

IExpr2Plain[expr_] := ContractIdx[expr] /. \[Delta][a_?VecQ, b_?VecQ] :> (a b /. Vec[v_] :> v)


Plain2IExpr::usage =
"Plain2IExpr[expr, kList] converts the quadratic form expr in the plain Times[] form into IExpr's \[Delta][] form. "

Plain2IExpr[expr_, kList_List] :=
	Enclose@If[Confirm@MomentumQ[expr, kList],
		expr /. {a:(Alternatives@@kList) :> Vec[a]},
	(*Else*)
		expr /. {
			a_^2/;MomentumQ[a, kList] :> 
				\[Delta]@@({a, a}/.{k:(Alternatives@@kList) :> Vec[k]}),
			a_ b_/;MomentumQ[a, kList]&&MomentumQ[b, kList] :> 
				\[Delta]@@({a, b}/.{k:(Alternatives@@kList) :> Vec[k]})
		}
	]


SInt::usage =
"SInt[{qf1, a1}, {qf2, a2}, ...] represents the scalar integral \
\[Integral]\!\(\*FractionBox[\(1\), \(\*SuperscriptBox[\(qf1\), \(a1\)] \*SuperscriptBox[\(qf2\), \(a2\)] ... \)]\)\[DifferentialD]l1.... "


TInt::usage =
"TInt[{{qf1, a1}, {qf2, a2}, ...}, tens] represents the tensor integral \
\[Integral]\[DifferentialD]l1... \!\(\*FractionBox[\(tens\), \(\*SuperscriptBox[\(qf1\), \(a1\)]\\\ \*SuperscriptBox[\(qf2\), \(a2\)]\\\  ... \)]\), where tens is a product of loop momenta with Lorentz indices. "

TInt[scalars_List, 1] := SInt@@scalars


IExpr2Int::usage =
"IExpr2Int[expr, lList] converts IExpr amplitudes expr with loop momenta in lList into the SInt[] & TInt[] \
representation. "

IExpr2Int[list_List, lList_List] := IExpr2Int[#, lList]& /@ list
IExpr2Int[expr_, lList_List] := Enclose@ClassifyFactorList[
	(
		ConfirmAssert[#5 === {}];
		Times@@#1 TInt[
			GatherTally[Join[#2, #3], Expand@*VecExpand@*ContractIdx],
			Times@@#4
		]
	)&,
		(*#1*){c_, a_} /; FreeQ[{c, a}, Alternatives@@lList] :>
			(c^a /. Denom[denom_] :> 1/Simplify@VecExpand@ContractIdx[denom]),
		(*#2*){Denom[denom_], a_} :> {denom, a},
		(*#3*){numer:\[Delta][_Vec, _Vec], a_} :> {numer, -a},
		(*#4*){tens:\[Delta][_Vec, _Idx], a_} :> tens^a,
		(*#5*)rest_ :> rest
][VecExpand[expr], Alternatives@@lList]


II2SInt::usage =
"II2SInt[expr, basis] reconstructs SInt[] forms from II[] expression expr with respect to basis. "

II2SInt[expr_, basis_List, OptionsPattern[]] := expr /. II[as__] :> 
	SInt@@DeleteCases[{basis, {as}}\[Transpose], {_, 0}]


SInt2Explicit::usage =
"SInt2Explicit[expr] converts SInt[] into a explicit fraction"

SInt2Explicit[expr_] := expr /. SInt[props__] :> Times@@Cases[{props}, {x_, a_} :> x^-a]


(* ::Section:: *)
(*Statistics*)


RS::usage =
"RS[sint] returns {r, s} where r(s) is the sum of all indices of the denominator(numerator). 
RS[sint, assum] uses assumptions in assum to determine the positivity. "

RS[sint_SInt, assum_:{}] := {
	Total@Cases[sint, {_, a_/;Simplify[a > 0, assum]} :> a],
	Total@Cases[sint, {_, a_/;Simplify[a < 0, assum]} :> -a]
}


(* ::Section:: *)
(*Typesetting*)


ClearAll[SinglePropBox]
SinglePropBox[prop_, a_] :=
	If[a === 1,
		If[Head[prop] =!= Plus && Head[prop] =!= Times,
			prop,
			RowBox[{"(", prop, ")"}]
		],
	(*Else*)
		SuperscriptBox[RowBox[{"(", prop, ")"}], a]
	]


DisplayInt::usage =
"DisplayInt[expr, lList] displays SInt[...] and TInt[...] in expr with loop momenta in lList in a 2D math form. "

Options[DisplayInt] = {
	"d" -> "d"
}

DisplayInt[expr_, lList_List, OptionsPattern[]] :=
	expr /. (SInt[props__] | TInt[{props__}, tens_]) :> Module[{
			numer = Cases[{props}, {prop_, a_/;a<0} :> {prop, -a}] ~Join~ ({#, 1}&/@{tens}),
			denom = Cases[{props}, {_, a_/;(a<0)=!=True}]
		},
		DisplayForm[
			RowBox[{"\[Integral]", FractionBox[
				RowBox[Join[
					Riffle[Vec/@lList, SuperscriptBox["\[DifferentialD]", OptionValue["d"]], {1, -2, 2}],
					Replace[SinglePropBox@@@numer, {ent__}:>{Style["\[Times]", Gray], ent}]
				]],
				RowBox[SinglePropBox@@@denom]
			]}]
		]
	]


(* ::Section:: *)
(*Baikov representation & Tensor reduction*)


Gram::usage =
"Gram[kList, pList] gives the Gram matrix (\*GridBox[{
{
RowBox[{k1, \[CenterDot], p1}], \[CenterEllipsis], 
RowBox[{k1, \[CenterDot], pn}]},
{\[VerticalEllipsis], \[DescendingEllipsis], \[VerticalEllipsis]},
{
RowBox[{km, \[CenterDot], p1}], \[CenterEllipsis], 
RowBox[{km, \[CenterDot], pn}]}
}]). 
Gram[kList] is equivalent to Gram[kList, kList]. "

Gram[kList_List, pList_List] := Outer[SP, kList, pList]
Gram[kList_List] := Gram[kList, kList]


Baikov::usage =
"Baikov[int, ext, d] returns the integration measure of the d-dimensional integral of \
int = {\!\(\*SubscriptBox[\(l\), \(1\)]\), \!\(\*SubscriptBox[\(l\), \(2\)]\), \[Ellipsis]} with external momenta ext = {\!\(\*SubscriptBox[\(p\), \(1\)]\), \!\(\*SubscriptBox[\(p\), \(2\)]\), \[Ellipsis]}, \!\(\*SuperscriptBox[\(\[DifferentialD]\), \(d\)]\)\!\(\*SubscriptBox[\(l\), \(1\)]\) \!\(\*SuperscriptBox[\(\[DifferentialD]\), \(d\)]\)\!\(\*SubscriptBox[\(l\), \(2\)]\)\[CenterEllipsis] \[Rule] (\[Ellipsis]return\[Ellipsis]) \[DifferentialD]\!\(\*SubscriptBox[\(s\), \(11\)]\) \[DifferentialD]\!\(\*SubscriptBox[\(s\), \(12\)]\)\[CenterEllipsis], \
where \!\(\*SubscriptBox[\(q\), \(i\)]\) = {\!\(\*SubscriptBox[\(l\), \(1\)]\), \[Ellipsis], \!\(\*SubscriptBox[\(p\), \(1\)]\), \[Ellipsis]} and \!\(\*SubscriptBox[\(s\), \(ij\)]\) = \!\(\*SubscriptBox[\(q\), \(i\)]\)\[CenterDot]\!\(\*SubscriptBox[\(q\), \(j\)]\). 
\"WrapIn\" -> f
	Wrap the most complicated Gram determinant in f[]. "

Options[Baikov] = {
	"WrapIn" -> Identity
}

Baikov[int_List, ext_List, d_, OptionsPattern[]] :=
	With[{L = Length[int], EE = Length[ext], all = Join[int, ext]},
	With[{M = L+EE, NN = 1/2 L(L+1)+L EE},
		Simplify@Times[
			\[Pi]^((L(d+1)-NN)/2)/Product[Gamma[(d-M+i)/2], {i, L}],
			OptionValue["WrapIn"][(-1)^(M-1) Det@Gram[all]]^((d-M-1)/2)/((-1)^(EE-1) Det@Gram[ext])^((d-EE-1)/2)
		]
	]]


TID::usage =
"TID[tint, lList, d] performs Tensor Integral Decomposition for tensor integral 'tint' in 'd' dimensions \
with loop momenta given by 'lList'. 
TID[tintList, lList, d] runs TID[] for a list of tensor integrals. "

TID[tintList_List, lList_List, d_] := TID[#, lList, d]& /@ tintList
TID[TInt[props_List, tens_], lList_List, d_] :=
	Module[{DetG, iG, rules4l, numer, \[Eta]s}, 
	With[{
		extList = Echo@Complement[
			DDCasesAll[Expand@VecExpand@ContractIdx@props, Vec[p_] :> p],
			lList
		],
		lPatt = Alternatives@@lList
	},
		If[extList === {}, Return[Indeterminate]];
		DetG = Det@Gram[extList];
		If[Expand@DetG === 0, Return[Indeterminate]];
		iG = Inverse[Gram[extList]];
		rules4l = Table[
			\[Delta][Vec[l_], Idx[Lor, a_]] -> Sum[
				Det@Gram[extList, ReplacePart[extList, j -> lList[[i]]]]/DetG 
				Vec[extList[[j]], Idx[Lor, a]],
				{j, Length[extList]}
			] + Vec[l, Idx[Lor, a]] (* This is (d-Length[extList])-dimensional *),
			{i, Length[lList]}
		];
		numer = Expand@VecExpand[ContractIdx[tens] /. rules4l];
		numer = If[Head[numer] === Plus, List@@numer, {numer}];
		numer = EchoLabel["numer after"]@GatherTally@Replace[
			numer,
			(coef_ |
			 (l1:\[Delta][Vec[lPatt], Idx[Lor, _]]) |
			 HoldPattern@Times[ls:\[Delta][Vec[lPatt], Idx[Lor, _]] ..] |
			 (coef_ (ls:\[Delta][Vec[lPatt], Idx[Lor, _]] ..))
			) /; FreeQ[Times[coef], \[Delta][Vec[lPatt], Idx[Lor, _]]] :> {Times[l1, ls], Times[coef]},
			{1}
		];
		
		(* NOTE: 
			1. ls should not have powers of indexed l, since it should have been contracted and moved
			into coef;
			2. Vec[] in coef are d-dimensional, Vec[] in ls are (d-Length[extList])-dimensional. 
		*)
		With[{ls = Catenate[Table[#1, #2]& @@@ Rest@FactorList[#1]]},
			If[Not@EvenQ@Length[EchoLabel["ls"]@ls],
				(* 0 *)Nothing,
				With[{coef = EchoLabel["coef"]@Simplify@#2,
					  lis = ls /. \[Delta][Vec[lPatt], \[Mu]:Idx[Lor, _]] :> \[Mu]},
					\[Eta]s = MakeMetricProduct[lis, "List"];
					IExpr2Int[
						Times[
							(* These are always d-dimensional *)
							coef Times@@(Denom[#1]^#2& @@@ props),
							(* Should be re-expressed by the d-dimensional ones *)
							EchoLabel["sln"]@LinearSolve[
								(*m=*)Outer[ContractIdx[#1 #2]&, \[Eta]s, \[Eta]s],
								(*b=*)ContractIdx[Times@@ls #]& /@ \[Eta]s
							] . \[Eta]s /. {
								D -> d - Length[extList],
								\[Delta][a_, b_] -> \[Delta][a, b] - (\[Delta][Vec[#], a]&/@extList) . iG . (\[Delta][Vec[#], b]&/@extList)
							}
						],
						lList
					]
				]
			]
		]& @@@ numer //Total //Collect[#, _SInt, Simplify]&
	]]

TID[sint_SInt, lList_List, d_] := sint


AutoTID::usage =
"AutoTID[expr, lList, d] applies TID[] to each TInt[] in 'expr' automatically. "

Options[AutoTID] := {
	Indeterminate -> Identity,
	"ShowProgress" -> False
}
AutoTID[expr_, lList_List, d_, OptionsPattern[]] := Module[{tintList = DDCasesAll[expr, _TInt]},
	expr /. If[OptionValue["ShowProgress"] === True, MapWithProgress, Map][
		(# ->
			(rs |-> If[rs === Indeterminate, OptionValue[Indeterminate][#], rs])@
			QuietEcho@TID[#, lList, d]
		)&, 
		tintList
	] // If[ListQ[expr] && OptionValue["ShowProgress"] === True, 
		MapWithProgress[ContractIdx, #],
		ContractIdx[#]
	]&
]


(* ::Section:: *)
(*Feynman & \[Alpha]-parameterization*)


\[Alpha]::usage = "\[Alpha] parameter returned by UF[] and AP[]. "


\[CapitalDelta]0::usage = "\[CapitalDelta]0 appears in the result of FP[] to indicate the scaleless integral (\[CapitalDelta]0 \[Rule]0). \
\!\(\*SuperscriptBox[\(\[CapitalDelta]0\), \(a\)]\) can be translated into \!\(\*SubscriptBox[\(\[Delta]\), \(a, 0\)]\) for the UV divergence (\[Epsilon] in a is neglected). "


FP::usage =
"FP[int, l, d] performs Feynman parameterization for loop momentum l in d dimensions. \
It's assumed that the denominator have a '+\[ImaginaryI]0' imaginary part and the coefficient of \!\(\*SuperscriptBox[\(l\), \(2\)]\) is positive. 
FP[int, l, d, assum] performs Feynman parameterization on the assumptions assum of the variables in the powers. "

FP[SInt[props__] | TInt[{props__}, tens_], l_, d_, assum_:{}] :=
	Module[{
			denu = Echo@GroupBy[{props}, Which[
					Simplify[Last[#] > 0, assum], 1(* Denominator *),
					Simplify[Last[#] < 0, assum], -1(* Numerator *),
					True, 0
				]&
			], denom, numer, prefac,
			a, n, A, b, c, \[CapitalDelta]
		},
		denom = Lookup[denu, 1, {}]; 
		numer = EchoLabel["numer before"]@Times[
				Times@@((#1^-#2)&@@@Lookup[denu, -1, {}]),
				tens
		];

		a = Total[denom[[;;, 2]]]; n = Length[denom];
		prefac = Product[Subscript[\[Alpha], i]^(denom[[i, 2]] - 1) / Gamma[denom[[i, 2]]], {i, n}];
		{c, b, A} = EchoLabel["cbA"]@Coef012[Sum[Subscript[\[Alpha], i] denom[[i, 1]], {i, n}], {l}];
		A = A[[1, 1]] /. Sum[Subscript[\[Alpha], i], {i, n}] -> 1;
		b = b[[1]];
		\[CapitalDelta] = -(c/A) + \[Delta][b, b]/(4 A^2) // VecExpand // Simplify;
		If[\[CapitalDelta] === 0, \[CapitalDelta] = \[CapitalDelta]0]; (* Scaleless integral *)

		numer = RenumberIndices@Expand@UncontractIdx[VecExpand[numer /. Vec[l] :> Vec[l] - b/(2 A)], SP[l, _]];
		numer = If[Head[numer] === Plus, List@@numer, {numer}];
		numer = EchoLabel["numer after"]@GatherTally@Replace[
			numer,
			(coef_ |
			(l1:\[Delta][Vec[l], Idx[Lor, _]]) |
			 HoldPattern@Times[ls:\[Delta][Vec[l], Idx[Lor, _]]^_. ..] |
			 (coef_ (ls:\[Delta][Vec[l], Idx[Lor, _]]^_. ..))
			) /; FreeQ[Times[coef], l] :> {Times[l1, ls], Times[coef]},
			{1}
		];

		With[{ls = Catenate[Table[#1, #2]& @@@ Rest@FactorList[#1]],
			  coef = EchoLabel["coef"]@#2},
			With[{m = Length[EchoLabel["ls"]@ls]/2,
				  lis = ls /. \[Delta][Vec[l], \[Mu]:Idx[Lor, _]] :> \[Mu]},
				If[Not@IntegerQ[m],
					(* 0 *)Nothing,
					Times[
						prefac (2\[Pi])^d (((-1)^(m-a) I)/(4\[Pi])^(d/2) Gamma[a-m-d/2](1/\[CapitalDelta])^(a-m-d/2)) 1/2^m,
						MakeMetricProduct[lis, "Sym"] coef A^-a // ContractIdx
					]
				]
			]
		]& @@@ numer // Total // Simplify
	]


UF::usage =
"UF[sint, lList] gives the U, F polynomials in \[Alpha]-parameterization in the form {U, F}. Note that \
the powers of the denominators in sint are not checked. "

UF[sint_SInt, lList_List] :=
	Module[{\[Alpha]List = Array[Subscript[\[Alpha], #]&, Length[sint]],
			Q, c, b, A, U},
		Q = List@@sint[[;;, 1]] . \[Alpha]List;
		{c, b, A} = Coef012[Q, lList];
		{
			U = Simplify@Det[A], 
			(* F = *)Simplify[1/4 Tr[Adjugate[A] . VecExpand[Outer[\[Delta], b, b]]] - c U]
		}
	]


ZeroSIntQ::usage =
"ZeroSIntQ[sint, lList] determines whether sint is a zero integral. "

ZeroSIntQ[sint_SInt, lList_List, op:OptionsPattern[]] :=
	Module[{sint2 = Replace[sint, {_, 0} -> Splice[{}, SInt], {1}], U, F, \[Lambda]},
		{U, F} = UF[sint2, lList];
		If[Length[sint2] == 0 || U F === 0, Return[True]];
		AnyTrue[
			Subsets[Array[Subscript[\[Alpha], #]&, Length[sint2]], {1, Length[sint2]-1}], 
			Count[Expand@CoefficientList[U F /. Thread[# -> \[Lambda] #], \[Lambda]], Except[0]] <= 1 &
		]
	]


COrdering::usage =
"COrdering[polyList, vars] gives the arrangements of variables in vars that maximize the POT \
(position over term) canonical order of the polynomial vector polyList. "

COrdering[polyList_List, vars_List] := 
	Module[{word, r, arList, arListNew, powNew, ord, max},
		word = Flatten[MapIndexed[
			Join[{-First[#2], Expand@Last[#1]}, First[#1]]&,
			CoefficientRules[polyList, vars],
			{2}
		], 1];
		r = Range[Length[vars]];
		arList = {{}};  (* Currently derived partial arrangement *)
		While[Length[First[arList]] < Length[vars],
			arListNew = Join@@(Function[ar, Append[ar, #] & /@ Complement[r, ar]]/@arList);
			powNew = (Reverse[ Last/@Sort[word[[;;, Join[{1, 2}, #+2]]]] ])& /@ arListNew;
			ord = Ordering[powNew];
			max = powNew[[Last[ord]]];
			arList = Part[arListNew, Select[ord, powNew[[#]] === max &]];
		];
		arList
	]


AlphaStructure::usage =
"AlphaStructure[sint, lList] returns {{U, F, a}, arr} where U, F polynomials and propagator \
indices a are rearrangeed to the maximal canonical order. The arrangements of the propagators \
of sint for the maximal canonical order is listed in arr. 
\"SectorOnly\" \[Rule] False | True
    Whether determine the equivalency only in the sense of sector (whether powers are irrelevant). "

Options[AlphaStructure] = {
	"SectorOnly" -> False
}
AlphaStructure[sint_SInt, lList_List, OptionsPattern[]] :=
	Module[{SectorOnly = OptionValue["SectorOnly"],
			U, F, \[Alpha]List, a, co},
		{U, F} = UF[sint, lList]; 
		(* NOTE: Here \[Alpha]List must be in the canonical order. *)
		\[Alpha]List = Array[Subscript[\[Alpha], #]&, Length[sint]];
		a = List@@sint[[;;, 2]];
		co = COrdering[{
				U, F, 
				If[SectorOnly === True,
					Nothing,
					(* NOTE: Shift powers because CoefficientRules[] only deals with polynomials. *)
					Product[Subscript[\[Alpha], i]^(a[[i]]-Min[a]), {i, Length[a]}]
				]
			}, 
			\[Alpha]List
		];
		{U, F} = {U, F}/.Table[\[Alpha]List[[co[[1, i]]]] -> \[Alpha]List[[i]], {i, Length[\[Alpha]List]}];

		(*Return*){
			{Expand[U], Expand[F], If[SectorOnly, Nothing, a[[co[[1]]]]]},
			co
		}
	]


GroupEquivSInt::usage =
"GroupEquivSInt[sintList, lList] groups equivalent scalar integrals in sintList. It returns \
{groups, lookupTable} where each item of lookupTable is of the form {{igroup, ipos}, arr} with \
igroup the group index and ipos the index inside this group, arr is one of the arrangements of \
propagators that meet the maximal canonical order in \[Alpha]-representation. If a scalar integral is \
zero, its arr will be set to Null. 
\"SectorOnly\" \[Rule] False | True
    Whether determine the equivalency only in the sense of sector (whether powers are irrelevant). "

Options[GroupEquivSInt] = {
	"SectorOnly" -> False
}
GroupEquivSInt[sintList_List, lList_List, OptionsPattern[]] :=
	Module[{alphaStruct, as,
			groupsRaw, lookupTable = Table[0, Length[sintList]]},
		alphaStruct = MapIndexed[{
			as = AlphaStructure[#1, lList, "SectorOnly" -> OptionValue["SectorOnly"]];
			First[as],
			#1, First@#2, First@Last@as}&,
			sintList
		];
		groupsRaw = GatherBy[alphaStruct, First];
		{
			MapIndexed[
				(lookupTable[[#1[[3]]]] = {
					#2, 
					If[#1[[1, 1]] =!= 0 && #1[[1, 2]] =!= 0, #1[[4]], Null]
				}; 
				#1[[2]])&, 
				groupsRaw, {2}
			],
			lookupTable
		}
	]


Match2EquivSInt::usage =
"Match2EquivSInt[src, dest, lList] tries to find all propagator arrangements of scalar integral src \
that can match the other scalar integral dest by a loop momentum transformation. It returns {} if src \
and dest does not match. It also tries to deal with null integrals. However the arrangements returned \
may not correspond to a valid momentum transformation. 
\"SectorOnly\" \[Rule] False | True
    Whether determine the equivalency only in the sense of sector (whether powers are irrelevant). "

Options[Match2EquivSInt] = {
	"SectorOnly" -> False
}
Match2EquivSInt[src_SInt, dest_SInt, lList_List, OptionsPattern[]] :=
	Module[{alphaStructDest, alphaStructSrc, temp},

		alphaStructDest = AlphaStructure[dest, lList, "SectorOnly" -> OptionValue["SectorOnly"]];

		alphaStructSrc = AlphaStructure[src, lList, "SectorOnly" -> OptionValue["SectorOnly"]];

		If[alphaStructSrc[[1]] === alphaStructDest[[1]] && Length[alphaStructDest[[2, 1]]] === Length[alphaStructSrc[[2, 1]]],
			Assert[Length[alphaStructSrc[[2]]] == Length[alphaStructDest[[2]]]]; (* The number of ways to rearrange src and dest should be the same. *)
			temp = Table[0, Length[alphaStructDest[[2, 1]]]];
			(temp[[alphaStructDest[[2, 1]]]] = #; temp)& /@ alphaStructSrc[[2]]
		,(*Else*)
			{}
		]
	]


GuessTrans::usage =
"GuessTrans[src, dest, lList] tries to transform a list of quadratic forms src to the corresponding \
dest by a linear transformation of loop momenta in lList. It's assumed that src and dest can match, \
otherwise it may not give correct answers. "

GuessTrans::notone = "Rule `` found but Jacobian is not one. "

GuessTrans[src_List, dest_List, lList_List] := 
	Module[{n = Length[lList], c, cList, d, rule, eq, 
			coef, sln4c, sln4d, rs},
		cList = Flatten@Array[c, {n, n}];
		rule = Table[Vec[lList[[i]]] -> Sum[c[i, j]Vec[lList[[j]]], {j, n}] + Vec[d[i]], {i, n}];
		eq = (VecExpand[src]/.rule) - dest;
		coef = Coef012[eq, lList];
		sln4c = Solve[Join[Flatten[coef[[;;, 3]]], #(#^2-1)&/@cList] == 0, cList];
		Do[
			sln4d = Solve[coef[[;;, 2]] == 0 /. onesln4c, Array[Vec[d[#]]&, n]];
			(* coef\[LeftDoubleBracket];;, 1\[RightDoubleBracket] is deemed to be zeros if src and dest match. *)
			If[sln4d =!= {} && AllTrue[Expand@VecExpand[coef[[;;, 1]]/.First@sln4d], # === 0&],
				(* NOTE: This may not always find all the transformations *)
				rs = Expand[rule/.onesln4c/.First@sln4d/.{Vec[_d] -> 0 (* If solution not unique *)}];
				If[Abs@Det[Array[c, {n, n}]/.onesln4c] =!= 1, 
					Message[GuessTrans::notone, rs]; Return[]
				];
				Return[rs]
			],
			{onesln4c, sln4c}
		]
	]


AP::usage =
"AP[sint, lList, d, options...] performs d-dimensional \[Alpha]-parameterization and momentum integration. 
\"eps\" \[Rule] None | ...
    The variable chosen as a positive infinitesimal (even if it has a explicit minus sign. \
For example, \"eps\"\[Rule]-\[Eta] indicates \[Eta]<0), which will appear in the final result. If the default \
value None is chosen, no \[ImaginaryI] \[Epsilon] will be present on the final result.
\"Ieps\" \[Rule] Plus | Minus
    Sign of \[ImaginaryI] \[Epsilon] in each propagator. If left default, Plus is used. 
\"A\" \[Rule] Plus | Minus
    Whether A is positive | negative definite (assumed to be). If left default, It is set \
to If[Euclidean, Minus, Identity]@*Ieps. 
\"Denom\" \[Rule] Plus | Minus
    Sign inside the denominator of the result. If left default, Plus is used. 
\"SeparateIntegrand\" -> True | False
	Wheher to separate the integrand into three factors: {Mellin part, U part, F part}. Default is False. 
NOTE: \"Ieps\" and \"A\" are determined by the specific integral. \"Denom\" can be freely chosen to \
adjust the result to take the principal value. "

Options[AP] = {
	"Euclidean" -> False,
	"eps" -> None,
	"Ieps" -> Plus,
	"A" -> Undefined,
	"Denom" -> Plus,
	"SeparateIntegrand" -> False
}
AP[sint_SInt, lList_List, d_, OptionsPattern[]] :=
	Module[{sgnIeps, sgnA, sgnDenom,
			a, Ta, L = Length[lList],
			U, F, pow},
		sgnIeps = OptionValue["Ieps"]; sgnDenom = OptionValue["Denom"];
		If[OptionValue["A"] === Undefined,
			sgnA = If[OptionValue["Euclidean"], Minus, Identity]@*sgnIeps,
			sgnA = OptionValue["A"]
		];
		a = List@@sint[[;;, 2]]; Ta = Total[a];
		{U, F} = UF[
			If[OptionValue["eps"] === None, 
				sint, 
				MapAt[# + sgnIeps[I OptionValue["eps"]]&, sint, {All, 1}]
			], 
			lList
		];
		<|
			"integrand" -> Simplify[
				If[OptionValue["SeparateIntegrand"] === True, pow=List; List, pow=Power; Times][
					Product[Subscript[\[Alpha], i]^(a[[i]]-1), {i, Length[sint]}],
					pow[(sgnA[1]^L U), (Ta - d (L+1)/2)],
					pow[(sgnA[1]^L sgnDenom[F]), (d L/2 - Ta)]
				],
				Assumptions -> AllTrue[Table[Subscript[\[Alpha], i], {i, Length[sint]}], # > 0 &]
			],
			"coef" -> Simplify[Times[
				Power[I,
					sgnIeps[-Ta
						+sgnA[If[OptionValue["Euclidean"], d L/2, L-d L/2]]
						+sgnDenom[-Ta + d L/2]
					]
				],
				\[Pi]^(d L/2) Gamma[Ta - d L/2]/Times@@(Gamma/@a)
			]]
		|>
	]


(* ::Section:: *)
(*Reduction to a given basis*)


CompleteBasis::usage =
"CompleteBasis[basis, int, ext, \"AuxiliaryBasis\" \[Rule] {aux1, aux2, ...}] completes basis with respect to \
the specific auxiliary basis aux1, aux2, ... "

Options[CompleteBasis] = {
	"AuxiliaryBasis" -> None
}
CompleteBasis[basis_List, int_List, ext_List, OptionsPattern[]] :=
	Module[{result = basis, auxBasis},
		auxBasis = If[OptionValue["AuxiliaryBasis"] === None, 
			SP /@ Plus@@@DeleteCases[
				Subsets[Join[int, ext], {1, 2}],
				_?(FreeQ[#, Alternatives@@int]&)
			], 
			OptionValue["AuxiliaryBasis"]
		];
		Do[
			If[LinearIndepQ[Append[result, aux], int],
				AppendTo[result, aux];
			],
			{aux, auxBasis}
		];
		result
	]


ExpressByBasis::usage =
"ExpressByBasis[sintList, basis, lList] tries to express the propagators of scalar integrals in sintList \
with respect to basis in the sense of change of variables of loop momenta. The numerators (with negative \
indices) are automatically expanded as linear combinations of basis. 
ExpressByBasis[sint, basis, lList] express single scalar integral sint. "

ExpressByBasis::guessfail = "[NOT an error] Failed to derive momentum transformation rules for scalar integral i = `` \
with denominator candidates = `` from the basis. "
ExpressByBasis::linredfail = "Failed to express the numerator in terms of the basis for scalar integral i = ``. "

Options[ExpressByBasis] = {
	"AllMatches" -> False,
	"ExactMatch" -> False,
	"ShowProgress" -> True
}
ExpressByBasis[sintList_List, basis_List, lList_List, OptionsPattern[]] :=
	Module[{AllMatches = OptionValue["AllMatches"],
			ExactMatch = OptionValue["ExactMatch"],
			ShowProgress = OptionValue["ShowProgress"],
			printcell,
			b, bList, denomPos, denom, numer, rt, succ, as, word, lrules, 
			rs, result},
		bList = Array[b, Length[basis]];
		DynamicModule[{prog = 0},
			If[ShowProgress =!= False,
				printcell = PrintTemporary@Row[{
					ProgressIndicator[Dynamic[prog], {0, Length[sintList]}], " ",
					Dynamic[prog], "/", Length[sintList]
				}];
			];
			result = Table[
				rs = {};
				denomPos = Flatten@Position[sint, {_, a_/;a>0}, {1}, Heads -> False];
				denom = sint[[denomPos]];
				Catch@Do[
					rt = If[ExactMatch,
						Quiet[Check[{Permute[Range@Length[can], FindPermutation[
							Expand@VecExpand[List@@denom[[;;, 1]]], Expand@VecExpand@basis[[can]]]
						]}, {}, FindPermutation::norel], FindPermutation::norel],
					(*Else*)
						Match2EquivSInt[denom, SInt@@({#, 1}&/@(basis[[can]])), lList, "SectorOnly" -> True]
					];
					(* Counterexample: {l1^2, (l1-k1)^2, (l1+k2)^2} with massless k1, k2 *)
					(*rt = DeleteDuplicatesBy[rt, List@@denom[[#, 2]]&];*)
					succ = True;
					Do[
						(* Deal with the denominator *)
						as = Table[0, Length[basis]];
						as[[can]] = List@@denom[[arrDenom, 2]];

						(* Deal with the numerator *)
						If[Count[sint, {_, a_Integer/;a<0}] > 0 (* Non-trivial numerator *), 
							lrules = GuessTrans[List@@denom[[arrDenom, 1]], basis[[can]], lList];
							If[lrules === Null, succ = False; Continue[]];
							numer = Expand[Times@@Cases[sint, {DD_, a_Integer/;a<0} :> (
								(#1 . bList + #2)^-a&@@With[{lr = LinearReduce[DD/.lrules, basis, lList]},
									If[lr === Null, Message[ExpressByBasis::linredfail, prog+1]; Throw[Null], lr]
								]
							)]],
						(*Else*) (* No numerator (numer = 1) *)
							numer = 1
						];

						word = Join[{Expand@Last[#1]}, First[#1]]&/@CoefficientRules[numer, bList];
						AppendTo[rs, {
							Sum[mono[[1]]II@@(as - mono[[2;;]]), {mono, word}],
							denomPos[[arrDenom]] -> can
						}];
						succ = True;
						If[AllMatches === False, Throw[Null]],
						{arrDenom, rt}
					];
					If[Not@succ, Message[ExpressByBasis::guessfail, prog+1, can]],
					{can, Subsets[Range@Length[basis], {Length[denom]}]}
				]; 
				prog++;
				(*Return*)If[AllMatches === True, rs, First[rs, Null]],
				{sint, sintList}
			];
		];
		If[ShowProgress === True, NotebookDelete[printcell]];
		(*Return*)result
	]

ExpressByBasis[sint_SInt, basis_List, lList_List, op:OptionsPattern[{"ShowProgress" -> False}]] := 
	First@ExpressByBasis[{sint}, basis, lList, op]


ExpressByBasisParallel::usage =
"ExpressByBasisParallel[sintList, basis, lList] is the same as ExpressByBasis[] but with parallel kernels. "

Options[ExpressByBasisParallel] = {
	"AllMatches" -> False,
	"ExactMatch" -> False
}
ExpressByBasisParallel[sintList_List, basis_List, lList_List, OptionsPattern[]] :=
	Module[{AllMatches = OptionValue["AllMatches"],
			ExactMatch = OptionValue["ExactMatch"],
			sint, 
			b, bList, denomPos, denom, numer, rt, succ, as, word, lrules, 
			rs, result},
		bList = Array[b, Length[basis]];
		result = ParallelTable[
			sint = sintList[[i]];
			rs = {};
			denomPos = Flatten@Position[sint, {_, a_/;a>0}, {1}, Heads -> False];
			denom = sint[[denomPos]];
			Catch@Do[
				rt = If[ExactMatch,
					Quiet[Check[{Permute[Range@Length[can], FindPermutation[
						Expand@VecExpand[List@@denom[[;;, 1]]], Expand@VecExpand@basis[[can]]]
					]}, {}, FindPermutation::norel], FindPermutation::norel],
				(*Else*)
					Match2EquivSInt[denom, SInt@@({#, 1}&/@(basis[[can]])), lList, "SectorOnly" -> True]
				];
				(* Counterexample: {l1^2, (l1-k1)^2, (l1+k2)^2} with massless k1, k2 *)
				(*rt = DeleteDuplicatesBy[rt, List@@denom[[#, 2]]&];*)
				succ = True;
				Do[
					(* Deal with the denominator *)
					as = Table[0, Length[basis]];
					as[[can]] = List@@denom[[arrDenom, 2]];

					(* Deal with the numerator *)
					If[Count[sint, {_, a_Integer/;a<0}] > 0 (* Non-trivial numerator *), 
						lrules = GuessTrans[List@@denom[[arrDenom, 1]], basis[[can]], lList];
						If[lrules === Null, succ = False; Continue[]];
						numer = Expand[Times@@Cases[sint, {DD_, a_Integer/;a<0} :> (
							(#1 . bList + #2)^-a&@@With[{lr = LinearReduce[DD/.lrules, basis, lList]},
								If[lr === Null, Message[ExpressByBasis::linredfail, i]; Throw[Null], lr]
							]
						)]],
					(*Else*) (* No numerator (numer = 1) *)
						numer = 1;
					];

					word = Join[{Expand@Last[#1]}, First[#1]]&/@CoefficientRules[numer, bList];
					AppendTo[rs, {
						Sum[mono[[1]]II@@(as - mono[[2;;]]), {mono, word}],
						denomPos[[arrDenom]] -> can
					}];
					If[AllMatches === False, Throw[Null]],
					{arrDenom, rt}
				];
				If[Not@succ, Message[ExpressByBasis::guessfail, i, can]],
				{can, Subsets[Range@Length[basis], {Length[denom]}]}
			]; 
			(*Return*)If[AllMatches === True, rs, First[rs, Null]],
			{i, Length[sintList]},
			Method -> "FinestGrained",
			DistributedContexts -> Automatic
		];
		(*Return*)result
	]


ReExpressNumerators::usage =
"ReExpressNumerators[sint, basis, lList] re-expresses the numerators in sint as linear \
combinations of the basis. NOTE: Not optimal in speed. ";
ReExpressNumerators[sint_SInt, basis_List, lList_List] := II2SInt[
	ExpressByBasis[sint, basis, lList, "ShowProgress" -> False][[1]],
	basis
] 

ReExpressNumeratorsFool::usage =
"ReExpressNumeratorsFool[sintList, lList, extList], lList: loop momenta, extList: external momenta. "
ReExpressNumeratorsFool[sintList_List, lList_List, extList_List] := 
	ReExpressNumerators[#,
		CompleteBasis[Cases[#, {denom_, i_/;i>0}][[;;,1]], lList, extList],
		lList
	]& /@ sintList


(* ::Section:: *)
(*IBP*)


(* ::Subsection:: *)
(*FIRE interface (obsolete)*)


GenFIREFiles::usage =
"GenFIREFiles[pn, problemName, basis, iiList, internal, external] generates the requisite files for the IBP \
reduction in the C++ version of FIRE6. pn is the internal problem number of FIRE6 which can be set arbitrarily \
under normal circumstances. "

Options[GenFIREFiles] = {
	"Threads" -> 8,
	"Preferred" -> {},
	"OutDir" :> NotebookDirectory[]
}
GenFIREFiles[pn_Integer, problemName_String, basis_List, iiList_List, int_List, ext_List, OptionsPattern[]] :=
	Module[{
			Threads = OptionValue["Threads"],
			Preferred = OptionValue["Preferred"],
			OutDir = OptionValue["OutDir"],
			basisP = IExpr2Plain[basis],
			fileName
		},

		(* 1. Export integral indices *)
		Export[FileNameJoin[{OutDir, StringTemplate["``.wl"][problemName]}], {pn, List@@#}&/@iiList];
		If[Preferred =!= {},
			Export[FileNameJoin[{OutDir, StringTemplate["``.preferred"][problemName]}], {pn, List@@#}&/@Preferred, "WL"];
		];

		(* 2. Export propagator information *)
		Export[FileNameJoin[{OutDir, StringTemplate["``_defs.wl"][problemName]}],
			{
				(*Internal=*)int,
				(*External=*)ext,
				(*Propagators=*)basisP,
				(*Replacements*)Thread[EnumSP[ext] -> EnumSP[ext, SP]]
			}
		];

		(* 3. Prepare for FIRE *)
		RunProcess[{"wolframscript", "-file", FileNameJoin[{pd, "prepareFIRE.wls"}], $FIREHome, problemName}, ProcessDirectory -> OutDir];

		(* 4. Export FIRE configure file *)
		Export[FileNameJoin[{OutDir, StringTemplate["``.config"][problemName]}],
			StringTemplate[
"#threads `th`
#variables d, `varList`
#start
#problem `no` `na`.start
`pf`
#integrals `na`.wl
#output `na`.tables
"][<|
	"th" -> Threads, 
	"varList" -> StringRiffle[Complement[Variables@{EnumSP[ext, SP], basisP}, int, ext](*NOTE: To be tested here*), ", "], 
	"no" -> pn,
	"na" -> problemName,
	"pf" -> If[Preferred=!={}, StringTemplate["#preferred ``.preferred"][problemName], ""]
|>],
			"Text"
		];

		(* 5. Delete obselete table file *)
		fileName = FileNameJoin[{OutDir, problemName <> ".tables"}];
		If[FileExistsQ[fileName], DeleteFile[fileName]];
	]


GetFIRETables::usage =
"GetFIRETables[problemName] gets the result tables of FIRE6 corresponding to problemName. If the *.tables file \
does not exist, the C++ version of FIRE6 will be executed by this function. "

CloseKernels[subker]
ClearAll[subker]
Options[GetFIRETables] = {
	"OutDir" :> NotebookDirectory[]
}
GetFIRETables[problemName_String, OptionsPattern[]] := 
	Module[{
			OutDir = OptionValue["OutDir"],
			fileName, status
		},
		If[!ValueQ[subker] || FailureQ@Quiet@ParallelEvaluate[$KernelID, subker, DistributedContexts -> Automatic],
			subker = First@LaunchKernels[1]
		];
		ParallelEvaluate[Get@FileNameJoin[{$FIREHome, "FIRE6.m"}], subker, DistributedContexts -> Automatic];
		
		fileName = FileNameJoin[{OutDir, problemName <> ".tables"}];
		
		If[Not@FileExistsQ[fileName],
			status = RunProcess[{FileNameJoin[{$FIREHome, "bin/FIRE6"}], "-c", problemName}, ProcessDirectory -> OutDir];
			If[status["ExitCode"] =!= 0, 
				Return[Failure["FIRE6 error",
					<|"MessageTemplate" -> status["StandardError"]|>
				]]
			]
		];

		ParallelEvaluate[
			Global`Tables2Rules[fileName, Factor] /. Global`G[_, {as__}] :> II[as],
			subker,
			DistributedContexts -> Automatic
		]
	]	


(* ::Subsection:: *)
(*Kira interface*)


familyTemp = StringTemplate[
"integralfamilies: 
  - name: \"`name`\"
    loop_momenta: `lList`
    top_level_sectors: [`top`]
    propagators: 
      `props`
    `symIBP`
    `cut`
"]

kinematicsTemp = StringTemplate[
"kinematics: 
  incoming_momenta: `kList`
  kinematic_invariants: 
    `inv`
  scalarproduct_rules: 
    `rep`
  `strbo`
"]

jobsTemp = StringTemplate[
"jobs: 
  - reduce_sectors: 
      reduce: 
        - {topologies: [`name`], sectors: [`top`], r: `r`, s: `s`}
      select_integrals: 
        select_mandatory_list: 
          - [`name`, target]
      `pf`
      run_initiate: true
      `sol`
      integral_ordering: `io`

  - kira2math: 
      target: 
        - [`name`, target]
      reconstruct_mass: true
"]


GenKiraFiles::usage =
"GenKiraFiles[topoName, basis, iiList, int, ext] generates Kira configuration & job files for the IBP reduction. \
Due to the feature of Kira, it's better to check that no scaleless integral appears in the input. "

Options[GenKiraFiles] = {
	"Top" -> Automatic,
	"SymbolicIBP" -> {},
	"CutPropagators" -> {},
	"VarDims" -> {_ -> 1},
	"Unit" -> None, 
	"rs" -> {Automatic, Automatic},
	"Preferred" -> {},
	"RunFirefly" -> False,
	"IntegralOrdering" -> 1,
	"OutDir" :> NotebookDirectory[]
}
GenKiraFiles[topoName_String, basis_List, iiList_List, int_List, ext_List, OptionsPattern[]] := 
	Module[{
			Top = OptionValue["Top"],
			SymbolicIBP = OptionValue["SymbolicIBP"],
			CutPropagators = OptionValue["CutPropagators"],
			VarDims = OptionValue["VarDims"],
			Unit = OptionValue["Unit"],
			rs = OptionValue["rs"],
			Preferred = OptionValue["Preferred"],
			RunFirefly = OptionValue["RunFirefly"],
			IntegralOrdering = OptionValue["IntegralOrdering"],
			OutDir = OptionValue["OutDir"],
			props = IExpr2Plain[basis], rep, inv,
			topLoc, top, dot, rank, denom
		},
		(* 1. Delete old files *)
		DeletePath[FileNameJoin[{OutDir, topoName, "results"}]];
		DeletePath[FileNameJoin[{OutDir, topoName, "sectormappings"}]];
		DeletePath[FileNameJoin[{OutDir, topoName, "tmp"}]];
		DeletePath[FileNameJoin[{OutDir, topoName, "kira.log"}]];
		DeletePath[FileNameJoin[{OutDir, topoName, "preferred"}]];
		DeletePath[FileNameJoin[{OutDir, topoName, "config"}]];

		(* 2. Export configuration information *)
		CreateDirectory[FileNameJoin[{OutDir, topoName, "config"}]];
		FileTemplateApply[familyTemp, 
			<|
				"name" -> topoName,
				"lList" -> EncodeIntoYAML[int, "Type" -> "Inline"],
				"top" -> Switch[Top, Automatic, 2^Length[props]-1, _, Top],
				"props" -> EncodeIntoYAML[{#, 0}& /@ props, 6, "Type" -> "Block"],
				"symIBP" -> Switch[SymbolicIBP, {}, "", _, "symbolic_ibp: " <> EncodeIntoYAML[SymbolicIBP, "Type" -> "Inline"]],
				"cut" -> Switch[CutPropagators, {}, "", _, "cut_propagators: " <> EncodeIntoYAML[CutPropagators, "Type" -> "Inline"]]
			|>,
			FileNameJoin[{OutDir, topoName, "config", "integralfamilies.yaml"}]
		];

		rep = EnumSP[ext, SP];
		inv = Complement[Variables[{props, rep}], int, ext];
		FileTemplateApply[kinematicsTemp, 
			<|
				"kList" -> EncodeIntoYAML[ext, "Type" -> "Inline"],
				"inv" -> EncodeIntoYAML[Join[
						{inv, Replace[inv, VarDims, {1}]}\[Transpose],
						{StringTemplate["b``"][#-1], 0}& /@ SymbolicIBP
					],
					 4, "Type" -> "Block"
				],
				"rep" -> EncodeIntoYAML[{EnumSP[ext, List], rep}\[Transpose], 4, "Type" -> "Block"],
				"strbo" -> Switch[Unit, None, "", _, StringTemplate["symbol_to_replace_by_one: `unit`"][Unit]]
			|>,
			FileNameJoin[{OutDir, topoName, "config", "kinematics.yaml"}]
		];

		(* 3. Export target & preferred files *)
		Export[FileNameJoin[{OutDir, topoName, "target"}], iiList/.II->Symbol[topoName], "Text"];
		If[MatchQ[Preferred, {__}],
			Export[FileNameJoin[{OutDir, topoName, "preferred"}], Preferred/.II->Symbol[topoName], "Text"];
		];

		(* 4. Export job file *)
		topLoc = AnyTrue[#, #>0&]& /@ Transpose[Union[iiList, Preferred]/.II->List];
		top = Sum[If[topLoc[[i]], 2^(i-1), 0, 0], {i, Length[topLoc]}];
		dot = Max[Total@Select[#-1, #>0&]& /@ (Union[iiList, Preferred]/.II->List)];
		denom = Switch[rs[[1]],
			Automatic, Count[topLoc, True] + dot,
			_, rs[[1]]
		];
		rank = Switch[rs[[2]],
			Automatic, Max[-Total@Select[#, #<0&]& /@ (Union[iiList, Preferred]/.II->List)],
			_, rs[[2]]
		];
		FileTemplateApply[jobsTemp,
			<|
				"name" -> topoName,
				"top" -> top,
				"r" -> denom,
				"s" -> rank,
				"pf" -> If[MatchQ[Preferred, {__}], "preferred_masters: preferred", ""],
				"sol" -> Switch[RunFirefly,
					True, "run_firefly: true",
					Back, "run_triangular: true\n      run_firefly: back",
					_, "run_triangular: true\n      run_back_substitution: true"
				],
				"io" -> IntegralOrdering
			|>,
			FileNameJoin[{OutDir, topoName, "jobs.yaml"}]
		];
	]


GetKiraTables::usage =
"GetKiraTables[topoName] gets the results of Kira corresponding to topoName. Note that zero integrals and \
trivial reductions a \[Rule] a may not appear in the result table. "

GetKiraTables::kiraerr = "kira: Exit code `1`. Error message: \n`2`";

Options[GetKiraTables] = {
	"Threads" -> 8,
	"OutDir" :> NotebookDirectory[]
}
GetKiraTables[topoName_String, OptionsPattern[]] := 
	Module[{
			Threads = OptionValue["Threads"],
			OutDir = OptionValue["OutDir"],
			rt
		},
		(* 1. Run Kira *)
		rt = RunProcess[{$KiraExecutable, StringTemplate["--parallel=``"][Threads], "jobs.yaml"},
			ProcessDirectory -> FileNameJoin[{OutDir, topoName}],
			ProcessEnvironment -> <|"FERMATPATH" -> $FermatExecutable|>
		];
		If[rt["ExitCode"] =!= 0 || rt["StandardError"] =!= "",
			Message[GetKiraTables::kiraerr, rt["ExitCode"], rt["StandardError"]]
		];

		(* 5. Get results *)
		Get[FileNameJoin[{OutDir, topoName, "results", topoName, "kira_target.m"}]]/.Symbol[topoName] -> II
	]


(* ::Section:: *)
(*End*)


End[]
EndPackage[]
