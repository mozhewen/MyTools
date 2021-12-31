(* ::Package:: *)

(* ::Text:: *)
(*Description:*)
(*	Utility functions for calculating loop integrals. *)
(**)
(*Author: Zhewen Mo (mozhewen@outlook.com, mozw@ihep.ac.cn)*)
(**)
(*Last update: 2021.12.30*)


(* ::Section:: *)
(*Begin*)


If[!ValueQ[Global`$FIREHome],
	MyTools`$FIREHome = "/home/mozhewen/Documents/fire/FIRE6/",
	MyTools`$FIREHome = Global`$FIREHome;
	Remove[Global`$FIREHome]
]


BeginPackage["MyTools`", {"FeynCalc`"}];

ClearAll[Coef012]
ClearAll[Adjoint]
ClearAll[PropExplicit]
ClearAll[EnumSP]
ClearAll[LinearIndepQ]
ClearAll[LinearReduce]

ClearAll[\[CapitalOmega]]

ClearAll[SInt]
ClearAll[FC2SInt]
ClearAll[FC2FIRE]
ClearAll[Idx2SInt]

ClearAll[DisplaySInt]

ClearAll[\[Alpha]]
ClearAll[UF]
ClearAll[ZeroSIntQ]
ClearAll[COrdering]
ClearAll[AlphaStructure]
ClearAll[GroupEquivSInt]
ClearAll[Match2EquivSInt]
ClearAll[GuessTrans]
ClearAll[AP]

ClearAll[CompleteBasis]
ClearAll[Idx]
ClearAll[ExpressByBasis]
ClearAll[GenFIREFiles]
ClearAll[GetFIRETables]

Begin["`Private`"]


(* ::Section:: *)
(*Body*)


(* ::Subsection:: *)
(*Functions that may not be used directly by users*)


(* Package directory *)
pd = DirectoryName[$InputFileName];


Coef012::usage =
"Coef012[expr, lList] gives the coefficients of the quadratic form expr with variables in lList. \
It returns a list {c, b, A} with A quadratic, b linear and c constant coefficients. ";
Coef012::notpos = "Not possible. ";
Coef012[expr_, lList_List] :=
	Module[{exExpr = ExpandScalarProduct[expr],
			vars(* All scalar products *),
			coef(* Coefficients of vars *),
			idx(* indices of the momenta in lList *),
			A = Table[0, Length[lList], Length[lList]], b = Table[0, Length[lList]], c = 0},
		vars = DeleteDuplicates@Cases[exExpr, Pair[_Momentum?(Not@FreeQ[#, Alternatives@@lList]&), _Momentum], {0, \[Infinity]}];
		If[Length[vars] == 0, (* Deal with the special case *)
			c = exExpr,
			{c, coef} = CoefficientArrays[exExpr, vars]
		];
		Do[
			idx = Replace[vars[[i]], 
				Pair[Momentum[k1_, ___], Momentum[k2_, ___]] :> 
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


Adjoint::usage = "Adjoint[m] calculates the adjoint of matrix m. ";
Adjoint[m_?MatrixQ] :=
	Map[Reverse, Minors[Transpose[m]], {0, 1}]Table[(-1)^(i+j), {i, Length[m]}, {j, Length[m]}]


PropExplicit::usage =
"PropExplicit[PropagatorDenominator[p, m]] rewrites the propagator denominator in the explicit form \
\!\(\*SuperscriptBox[\(p\), \(2\)]\)-\!\(\*SuperscriptBox[\(m\), \(2\)]\). ";
PropExplicit[PropagatorDenominator[p_, m_]] := Pair[p, p] - m^2


EnumSP::usage =
"EnumSP[kList, sp] gives all scalar products of momenta in kList. The function used to represent scalar \
products are defined by sp. ";
EnumSP[kList_List, sp_:Times] := sp@@@DeleteDuplicates[Tuples[kList, 2], ContainsExactly]


LinearIndepQ::usage = 
"LinearIndepQ[{b1, b2, ...}, {l1, l2, ...}] check if the quadratic form basis {b1, b2, ...} is linear \
independent modulo constant terms. Momenta l1, l2, ... are used to define variable terms. \
Note that scalar products should be represented in the FeynCalc form Pair[Momentum[l1], Momentum[l2]] \
instead of the FIRE form l1 l2. It's a faster version of LinearReduce[] for only testing the independency \
without actually computing the coefficients. (These is a faster version of LinearReduce[] for full \
functionality by solving the lift problem. However Mathematica has not yet implement a \"lift\" function \
as Singular. )";
LinearIndepQ[basis_List, lList_List] :=
	Module[{basisEx = DeleteCases[ExpandScalarProduct[basis], _?(FreeQ[#, Alternatives@@lList]&)],
			primitives, gb},
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
define variable terms. Note that scalar products should be represented in the FeynCalc form \
Pair[Momentum[l1], Momentum[l2]] instead of the FIRE form l1 l2. ";
LinearReduce::nosln = "No solution is found. ";
LinearReduce::msln = "Solution is not unique. A particular one is chosen. ";
LinearReduce[expr_, basis_List, lList_List] := 
	Module[{c, cList, eq, primitives, coefList, const, sln},
		cList = Array[c, Length[basis]];
		eq = ExpandScalarProduct[expr] - cList . ExpandScalarProduct[basis];
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


(* ::Subsection:: *)
(*Functions that are used by user*)


\[CapitalOmega]::usage =
"\[CapitalOmega][d] is the surface area of a d-dimensional unit sphere. ";
\[CapitalOmega][d_] := (2 \[Pi]^(d/2))/Gamma[d/2]


(* ::Subsubsection:: *)
(*Change representation*)


SInt::usage =
"SInt[{qf1, a1}, {qf2, a2}, ...] represents the scalar integral \
\[Integral]\!\(\*FractionBox[\(1\), \(\*SuperscriptBox[\(qf1\), \(a1\)] \*SuperscriptBox[\(qf2\), \(a2\)] ... \)]\)\[DifferentialD]l1.... ";
SInt[] = 1;  (* Trivial integral *)


FC2SInt::usage =
"FC2SInt[expr, lList] converts FeynCalc amplitudes expr with loop momenta in lList into the SInt[] \
representation. Note that FC2SInt[] does not factor or expand numerators, it just recognizes the form \
of the numerators of the input, which gives users the flexibility to set to the desired numerator form. 
\"KeepOrder\" \[Rule] False | True
    Whether to keep the order of propagators (they are sorted by default). ";
Options[FC2SInt] = {
	"KeepOrder" -> False
};
FC2SInt[expr_, lList_List, OptionsPattern[]] := FeynAmpDenominatorCombine[expr] /.
	c_. Shortest[numer_.] denom_FeynAmpDenominator /; FreeQ[c, Alternatives@@lList] :>
		c (Times@@Cases[#, {x_?(FreeQ[#, Alternatives@@lList]&), a_} :> ExpandScalarProduct[x^-a]] 
		SInt@@If[OptionValue["KeepOrder"] === True, Identity, SortBy[#, First]&]@Cases[#, {x_?(Not@FreeQ[#, Alternatives@@lList]&), a_}]&)[
			MapAt[Minus, FactorList[numer], {All, 2}] ~Join~ Tally@Cases[denom, x_PropagatorDenominator :> PropExplicit[x]]
		]


FC2FIRE::usage =
"FC2FIRE[expr] converts the quadratic form expr in FeynCalc's Pair[] form into FIRE's Times[] form. ";
FC2FIRE[expr_] := FCI[expr] /. Momentum[a_, ___] :> a /. Pair[a_, b_] :> a b


Idx2SInt::usage = 
"Idx2SInt[basis, idxList] reconstructs SInt[] forms from idxList with respect to basis. 
\"KeepOrder\" \[Rule] False | True
    Whether to keep the order of propagators (they are sorted by default). ";
Options[Idx2SInt] = {
	"KeepOrder" -> False
};
Idx2SInt[basis_List, idxList_List, OptionsPattern[]] := 
	(SInt@@If[OptionValue["KeepOrder"] === True, Identity, SortBy[#, First]&]@DeleteCases[{basis, List@@#}\[Transpose], {_, 0}]&) /@ idxList
Idx2SInt[basis_List, idx_Idx, op:OptionsPattern[]] := First@Idx2SInt[basis, {idx}, op]


(* ::Subsubsection:: *)
(*Typesetting*)


ClearAll[SinglePropBox]
SinglePropBox[prop_, a_] :=
	If[a===1,
		If[Head[prop]=!=Plus && Head[prop]=!=Times,
			prop,
			RowBox[{"(", prop, ")"}]
		]
	,(*Else*)
		SuperscriptBox[RowBox[{"(", prop, ")"}], a]
	]


Options[DisplaySInt] = {
	"d" -> "d"
};
DisplaySInt::usage =
"DisplaySInt[expr, lList] displays SInt[...] in expr with loop momenta in lList in a 2D math form. "
DisplaySInt[expr_, lList_List, OptionsPattern[]] :=
	expr/.sint_SInt :> Module[{
			numer = Cases[sint, {prop_, a_/;a<0} :> {prop, -a}],
			denom = Cases[sint, {_, a_/;(a<0)=!=True}]
		},
		DisplayForm[
			RowBox[{"\[Integral]", FractionBox[
				RowBox[Join[
					Riffle[lList, SuperscriptBox["\[DifferentialD]", OptionValue["d"]], {1, -2, 2}],
					Replace[SinglePropBox@@@numer, {ent__}:>{Style["\[Times]", Gray], ent}]
				]],
				RowBox[SinglePropBox@@@denom]
			]}]
		]
	]


(* ::Subsubsection:: *)
(*\[Alpha]-parameterization*)


\[Alpha]::usage = "\[Alpha] parameter returned by UF[] and AP[]. ";


UF::usage = 
"UF[sint, lList] gives the U, F polynomials in \[Alpha]-parameterization in the form {U, F}. ";
UF[sint_SInt, lList_List] :=
	Module[{\[Alpha]List = Array[Subscript[\[Alpha], #]&, Length[sint]],
			Q, c, b, A, U},
		Q = List@@sint[[;;, 1]] . \[Alpha]List;
		{c, b, A} = Coef012[Q, lList];
		{
			U = Simplify@Det[A], 
			(* NOTE: Tr[] has been redefined by FeynCalc. Use TensorContract instead. *)
			(* F = *)Simplify[1/4 TensorContract[ExpandScalarProduct[Adjoint[A] . Outer[Pair, b, b]], {1, 2}] - c U]
		}
	]


ZeroSIntQ::usage = 
"ZeroSIntQ[sint, lList] determines whether sint is a zero integral. ";
ZeroSIntQ[sint_SInt, lList_List, op:OptionsPattern[]] :=
	Module[{U, F},
		{U, F} = UF[Replace[sint, {_, 0} -> Sequence], lList];
		If[U F === 0, True, False]
	]


COrdering::usage =
"COrdering[polyList, vars] gives the arrangements of variables in vars that maximize the POT \
(position over term) canonical order of the polynomial vector polyList. ";
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
    Whether determine the equivalency only in the sense of sector (whether powers are irrelevant). ";
Options[AlphaStructure] = {
	"SectorOnly" -> False
};
AlphaStructure[sint_SInt, lList_List, OptionsPattern[]] :=
	Module[{SectorOnly = OptionValue["SectorOnly"],
			U, F, \[Alpha]List, a, co},
		{U, F} = UF[sint, lList]; 
		(* NOTE: Here \[Alpha]List must be in the canonical order. *)
		\[Alpha]List = Array[Subscript[\[Alpha], #]&, Length[sint]];
		a = List@@sint[[;;, 2]];
		co = COrdering[{
				U, F, 
				If[SectorOnly,
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
    Whether determine the equivalency only in the sense of sector (whether powers are irrelevant). ";
Options[GroupEquivSInt] = {
	"SectorOnly" -> False
};
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
    Whether determine the equivalency only in the sense of sector (whether powers are irrelevant). ";
Options[Match2EquivSInt] = {
	"SectorOnly" -> False
};
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
otherwise it may not give correct answers. ";
GuessTrans[src_List, dest_List, lList_List] := 
	Module[{n = Length[lList], cList, rule, d, eq, coef, sln},
		(* Only select those with Jacobian = \[PlusMinus]1 *)
		cList = Select[Partition[#, n]& /@ Tuples[{-1, 0, 1}, n^2], Abs@Det[#] === 1 &];
		Do[
			rule = Table[lList[[i]] -> Sum[c[[i, j]]lList[[j]], {j, n}] + d[i], {i, n}];
			eq = (FC2FIRE[src]/.rule) - FC2FIRE[dest];
			coef = CoefficientArrays[eq, lList];
			If[AllTrue[coef[[3]], # === 0&, 3],
				sln = Solve[coef[[2]] == 0, Array[d, n]];
				(* coef\[LeftDoubleBracket]1\[RightDoubleBracket] is deemed to be zeros if src and dest match. *)
				If[sln =!= {},
					Return[Expand[rule/.First@sln]]
				]
			],
			{c, cList}
		]
	]


AP::usage =
"AP[propList, lList, d, options...] performs d-dimensional \[Alpha]-parameterization and momentum integration. 
\"eps\" \[Rule] None | ...
    The variable chosen as a positive infinitesimal (even if it has a explicit minus sign. \
For example, \"eps\"\[Rule]-\[Eta] indicates \[Eta]<0), which will appear in the final result. If the default \
value None is chosen, no \[ImaginaryI] \[Epsilon] will be present on the final result.
\"Ieps\" \[Rule] Plus | Minus
    Sign of \[ImaginaryI] \[Epsilon]. If left default, Plus is used. 
\"A\" \[Rule] Plus | Minus
    Whether A is positive | negative definite (assumed to be). If left default, It is set \
to If[Euclidean, Minus, Identity]@*Ieps. 
\"Denom\" \[Rule] Plus | Minus
    Sign inside the denominator of the result. If left default, Plus is used. 
\"SeparateIntegrand\" -> True | False
	Wheher to separate the integrand into three factors: {Mellin part, U part, F part}. Default is False. ";
Options[AP] = {
	"Euclidean" -> False,
	"eps" -> None,
	"Ieps" -> Plus,
	"A" -> Undefined,
	"Denom" -> Plus,
	"SeparateIntegrand" -> False
};
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


(* ::Subsubsection:: *)
(*FIRE interface*)


CompleteBasis::usage =
"CompleteBasis[basis, int, ext, \"AuxiliaryBasis\" \[Rule] {aux1, aux2, ...}] completes basis with respect to \
the specific auxiliary basis aux1, aux2, ... ";
Options[CompleteBasis] = {
	"AuxiliaryBasis" -> None
}
CompleteBasis[basis_List, int_List, ext_List, OptionsPattern[]] :=
	Module[{result = basis, auxBasis},
		auxBasis = If[OptionValue["AuxiliaryBasis"] === None, 
			EnumSP[Join[int, ext], FCI@*SPD]//DeleteCases[#, _?(FreeQ[#, Alternatives@@int]&)]&,
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


Idx::usage = "Idx[a1, a2, ] represents the indices of propagators in a specific basis. ";


ExpressByBasis::usage =
"ExpressByBasis[SIntList, basis, lList] tries to express the propagators of scalar integrals in SIntList \
with respect to basis in the sense of change of variables of loop momenta. The numerators (with negative \
indices) are automatically expanded as linear combinations of basis. ";
ExpressByBasis::guessfail = "Failed to derive momentum transformation rules for scalar integral i = `` \
with propagator \[Rule] basis arrangement = `` \[Rule] ``. "
Options[ExpressByBasis] = {
	"AllMatches" -> False,
	"ShowProgress" -> True
}
ExpressByBasis[sintList_List, basis_List, lList_List, OptionsPattern[]] :=
	Module[{AllMatches = OptionValue["AllMatches"],
			ShowProgress = OptionValue["ShowProgress"],
			printcell,
			basisI = FCI[basis],
			sint, denomPos, denom, numer, b, bList, word, lrules, 
			rt, idx, rs, result},
		bList = Array[b, Length[basisI]];
		DynamicModule[{prog = 0},
			If[ShowProgress === True,
				printcell = PrintTemporary@Row[{
					ProgressIndicator[Dynamic[prog], {0, Length[sintList]}],
					Dynamic[prog], "/", Length[sintList]
				}];
			];
			result = Table[
				rs = {};
				denomPos = Flatten@Position[sint, {_, a_/;a>0}, {1}, Heads -> False];
				denom = sint[[denomPos]];
				Catch@Do[
					rt = Match2EquivSInt[denom, SInt@@({#, 1}&/@(basisI[[can]])), lList, SectorOnly -> True];
					rt = DeleteDuplicatesBy[rt, List@@denom[[#, 2]]&];
					Do[
						(* Deal with the denominator *)
						idx = Table[0, Length[basisI]];
						idx[[can]] = List@@denom[[arrDenom, 2]];

						(* Deal with the numerator *)
						If[Count[sint, {_, a_Integer/;a<0}] > 0 (* Non-trivial numerator *), 
							lrules = GuessTrans[List@@denom[[arrDenom, 1]], basisI[[can]], lList];
							If[lrules === Null,
								Message[ExpressByBasis::guessfail, prog+1, denomPos[[arrDenom]], can]; 
								Continue[];
							];
							numer = Expand[Times@@Cases[sint, {DD_, a_Integer/;a<0} :> (
								(#1 . bList + #2)^-a&@@LinearReduce[DD/.lrules, basisI, lList]
							)]];
						,(*Else*) (* No numerator (numer = 1) *)
							numer = 1;
						];

						word = Join[{Expand@Last[#1]}, First[#1]]&/@CoefficientRules[numer, bList];
						AppendTo[rs, {
							Sum[mono[[1]]Idx@@(idx - mono[[2;;]]), {mono, word}],
							arrDenom -> can
						}];
						If[AllMatches === False, Throw[Null]];
						,
						{arrDenom, rt}
					]
					,
					{can, Subsets[Range@Length[basisI], {Length[denom]}]}
				]; 
				prog++;
				(*Return*)If[AllMatches === True, rs, First[rs, Null]],
				{sint, sintList}
			];
		];
		If[ShowProgress === True, NotebookDelete[printcell]];
		(*Return*)result
	]
	
ExpressByBasis[sint_SInt, basis_List, lList_List, op:OptionsPattern[{"ShowProgress" -> False}]] := First@ExpressByBasis[{sint}, basis, lList, op]


GenFIREFiles::usage = 
"GenFIREFiles[pn, problemName, basis, idxList, internal, external] generates the requisite files for the IBP \
reduction in the C++ version of FIRE6. pn is the internal problem number of FIRE6 which can be set arbitrarily \
under normal circumstances. ";
Options[GenFIREFiles] = {
	"Threads" -> 8,
	"Preferred" -> {},
	"OutDir" :> NotebookDirectory[]
};

GenFIREFiles[pn_Integer, problemName_String, basis_List, idxList_List, int_List, ext_List, OptionsPattern[]] := 
	Module[{
			Threads = OptionValue["Threads"],
			Preferred = OptionValue["Preferred"],
			OutDir = OptionValue["OutDir"],
			basisF = FC2FIRE[basis],
			fileName
		},

		(* 1. Export integral indices *)
		Export[FileNameJoin[{OutDir, StringTemplate["``.wl"][problemName]}], {pn, List@@#}&/@idxList];
		If[Preferred =!= {},
			Export[FileNameJoin[{OutDir, StringTemplate["``.preferred"][problemName]}], {pn, List@@#}&/@Preferred, "WL"];
		];

		(* 2. Export propagator information *)
		Export[FileNameJoin[{OutDir, StringTemplate["``_defs.wl"][problemName]}],
			{
				(*Internal=*)int,
				(*External=*)ext,
				(*Propagators=*)basisF,
				(*Replacements*)Thread[EnumSP[ext] -> EnumSP[ext, FCI@*SPD]]
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
	"varList" -> StringRiffle[Complement[Variables@{EnumSP[ext, FCI@SPD], basisF}, int, ext](*NOTE: To be tested here*), ", "], 
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
does not exist, the C++ version of FIRE6 will be executed by this function. ";
CloseKernels[subker];
ClearAll[subker]
Options[GetFIRETables] = {
	"OutDir" :> NotebookDirectory[]
};

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
			Global`Tables2Rules[fileName, Factor] /. Global`G[_, {idx__}] :> Idx[idx],
			subker,
			DistributedContexts -> Automatic
		]
	]	


(* ::Section:: *)
(*End*)


End[]
EndPackage[]


(* ::Section:: *)
(*Unused*)


(* ::Text:: *)
(*Some functions that are not used but may be required for future work. *)


(****

ClearAll[BilinearLevel]
BilinearLevel[expr_, lList_List] :=
	Switch[Head[expr],
		Plus, Max[BilinearLevel[#, lList]&/@(List@@expr)],
		Times, Total[BilinearLevel[#, lList]&/@(List@@expr)],
		Pair, If[FreeQ[expr, Alternatives@@lList], 0, 1],
		_, 0
	]

****)


(****
GroupSInt::usage =
"GroupSInt[sintList, int, ext] groups scalar integrals into several classes of bases for \
batch processing of FIRE. It returns with {result, lookupTable} where result is a list of grouped \
SInt[] represented as {basis, idxList}, lookupTable\[LeftDoubleBracket]i\[RightDoubleBracket] = {j, k} represents that the i'th SInt[]
in sintList is mapped to the j'th basis and the k'th indices in this basis. NOTE: Propagators \
that appear in a SInt[] should be independent (in particular, duplicate free). It's recommended \
to sort sintList to the reverse order of propagator length before calling this function. ";

Options[GroupSInt] = {
	ShowProgress -> True
}

GroupSInt[sintList_List, int_List, ext_List, OptionsPattern[]] := 
	Module[{
			ShowProgress = OptionValue[ShowProgress],
			basis, idxList, SIntListMod = MapIndexed[{#1, First[#2]}&, sintList], 
			L = Length[int], EE = Length[ext], n,
			curSInt, ptr, newbasis,
			auxBasis = EnumSP[Join[int, ext], FCI@*SPD]//DeleteCases[#, _?(FreeQ[#, Alternatives@@int]&)]&,
			result = {}, lookupTable = Table[0, Length[sintList]]
		},
		n = (L(L+1))/2 + L EE;
		DynamicModule[{prog = 0},
			If[ShowProgress === True,
				PrintTemporary@Row[{
					ProgressIndicator[Dynamic[prog], {0, Length[sintList]}],
					Dynamic[prog], "/", Length[sintList]
				}];
			];
			While[Length[SIntListMod] > 0,
				basis = {}; idxList = {}; ptr = 1;
				While[ptr <= Length[SIntListMod], 
					curSInt = SIntListMod[[ptr, 1]];
					newbasis = Union[ExpandScalarProduct/@(List@@curSInt[[;;, 1]]), ExpandScalarProduct/@basis];
					If[Length[newbasis] > n, ptr++; Continue[]];
					If[Not@LinearIndepQ[newbasis, int], ptr++; Continue[]];
					basis = Union[List@@curSInt[[;;, 1]], basis];  (* Keep the original form for human reading *)
					AppendTo[idxList, (
						If[Length@Cases[curSInt, {#, a_} :> a] > 1, (*Not possible*)Echo[curSInt], FirstCase[curSInt, {#, a_} :> a, 0]]
					)&/@basis];
					lookupTable[[SIntListMod[[ptr, 2]]]] = {Length[result]+1, Length[idxList]};
					SIntListMod = Delete[SIntListMod, ptr];
					prog++;
				];
				(* Add supplemental basis *)
				Do[
					If[LinearIndepQ[Append[basis, aux], int],
						AppendTo[basis, aux];
					],
					{aux, auxBasis}
				];
				AppendTo[result, {basis, PadRight[#, n]&/@idxList}]
			]
		];
		{result, lookupTable}
	]
****)


(****
Options[RunFIRE] = {
	FIREHome -> "/home/mozhewen/Documents/fire/FIRE6/",
	Threads -> 8,
	OutDir :> NotebookDirectory[],
	NoOutput -> False,
	InitialProblemNumber -> 1
};

RunFIRE[basisGroups_List, int_List, ext_List, op:OptionsPattern[]] := 
	Module[{
			FIREHome = OptionValue[FIREHome],
			Threads = OptionValue[Threads],
			OutDir = OptionValue[OutDir],
			NoOutput = OptionValue[NoOutput],
			InitialProblemNumber = OptionValue[InitialProblemNumber],
			ker,
			basis, idxList,
			result = {}
		},
		(* Initialization *)
		ker = LaunchKernels[1];
		ParallelEvaluate[Get@FileNameJoin[{FIREHome, "FIRE6.m"}], ker, DistributedContexts -> Automatic];

		DynamicModule[{prog = 0},
			PrintTemporary@Row[{
				ProgressIndicator[Dynamic[prog], {0, Length[basisGroups]}],
				Dynamic[prog], "/", Length[basisGroups]
			}];
			Do[
				basis = ExpandScalarProduct[basisGroups[[pn, 1]]] /. Pair[Momentum[a_, ___], Momentum[b_, ___]] :> a b;
				idxList = basisGroups[[pn, 2]];
				pn += InitialProblemNumber - 1;

				(* 1.1. Export integral indices *)
				Export[FileNameJoin[{OutDir, StringTemplate["``.m"][pn]}], {pn, #}&/@idxList];
				(* 1.2. Export propagator information *)
				Export[FileNameJoin[{OutDir, StringTemplate["``.wl"][pn]}],
					{
						(*Internal=*)int,
						(*External=*)ext,
						(*Propagators=*)basis,
						(*Replacements*)Thread[EnumSP[ext] -> EnumSP[ext, FCI@*SPD]]
					}
				];

				(* 2. Prepare for FIRE *)
				RunProcess[{"wolframscript", "-file", FileNameJoin[{pd, "prepareFIRE.wls"}], FIREHome, pn}, ProcessDirectory -> OutDir];

				(* 3. Export FIRE configure file *)
				Export[FileNameJoin[{OutDir, StringTemplate["``.config"][pn]}],
					StringTemplate[
"#threads `th`
#variables d, `varList`
#start
#problem `no` `no`.start
#integrals `no`.m
#output `no`.tables
"][<|
	"th" -> Threads, 
	"varList" -> StringRiffle[Complement[Variables@{EnumSP[ext, FCI@SPD], basis}, int, ext](*NOTE: To be tested here*), ", "], 
	"no" -> pn
|>],
					"Text"
				];

				(* 4. Run FIRE *)
				RunProcess[{FileNameJoin[{FIREHome, "bin/FIRE6"}], "-c", pn}, ProcessDirectory -> OutDir];

				(* 5. Add to result *)
				If[Not@NoOutput,
					AppendTo[result, First@ParallelEvaluate[
						Global`Tables2Rules[FileNameJoin[{OutDir, StringTemplate["``.tables"][pn]}], Factor],
						ker,
						DistributedContexts -> Automatic
					]];
				]

				prog++;,
				{pn, Length@basisGroups}
			]
		];

		(* Finish *)
		CloseKernels[ker];
		If[Not@NoOutput, result]
	]
****)


(****
APOld::usage =
"AP[propList, lList, d, options...] performs d-dimensional \[Alpha]-parameterization and momentum integration. 
\"eps\" \[Rule] None | ...
    The variable chosen as a positive infinitesimal (even if it has a explicit minus sign. \
For example, \"eps\"\[Rule]-\[Eta] indicates \[Eta]<0), which will appear in the final result. If the default \
value None is chosen, no \[ImaginaryI] \[Epsilon] will be present on the final result.
\"Ieps\" \[Rule] Plus | Minus
    Sign of \[ImaginaryI] \[Epsilon]. If left default, Plus is used. 
\"A\" \[Rule] Plus | Minus
    Whether A is positive | negative definite (assumed to be). If left default, It is set \
to If[Euclidean, Minus, Identity]@*Ieps. 
\"Denom\" \[Rule] Plus | Minus
    Sign inside the denominator of the result. If left default, Plus is used. ";
Options[APOld] = {
	"Euclidean" -> False,
	"eps" -> None,
	"Ieps" -> Plus,
	"A" -> Undefined,
	"Denom" -> Plus
};
APOld[sint_SInt, lList_List, d_, OptionsPattern[]] :=
	Module[{sgnIeps, sgnA, sgnDenom,
			Q, \[Alpha]List = Array[Subscript[\[Alpha], #]&, Length[sint]],
			a, h = Length[lList],
			A, b, c,
			Q1},
		sgnIeps = OptionValue["Ieps"]; sgnDenom = OptionValue["Denom"];
		If[OptionValue["A"] === Undefined,
			sgnA = If[OptionValue["Euclidean"], Minus, Identity]@*sgnIeps,
			sgnA = OptionValue["A"]
		];
		
		Q = (List@@sint[[;;, 1]] + If[OptionValue["eps"] === None, 0, sgnIeps[I OptionValue["eps"]]]) . \[Alpha]List;
		a = List@@sint[[;;, 2]];

		{c, b, A} = Echo@Coef012[Q, lList];
		Q1 = sgnDenom[1/4 TensorContract[ExpandScalarProduct[Inverse[A] . Outer[Pair, b, b]], {1, 2}] - c];
		<|
			"integrand" -> Simplify[
				((sgnA[1]^h Det[A])^(-d/2) Product[Subscript[\[Alpha], i]^(a[[i]]-1), {i, Length[sint]}])/Q1^(Total[a]-d h/2),
				Assumptions -> AllTrue[\[Alpha]List, # > 0 &]
			],
			"coef" -> Simplify[Times[
				Power[I,
					sgnIeps[-Total[a]
						+sgnA[If[OptionValue["Euclidean"], d h/2, h-d h/2]]
						+sgnDenom[-Total[a] + d h/2]
					]
				],
				\[Pi]^(d h/2) Gamma[Total[a] - d h/2]/Times@@(Gamma/@a)
			]]
		|>
	]
****)
