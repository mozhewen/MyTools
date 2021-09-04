(* ::Package:: *)

(* ::Text:: *)
(*Description:*)
(*	Utility functions for calculating loop integrals. *)
(**)
(*Author: Zhewen Mo (mozhewen@outlook.com, mozw@ihep.ac.cn)*)
(**)
(*Last update: 2021.9.2*)


(* ::Section:: *)
(*Begin*)


BeginPackage["MyTools`", {"FeynCalc`"}];

ClearAll[Coef012]
ClearAll[Adjoint]
ClearAll[PropExplicit]
ClearAll[SInt]
ClearAll[EnumSP]
ClearAll[LinearIndepQ]
ClearAll[LinearReduce]

ClearAll[\[Alpha]]
ClearAll[UF]
ClearAll[COrdering]
ClearAll[GroupEquivSInt]
ClearAll[FindSubsector]
ClearAll[AP]

ClearAll[FC2SInt]
ClearAll[GroupSInt]
ClearAll[RunFIRE]

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


Adjoint[m_?MatrixQ] := 
	Map[Reverse, Minors[Transpose[m]], {0, 1}]Table[(-1)^(i+j), {i, Length[m]}, {j, Length[m]}]


PropExplicit::usage =
"PropExplicit[PropagatorDenominator[p, m]] rewrites the propagator denominator in the explicit form \
\!\(\*SuperscriptBox[\(p\), \(2\)]\)-\!\(\*SuperscriptBox[\(m\), \(2\)]\). ";
PropExplicit[PropagatorDenominator[p_, m_]] := Pair[p, p] - m^2


SInt::usage =
"SInt[{qf1, a1}, {qf2, a2}, ...] represents the scalar integral \
\[Integral]\!\(\*FractionBox[\(1\), \(\*SuperscriptBox[\(qf1\), \(a1\)] \*SuperscriptBox[\(qf2\), \(a2\)] ... \)]\)\[DifferentialD]l1.... ";
SInt[] = 1;  (* Trivial integral *)


EnumSP::usage =
"EnumSP[kList, sp] gives all scalar products of momenta in kList. The function used to represent scalar \
products are defined by sp. ";
EnumSP[kList_List, sp_:Times] := sp@@@DeleteDuplicates[Tuples[kList, 2], ContainsExactly]


LinearIndepQ::usage = 
"LinearIndepQ[{b1, b2, ...}, {l1, l2, ...}] check if the quadratic form basis {b1, b2, ...} is linear \
independent modulo constant terms. Momenta l1, l2, ... are used to define variable terms. \
Note that scalar products should be represented in the FeynCalc form Pair[Momentum[l1], Momentum[l2]] \
instead of the FIRE form l1 l2. It's a faster version of LinearReduce[] for only testing the independency without \
actually computing the coefficients. (These is a faster version of LinearReduce[] for full functionality by \
solving the lift problem. However Mathematica has not yet implement a \"lift\" function as Singular. )";
LinearIndepQ[basis_List, lList_List] :=
	Module[{ 
			basisEx = DeleteCases[ExpandScalarProduct[basis],_?(FreeQ[#, Alternatives@@lList]&)],
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
of b1, b2, ... and constant terms (returned as {{c1, c2, ...}, const}). Momenta l1, l2, ... are used to define \
variable terms. Note that scalar products should be represented in the FeynCalc form \
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
			U = Det[A], 
			(* F = *)1/4 TensorContract[ExpandScalarProduct[Adjoint[A] . Outer[Pair, b, b]], {1, 2}] - c U
		}
	]


COrdering::usage =
"COrdering[polyList, vars, n:-1] gives the arrangements of variables in vars that maximize \
the POT (position over term) canonical order of the polynomial vector polyList. n is used to \
limit the number of the arrangements. ";
COrdering[polyList_List, vars_List, n_Integer:-1] := 
	Module[{word, r, arList, arListNew, powNew, ord, max},
		word = Flatten[MapIndexed[
			Join[{-#2[[1]], Expand@Last[#1]}, First[#1]]&,
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
			arList = If[n >= 0 && n < Length[arList], Take[arList, n], arList];
		];
		arList
	]


GroupEquivSInt::usage = 
"GroupEquivSInt[sintList, lList] groups equivalent scalar integrals. It returns \
{groups, lookupTable}. 
SectorOnly \[Rule] False | True
    Whether determine the equivalency only in the sense of sector (powers are irrelevant). ";
Options[GroupEquivSInt] = {
	SectorOnly -> False
};
GroupEquivSInt[sintList_List, lList_List, OptionsPattern[]] :=
	Module[{alphaStruct, SectorOnly = OptionValue[SectorOnly],
		U, F, \[Alpha]List, a, co, MyHead, 
		groupsRaw, lookupTable = Table[0, Length[sintList]]},
		alphaStruct = MapIndexed[{
			{U, F} = UF[#1, lList]; 
			\[Alpha]List = DeleteDuplicates@Cases[{U, F}, Subscript[\[Alpha], _], \[Infinity]];
			a = List@@#1[[;;, 2]];
			co = COrdering[{
					U, F, 
					If[SectorOnly,
						Nothing,
						(* NOTE: Shift powers because CoefficientRules[] only deals with polynomials. *)
						Product[Subscript[\[Alpha], i]^(a[[i]]-Min[a]), {i, Length[a]}]
					]
				}, 
				\[Alpha]List, 
				1
			];
			{U, F} = {U, F}/.Table[\[Alpha]List[[co[[1, i]]]] -> \[Alpha]List[[i]], {i, Length[\[Alpha]List]}];
			(* Prevent multi-tag in Sow[] *)MyHead[Expand[U], Expand[F], If[SectorOnly, Nothing, a[[co[[1]]]]]],
			#1, First@#2}&,
			sintList
		];
		groupsRaw = GatherBy[alphaStruct, First];
		{
			MapIndexed[(lookupTable[[#1[[3]]]] = #2; #1[[2]])&, groupsRaw, {2}],
			lookupTable
		}
	]


FindSubsector::usage = 
"FindSubsector[high, low] checks whether there is a subsector of high that contains low (by brute force). 
The powers in the SInt[]'s of high and low are irrelevant. ";
FindSubsector[high_SInt, low_SInt, lList_List] :=
	Module[{n = Length[low], can, rs},
		Do[
			If[Length[GroupEquivSInt[{high[[can]], low}, lList, SectorOnly -> True][[1]]] == 1,
				Return[can]
			],
			{can, Subsets[Range@Length[high], {n}]}
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
    Sign inside the denominator of the result. If left default, Plus is used. ";
Options[AP] = {
	"Euclidean" -> False,
	"eps" -> None,
	"Ieps" -> Plus,
	"A" -> Undefined,
	"Denom" -> Plus
};
AP[sint_SInt, lList_List, d_, OptionsPattern[]] :=
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
		(* NOTE: Tr[] has been redefined by FeynCalc. Use TensorContract instead. *)
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


(* ::Subsubsection:: *)
(*FIRE interface*)


FC2SInt::usage =
"FC2SInt[expr, lList] converts FeynCalc amplitudes expr with loop momenta in lList into the SInt[] \
representation. Note that FC2SInt[] does not factor or expand numerator, it just recognizes the form \
of the numerator of the input, which gives users the flexibility to set to the desired numerator form. ";
FC2SInt[expr_, lList_List] := FeynAmpDenominatorCombine[expr] /.
	c_. Shortest[numer_.] denom_FeynAmpDenominator /; FreeQ[c, Alternatives@@lList] :>
		c (Times@@Cases[#, {x_?(FreeQ[#, Alternatives@@lList]&), a_} :> ExpandScalarProduct[x^-a]] 
		SInt@@Sort@Cases[#, {x_?(Not@FreeQ[#, Alternatives@@lList]&), a_}]&)[
			MapAt[Minus, FactorList[numer], {All, 2}] ~Join~ Tally@Cases[denom, x_PropagatorDenominator :> PropExplicit[x]]
		]


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


Options[RunFIRE] = {
	FIREHome -> "/home/mozhewen/Documents/fire/FIRE6/",
	Threads -> 8,
	OutDir :> NotebookDirectory[],
	NoOutput -> False,
	InitialProblemNumber -> 1
};

RunFIRE[sintGroup_List, int_List, ext_List, op:OptionsPattern[]] := 
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
				ProgressIndicator[Dynamic[prog], {0, Length[sintGroup]}],
				Dynamic[prog], "/", Length[sintGroup]
			}];
			Do[
				basis = ExpandScalarProduct[sintGroup[[pn, 1]]] /. Pair[Momentum[a_, ___], Momentum[b_, ___]] :> a b;
				idxList = sintGroup[[pn, 2]];
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
				{pn, Length@sintGroup}
			]
		];

		(* Finish *)
		CloseKernels[ker];
		If[Not@NoOutput, result]
	]


(* ::Section::Closed:: *)
(*End*)


End[]
EndPackage[]


(* ::Section::Closed:: *)
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
