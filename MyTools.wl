(* ::Package:: *)

(* ::Text:: *)
(*Description:*)
(*	Utility functions for calculating loop integrals. *)
(**)
(*Author: Zhewen Mo (mozhewen@outlook.com, mozw@ihep.ac.cn)*)
(**)
(*Last update: 2021.8.26*)


(* ::Section:: *)
(*Begin*)


BeginPackage["MyTools`", {"FeynCalc`"}];

ClearAll[Coef012]
ClearAll[PropExplicit]
ClearAll[SInt]
ClearAll[EnumSP]
ClearAll[LinearIndepQ]
ClearAll[LinearReduce]

ClearAll[FC2SInt]
ClearAll[GroupSInt]
ClearAll[RunFIRE]
ClearAll[\[Alpha], AP]

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


PropExplicit::usage =
"PropExplicit[PropagatorDenominator[p, m]] rewrites the propagator denominator in the explicit form \
\!\(\*SuperscriptBox[\(p\), \(2\)]\)-\!\(\*SuperscriptBox[\(m\), \(2\)]\). ";
PropExplicit[PropagatorDenominator[p_, m_]] := Pair[p, p] - m^2


SInt::usage =
"SInt[{qf1, a1}, {af2, a2}, ...] represents the scalar integral \
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
"GroupSInt[SIntList, int, ext] groups scalar integrals into several classes of bases for \
batch processing of FIRE. It returns with {result, lookupTable} where result is a list of grouped \
SInt[] represented as {basis, idxList}, lookupTable\[LeftDoubleBracket]i\[RightDoubleBracket] = {j, k} represents that the i'th SInt[]
in SIntList is mapped to the j'th basis and the k'th indices in this basis. NOTE: Propagators \
that appear in a SInt[] should be independent (in particular, duplicate free). It's recommended \
to sort SIntList to the reverse order of propagator length before calling this function. ";
GroupSInt[SIntList_List, int_List, ext_List] := 
	Module[{
			basis, idxList, SIntListMod = MapIndexed[{#1, First[#2]}&, SIntList], 
			L = Length[int], EE = Length[ext], n,
			curSInt, ptr, newbasis,
			auxBasis = Echo[EnumSP[Join[int, ext], FCI@*SPD]//DeleteCases[#, _?(FreeQ[#, Alternatives@@int]&)]&],
			result = {}, lookupTable = Table[0, Length[SIntList]]
		},
		n = (L(L+1))/2 + L EE;
		DynamicModule[{prog = 0},
			PrintTemporary@Row[{
				ProgressIndicator[Dynamic[prog], {0, Length[SIntList]}],
				Dynamic[prog], "/", Length[SIntList]
			}];
			While[Length[SIntListMod] > 0,
				basis = {}; idxList = {}; ptr = 1;
				While[ptr <= Length[SIntListMod], 
					curSInt = SIntListMod[[ptr, 1]];
					newbasis = Union[List@@curSInt[[;;, 1]], basis];
					If[Length[newbasis] > n, ptr++; Continue[]];
					If[Not@LinearIndepQ[newbasis, int], ptr++; Continue[]];
					basis = newbasis;
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

RunFIRE[SIntGroup_List, int_List, ext_List, op:OptionsPattern[]] := 
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
				ProgressIndicator[Dynamic[prog], {0, Length[SIntGroup]}],
				Dynamic[prog], "/", Length[SIntGroup]
			}];
			Do[
				basis = ExpandScalarProduct[SIntGroup[[pn, 1]]] /. Pair[Momentum[a_, ___], Momentum[b_, ___]] :> a b;
				idxList = SIntGroup[[pn, 2]];
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
				{pn, Length@SIntGroup}
			]
		];

		(* Finish *)
		CloseKernels[ker];
		If[Not@NoOutput, result]
	]


\[Alpha]::usage =
"\[Alpha] parameter returned by AP[]. "
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
\"Denom\"\[Rule]Plus | Minus
    Sign inside the denominator of the result. If left default, Plus is used. ";
Options[AP] = {
	"Euclidean" -> False,
	"eps" -> None,
	"Ieps" -> Plus,
	"A" -> Undefined,
	"Denom" -> Plus
};
AP[propList_SInt, lList_List, d_, OptionsPattern[]] :=
	Module[{sgnIeps, sgnA, sgnDenom,
			Q, \[Alpha]List = Array[Subscript[\[Alpha], #]&, Length[propList]],
			a, h = Length[lList],
			A, b, c,
			Q1},
		sgnIeps = OptionValue["Ieps"]; sgnDenom = OptionValue["Denom"];
		If[OptionValue["A"] === Undefined,
			sgnA = If[OptionValue["Euclidean"], Minus, Identity]@*sgnIeps,
			sgnA = OptionValue["A"]
		];
		Q = (List@@propList[[;;, 1]] + If[OptionValue["eps"] === None, 0, sgnIeps[I OptionValue["eps"]]]) . \[Alpha]List;
		a = List@@propList[[;;, 2]];

		{c, b, A} = Echo@Coef012[Q, lList];
		(* NOTE: Tr[] has been redefined by FeynCalc. Use TensorContract instead. *)
		Q1 = sgnDenom[1/4 TensorContract[ExpandScalarProduct[Inverse[A] . Outer[Pair, b, b]], {1, 2}] - c];
		<|
			"integrand" -> Simplify[
				((sgnA[1]^h Det[A])^(-d/2) Product[Subscript[\[Alpha], i]^(a[[i]]-1), {i, Length[propList]}])/Q1^(Total[a]-d h/2),
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
