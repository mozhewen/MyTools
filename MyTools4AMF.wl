(* ::Package:: *)

(* ::Text:: *)
(*Description:*)
(*	Utility functions for calculating Feynman integrals using the AMFlow package. *)
(**)
(*Author: Zhewen Mo (mozhewen@outlook.com, mozw@ihep.ac.cn)*)
(**)
(*Last update: 2022.3.6*)


(* ::Section:: *)
(*Begin*)


BeginPackage["MyTools4AMF`"];

Get[FileNameJoin[{DirectoryName[$InputFileName], "common.wl"}]];

ClearAll[LinearReduce]
ClearAll[LinearIndepQ]

ClearAll[CompleteBasis]

Begin["`Private`"]


(* ::Section:: *)
(*Body*)


(* Package directory *)
pd = DirectoryName[$InputFileName];


Wrap;
WrapMono[exprList_List, kList_List] := (Total[Wrap/@MonomialList[#]]& /@ exprList)/. Wrap[c_?(FreeQ[#,Alternatives@@kList]&) Shortest[sp_.]] :> c Wrap[sp];
WrapMono[expr:Except[_List], kList_List] := First@WrapMono[{expr}, kList]


LinearReduce::usage = 
"LinearReduce[expr, {b1, b2, ...}, {l1, l2, ...}, {p1, p2, ...}] reduces the quadratic form expr into a \
linear combination of b1, b2, ... and constant terms (returned as {{c1, c2, ...}, const}). Momenta l1, l2, \
... are used to define variable terms. Note that scalar products should be represented in the normal \
product form l1 l2. ";
LinearReduce::nosln = "No solution is found. ";
LinearReduce::msln = "Solution is not unique. A particular one is chosen. ";
LinearReduce[expr_, basis_List, int_List, ext_List] := 
	Module[{c, cList, eq, primitives, coefList, const, sln},
		cList = Array[c, Length[basis]];
		eq = WrapMono[expr, Join[int, ext]] - cList . WrapMono[basis, Join[int, ext]];
		primitives = DeleteDuplicates@Cases[eq, _Wrap?(Not@FreeQ[#, Alternatives@@int]&), \[Infinity]];
		coefList = CoefficientList[eq, primitives];
		const = coefList[[Sequence@@Table[1, Length[primitives]]]];
		coefList[[Sequence@@Table[1, Length[primitives]]]] = 0;  (* Delete constant terms *)
		sln = Solve[coefList == 0, cList];
		If[Length[sln] == 0, Message[LinearReduce::nosln]; Return[]];
		sln = sln[[1]];
		If[Length[sln] < Length[basis], Message[LinearReduce::msln]];
		{
			cList/.sln/.c[_] -> 0,
			const/.sln/.c[_] -> 0/.Wrap->Identity
		}
	]


LinearIndepQ::usage = 
"LinearIndepQ[{b1, b2, ...}, {l1, l2, ...}, {p1, p2, ...}] check if the quadratic forms {b1, b2, ...} are \
linear independent modulo constant terms. Momenta l1, l2, ... are used to define variable terms. \
Note that scalar products should be represented in the normal product form l1 l2. ";
LinearIndepQ[basis_List, int_List, ext_List] :=
	Module[{basisEx = DeleteCases[basis, _?(FreeQ[#, Alternatives@@int]&)],
			primitives, gb},
		basisEx = WrapMono[basisEx, Join[int, ext]];
		primitives = DeleteDuplicates@Cases[basisEx, _Wrap?(Not@FreeQ[#, Alternatives@@int]&), \[Infinity]];
		gb = GroebnerBasis[basisEx, primitives];
		If[Count[gb, _?(Not@FreeQ[#, Alternatives@@int]&)] < Length[basis],
			Return[False],
			Return[True]
		]
	]


(* ::Subsubsection:: *)
(*Utilities for AMFlow*)


CompleteBasis::usage =
"CompleteBasis[basis, int, ext] completes basis with respect to the specific auxiliary basis aux1, aux2, ... ";
CompleteBasis[basis_List, int_List, ext_List] :=
	Module[{result = basis, auxBasis},
		auxBasis = (Plus@@@DeleteCases[
			Subsets[Join[int, ext], {1, 2}],
			_?(FreeQ[#, Alternatives@@int]&)
		])^2;
		Do[
			If[LinearIndepQ[Append[result, aux], int, ext],
				AppendTo[result, aux];
			],
			{aux, auxBasis}
		];
		result
	]


(* ::Section:: *)
(*End*)


End[]
EndPackage[]
