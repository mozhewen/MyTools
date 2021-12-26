(* ::Package:: *)

(* ::Text:: *)
(*Description:*)
(*	Utility functions for deriving differential equations of scalar integrals. This package is separated from MyTools.wl because of name conflicts in FeynCalc and LiteRed. *)
(**)
(*Author: Zhewen Mo (mozhewen@outlook.com, mozw@ihep.ac.cn)*)
(**)
(*Last update: 2021.10.17*)


(* ::Section:: *)
(*Begin*)


If[!ValueQ[Global`$FIREHome],
	MyTools4DEs`$FIREHome = "/home/mozhewen/Documents/fire/FIRE6/",
	MyTools4DEs`$FIREHome = Global`$FIREHome;
	Remove[Global`$FIREHome]
]


BeginPackage["MyTools4DEs`", {"LiteRed`", "Libra`"}];

ClearAll[EnumSP]

ClearAll[Idx]
ClearAll[PD]
ClearAll[GenFIREFile]
ClearAll[RunFIRE]

Begin["`Private`"]


(* ::Section:: *)
(*Body*)


(* Package directory *)
pd = DirectoryName[$InputFileName];


EnumSP::usage =
"EnumSP[kList, sp] gives all scalar products of momenta in kList. The function used to represent scalar \
products are defined by sp. ";
EnumSP[kList_List, sp_:Times] := sp@@@DeleteDuplicates[Tuples[kList, 2], ContainsExactly]


Idx::usage = "Idx[a1, a2, ] represents the indices of propagators in a specific basis. ";


ClearAll[PD]
PD::usage = "PD[expr, x] is a user-defined partial derivative for deriving DEs. \
Addtional definitions for PD[Idx[__], _] should be designated in specific problems. ";
PD[expr_Plus, x_] := PD[#, x]&/@expr
PD[c_ a_, x_]:=PD[c, x] a + c PD[a, x]
PD[expr_?(FreeQ[#, _Idx]&), x_^i_.] := Module[{t}, ((\!\(
\*SubscriptBox[\(\[PartialD]\), \(t\)]\((expr /. x -> 
\*SuperscriptBox[\(t\), \(1/i\)])\)\)) /. t->x^i)]


GenFIREFile::usage =
"GenFIREFile[pn, problemName, basis] generates FIRE start, configure and relevant files for running the \
C++ version of FIRE for IBP reduction. ";
Options[GenFIREFile] = {
	"OutDir" :> NotebookDirectory[]
};
GenFIREFile[pn_Integer, problemName_String, basis_, OptionsPattern[]] := 
	Module[{OutDir = OptionValue["OutDir"]},
		(* 1. Export propagator information *)
		Export[FileNameJoin[{OutDir, StringTemplate["``_defs.wl"][problemName]}],
			{
				(*Internal=*)LMs[basis],
				(*External=*)EMs[basis],
				(*Propagators=*)Ds[basis] /. Vectors`sp -> Times,
				(*Replacements*)Thread[EnumSP[EMs[basis]] -> EnumSP[EMs[basis], Vectors`sp]]
			}
		];
		(* 2. Prepare for FIRE *)
		RunProcess[{"wolframscript", "-file", FileNameJoin[{pd, "prepareFIRE.wls"}], $FIREHome, problemName}, ProcessDirectory -> OutDir];
	]


RunFIRE::usage = 
"RunFIRE[pn, problemName, intName, idxList] uses the files generated by \
GenFIREFile[pn, problemName, basis] to run the C++ version of FIRE to perform IBP reduction for idxList. ";
Options[RunFIRE] = {
	"Threads" -> 8,
	"Preferred" -> {},
	"OutDir" :> NotebookDirectory[]
};
ClearAll[subker]
RunFIRE[pn_Integer, problemName_String, intName_String, idxList_List, OptionsPattern[]] := 
	Module[{
			Threads = OptionValue["Threads"],
			Preferred = OptionValue["Preferred"],
			OutDir = OptionValue["OutDir"],
			int, ext, prop, rep
		},
		If[!ValueQ[subker] || FailureQ@Quiet@ParallelEvaluate[$KernelID, subker, DistributedContexts -> Automatic],
			subker = First@LaunchKernels[1]
		];
		ParallelEvaluate[Get@FileNameJoin[{$FIREHome, "FIRE6.m"}], subker, DistributedContexts -> Automatic];

		(* 1. Export FIRE configure file *)
		{int, ext, prop, rep} = Import[FileNameJoin[{OutDir, StringTemplate["``_defs.wl"][problemName]}]];
		If[MatchQ[Preferred, {__}],
			Export[FileNameJoin[{OutDir, StringTemplate["``.preferred"][problemName]}], {pn, List@@#}&/@Preferred, "WL"];
		];
		Export[FileNameJoin[{OutDir, StringTemplate["``.wl"][intName]}], {pn, List@@#}&/@idxList];
		Export[FileNameJoin[{OutDir, StringTemplate["``.config"][intName]}],
			StringTemplate[
"#threads `th`
#variables d, `varList`
#start
#problem `no` `na`.start
`pf`
#integrals `int`.wl
#output `int`.tables
"][<|
	"th" -> Threads, 
	"varList" -> StringRiffle[Complement[Variables[{prop, rep/.{(_->rhs_) :> rhs}}], int, ext], ", "], 
	"no" -> pn,
	"na" -> problemName,
	"int" -> intName,
	"pf" -> If[Preferred=!={}, StringTemplate["#preferred ``.preferred"][problemName], ""]
|>],
			"Text"
		];

		(* 2. Run FIRE *)
		RunProcess[
			{$FIREHome<>"/bin/FIRE6", "-c", FileNameJoin[{OutDir, intName}]},
			ProcessDirectory -> OutDir
		];
	
		(* 3. Get results *)
		ParallelEvaluate[
			Global`Tables2Rules[FileNameJoin[{OutDir, StringTemplate["``.tables"][intName]}], Factor]/.{Global`G[_, {idx__}] :> Idx[idx]},
			subker,
			DistributedContexts -> Automatic
		]
	]


(* ::Section:: *)
(*End*)


End[]
EndPackage[]