(* ::Package:: *)

(* ::Text:: *)
(*Description:*)
(*	IBP with known basis. *)
(**)
(*Author: Zhewen Mo (mozhewen@outlook.com, mozw@itp.ac.cn)*)
(**)
(*Mathematica version: 13.3*)
(**)
(*Last update: 2023.11.28*)


(* ::Section:: *)
(*Begin*)


(* Package directory *)
pd = DirectoryName[$InputFileName]


Get[FileNameJoin[{pd, "MyTools.wl"}]]


Begin["MyTools`"]


ClearAll[AutoIBP]


Begin["`Private`"]


(* ::Section:: *)
(*Utilities*)


ClearAll[BuildRules4SInt2MIs]
BuildRules4SInt2MIs[no_, sintList_List, iiExprList_List, rules4II_List] := Thread[
	sintList -> (iiExprList /. rules4II /. Global`d -> D // Collect[#, _II, Simplify]& // ReplaceAll[II -> II[no]])
]


(* ::Section:: *)
(*Main function*)


Options[AutoIBP] := {
	"CutPropagators" -> {},
	"ExactMatch" -> False,
	"Threads" -> 8
}


AutoIBP::usage =
"AutoIBP[sintList, basisList, intList, extList] automatically performs IBP with a given list of bases. \
It returns {IBPRules, NoOfTheRest}. "

AutoIBP[sintList_List, basisList_List, intList_List, extList_List:{}, OptionsPattern[]] :=
	Module[{
		printCell, printCell1,
		basis, extEach,
		no = Range@Length[sintList], noVal, noNull,
		ex, iiList, rules4II
	},
		DeletePath[".temp_MyTools4IBP"];
		{
		Catenate@Table[{basis, extEach} = If[Head@Last[basisList[[ii]], Null] === List,
				{Most@basisList[[ii]], Last@basisList[[ii]]},
				{basisList[[ii]], {}}
			];
			printCell = PrintTemporary[StringTemplate["Processing basis `1`/`2`... "][ii, Length[basisList]]];
			ex = ExpressByBasis[sintList[[no]], basis, intList, "ExactMatch" -> OptionValue["ExactMatch"]];
			noVal = Position[ex, Except[Null], {1}, Heads -> False];
			noNull = Position[ex, Null, {1}, Heads -> False];
			iiList = DDCasesAll[ex, _II];
			printCell1 = PrintTemporary[StringTemplate["Matched `1` scalar integral(s). Run IBP for `2` target integral(s)... "][
				Length[noVal], Length[iiList]
			]];
			If[Length[iiList] > 0,
				GenKiraFiles[StringTemplate["basis``"][ii],
					basis, iiList, intList, Union[extList, extEach],
					"CutPropagators" -> With[{cp = OptionValue["CutPropagators"]},
						If[Depth[cp] > 2, cp[[ii]], cp]
					],
					"OutDir" -> ".temp_MyTools4IBP"
				];
				rules4II = GetKiraTables[StringTemplate["basis``"][ii],
					"OutDir" -> ".temp_MyTools4IBP",
					"Threads" -> OptionValue["Threads"]
				];
				If[FailureQ[rules4II], rules4II = {}],
			(*Else*)
				 rules4II = {}
			];
			NotebookDelete[printCell1];
			WithCleanup[
				BuildRules4SInt2MIs[ii,
					sintList[[Extract[no, noVal]]],
					Extract[ex, noVal][[;;, 1]],
					rules4II
				],
				NotebookDelete[printCell];
				no = Extract[no, noNull]
			]
			,
			{ii, Length[basisList]}
		],
		no
		}
	]


(* ::Section:: *)
(*End*)


End[]


End[];
