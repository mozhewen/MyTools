(* ::Package:: *)

(* ::Text:: *)
(*Description:*)
(*	IBP with known basis. *)
(**)
(*Author: Zhewen Mo (mozhewen@outlook.com, mozw@itp.ac.cn)*)
(**)
(*Mathematica version: 13.3*)
(**)
(*Last update: 2023.12.20*)


(* ::Section:: *)
(*Begin*)


(* Package directory *)
pd = DirectoryName[$InputFileName]


Get[FileNameJoin[{pd, "MyTools.wl"}]]


Begin["MyTools`"]


ClearAll[AutoIBP, AutoTIDAndIBP]


Begin["`Private`"]


(* ::Section:: *)
(*Utilities*)


ClearAll[BuildRules4SInt2MIs]
BuildRules4SInt2MIs[no_, sintList_List, iiExprList_List, rules4II_List] := Thread[
	sintList -> MapWithProgress[
		(# /. rules4II /. Global`d -> D // Collect[#, _II, Simplify]& //
			If[no === Null,
				Identity,
				ReplaceAll[II -> II[no]]
			]
		)&, 
		iiExprList
	]
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
		basisList2 = If[MatchQ[basisList, {__List}], basisList, {basisList}],
		printCell, printCell1,
		basis, extEach,
		no = Range@Length[sintList], noVal, noNull,
		ex, iiList, rules4II
	},
		DeletePath[".temp_MyTools4IBP"];
		{
		Catenate@Table[{basis, extEach} = If[Head@Last[basisList2[[ii]], Null] === List,
				{Most@basisList2[[ii]], Last@basisList2[[ii]]},
				{basisList2[[ii]], {}}
			];
			printCell = PrintTemporary[StringTemplate["Processing basis `1`/`2`... "][ii, Length[basisList2]]];
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
						If[MatchQ[cp, {__List}], cp[[ii]], cp]
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
				BuildRules4SInt2MIs[If[MatchQ[basisList, {__List}], ii, Null],
					sintList[[Extract[no, noVal]]],
					Extract[ex, noVal][[;;, 1]],
					rules4II
				],
				NotebookDelete[printCell];
				no = Extract[no, noNull]
			]
			,
			{ii, Length[basisList2]}
		],
		no
		}
	]


AutoTIDAndIBP::usage =
"AutoTIDAndIBP[expr, basisList, intList, extList] applies TID and IBP to 'expr' automatically. "

AutoTIDAndIBP::ibpinsuff = "Insufficient bases for IBP. ";

Options[AutoTIDAndIBP] := {
	Indeterminate -> Identity,
	"ShowProgress" -> False,

	"CutPropagators" -> {},
	"ExactMatch" -> False,
	"Threads" -> 8
}
AutoTIDAndIBP[expr_, basisList_List, intList_List, extList_List:{}, op:OptionsPattern[]] :=
	Module[{
		printCell,
		tintList = DDCasesAll[expr, _TInt],
		sintList = DDCasesAll[expr, _SInt],
		whichMap = If[OptionValue["ShowProgress"] === True, MapWithProgress, Map],
		tint2sint,
		rules4SInt2MIs, noRest,
		Lorentz,
		rules
	},
		printCell = PrintTemporary["Stage 1: TID"];
		tint2sint = whichMap[
			((rs |-> If[rs === Indeterminate, OptionValue[Indeterminate][#], rs])@
				QuietEcho@TID[#, intList, D]
			)&,
			tintList
		];
		sintList = Union[sintList, DDCasesAll[tint2sint, _SInt]];
		NotebookDelete[printCell];

		printCell = PrintTemporary["Stage 2: IBP"];
		{rules4SInt2MIs, noRest} = AutoIBP[sintList, basisList, intList, extList, FilterRules[op, Options[AutoIBP]]];
		If[noRest =!= {}, Message[AutoTIDAndIBP::ibpinsuff]; 
			Return[sintList[[noRest]]]
		];
		NotebookDelete[printCell];

		WithCleanup[
			(*Init*)printCell = PrintTemporary["Stage 3: Substitute into the original expression"],
			{tint2sint, rules4SInt2MIs};
			
			tint2sint = whichMap[
				(ClassifyFactorList[(Times@@#1 Lorentz[Times@@#2])&,
					{patt_?(FreeQ[Idx[Lor,_]]), p_} :> patt^p,
					{rest_, p_} :> rest^p
				][#, Idx[Lor, _]] /. rules4SInt2MIs
					// Collect[#, {_Lorentz, II[_][__]}, Simplify]&
					// ReplaceAll[Lorentz -> Identity])&,
				tint2sint
			];
			rules = Join[Thread[tintList -> tint2sint], rules4SInt2MIs]; 
			{
				expr /. rules // If[ListQ[expr], whichMap, Construct][ContractIdx, #]&,
				rules
			},
			(*Cleanup*)NotebookDelete[printCell]
		]
	]


(* ::Section:: *)
(*End*)


End[]


End[];
