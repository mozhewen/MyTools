(* ::Package:: *)

(* ::Text:: *)
(*Description:*)
(*	Utility functions for deriving differential equations of scalar integrals. This package is separated from MyTools.wl because of name conflicts in FeynCalc and LiteRed. *)
(**)
(*Author: Zhewen Mo (mozhewen@outlook.com, mozw@ihep.ac.cn)*)
(**)
(*Mathematica version: 13.2*)
(**)
(*Last update: 2022.2.19*)
(**)
(*NOTE: *)
(*	1. Series[] has been redefined in Libra. *)
(**)
(*TODO: *)
(*	(none)*)


(* ::Section:: *)
(*Begin*)


If[!ValueQ[Global`$FIREHome],
	MyTools4DEs`$FIREHome = "/home/mozhewen/Documents/fire/FIRE6/",
	MyTools4DEs`$FIREHome = Global`$FIREHome;
	Remove[Global`$FIREHome]
]


If[!ValueQ[Global`$KiraExecutable],
	MyTools4DEs`$KiraExecutable = "/usr/local/bin/kira",
	MyTools4DEs`$KiraExecutable = Global`$KiraExecutable;
	Remove[Global`$KiraExecutable]
]


If[!ValueQ[Global`$FermatExecutable],
	MyTools4DEs`$FermatExecutable = "/home/mozhewen/Documents/ferl6/fer64",
	MyTools4DEs`$FermatExecutable = Global`$FermatExecutable;
	Remove[Global`$FermatExecutable]
]


If[!ValueQ[Global`$PLTHome],
	MyTools4DEs`$PLTHome = "/media/mozhewen/T7/Loops/Packages/plt",
	MyTools4DEs`$PLTHome = Global`$PLTHome;
	Remove[Global`$PLTHome]
]


BeginPackage["MyTools4DEs`", {"LiteRed`", "Libra`"}];

Get[FileNameJoin[{DirectoryName[$InputFileName], "common.wl"}]];

ClearAll[Plain2LR]
ClearAll[SPExpand]
ClearAll[PD]

ClearAll[GenFIREFiles, RunFIRE]

ClearAll[GenKiraFiles, RunKira]

ClearAll[GPL2HPL, StartPLT, CallPLT, KillPLT]

ClearAll[Wrap, WrapLinearFraction]
ClearAll[GPL, IntGPL, DysonGPL, DysonGPLWithAsy]
ClearAll[WrapEpsPow, IntAsy, DysonAsy, DysonAsyCanonical]
ClearAll[DotConvolve]

Begin["`Private`"]


(* ::Section:: *)
(*Body*)


(* Package directory *)
pd = DirectoryName[$InputFileName];


(* ::Subsection::Closed:: *)
(*Utilities*)


Plain2LR::usage = 
"Plain2LR[expr, kList] converts the quadratic form expr in the plain Times[] form into LiteRed's sp[] form. ";
Plain2LR[expr_, kList_List] :=
	Enclose[Confirm@MomentumQ[expr, kList];
		expr /. {
			a_^2/;MomentumQ[a, kList] :> Vectors`sp[a],
			a_ b_/;MomentumQ[a, kList]&&MomentumQ[b, kList] :> Vectors`sp[a, b]
		}
	, $Failed &]


SPExpand[expr_] := expr /. ex_Vectors`sp :> Distribute[ex] //. Vectors`sp[c_?NumberQ a_, b_] :> c Vectors`sp[a, b]


PD::usage = "PD[expr, x] is a user-defined partial derivative for deriving DEs. \
Addtional definitions for PD[Idx[__], _] should be designated in specific problems. ";
PD[expr_Plus, x_] := PD[#, x]&/@expr
PD[c_ a_, x_] := PD[c, x] a + c PD[a, x]
PD[expr_?(FreeQ[#, _Idx]&), x_^i_.] := Cancel[1/(i x^(i-1)) \!\(
\*SubscriptBox[\(\[PartialD]\), \(x\)]\((expr)\)\)]
PD[idx_Idx, x_^i_] := Collect[1/(i x^(i-1)) PD[idx, x], _Idx]


(* ::Subsection::Closed:: *)
(*FIRE interface*)


GenFIREFiles::usage =
"GenFIREFiles[pn, problemName, basis] generates FIRE start, configure and relevant files for running the \
C++ version of FIRE for IBP reduction. ";
Options[GenFIREFiles] = {
	"OutDir" :> NotebookDirectory[]
};
GenFIREFiles[pn_Integer, problemName_String, basis_, OptionsPattern[]] := 
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
GenFIREFiles[pn, problemName, basis] to run the C++ version of FIRE to perform IBP reduction for idxList. ";
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


(* ::Subsection::Closed:: *)
(*Kira interface*)


familyTemp = StringTemplate[
"integralfamilies: 
  - name: \"`name`\"
    loop_momenta: `lList`
    top_level_sectors: [`top`]
    propagators: 
      `props`
"];

kinematicsTemp = StringTemplate[
"kinematics: 
  incoming_momenta: `kList`
  kinematic_invariants: 
    `inv`
  scalarproduct_rules: 
    `rep`
  `strbo`
"];

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
      run_triangular: true
      run_back_substitution: true

  - kira2math: 
      target: 
        - [`name`, target]
      reconstruct_mass: true
"];


GenKiraFiles::usage =
"GenKiraFiles[problemName, basis] generates Kira configuration files for the IBP reduction. ";
Options[GenKiraFiles] = {
	"Top" -> Automatic,
	"VarDims" -> {_ -> 1},
	"Unit" -> None, 
	"OutDir" :> NotebookDirectory[]
};
GenKiraFiles[topoName_String, basis_, OptionsPattern[]] := 
	Module[{
			Top = OptionValue["Top"],
			VarDims = OptionValue["VarDims"],
			Unit = OptionValue["Unit"],
			OutDir = OptionValue["OutDir"],
			props, rep, inv
		},
		(* 1. Export configuration information *)
		props = {#/.Vectors`sp->Times, 0}& /@ Ds[basis];
		FileTemplateApply[familyTemp, 
			<|
				"name" -> topoName,
				"lList" -> EncodeIntoYAML[LMs[basis], "Type" -> "Inline"],
				"top" -> Switch[Top, Automatic, 2^Length[Ds[basis]]-1, _, Top],
				"props" -> EncodeIntoYAML[props, 6, "Type" -> "Block"]
			|>,
			FileNameJoin[{OutDir, topoName, "config", "integralfamilies.yaml"}]
		];

		rep = EnumSP[EMs[basis], Vectors`sp];
		inv = Complement[Variables[{props, rep}], LMs[basis], EMs[basis]];
		FileTemplateApply[kinematicsTemp, 
			<|
				"kList" -> EncodeIntoYAML[EMs[basis], "Type" -> "Inline"],
				"inv" -> EncodeIntoYAML[{inv, Replace[VarDims]/@inv}\[Transpose], 4, "Type" -> "Block"],
				"rep" -> EncodeIntoYAML[{EnumSP[EMs[basis], List], rep}\[Transpose], 4, "Type" -> "Block"],
				"strbo" -> Switch[Unit, None, "", _, StringTemplate["symbol_to_replace_by_one: `unit`"][Unit]]
			|>,
			FileNameJoin[{OutDir, topoName, "config", "kinematics.yaml"}]
		];
	]


RunKira::usage = 
"RunKira[topoName, idxList] uses the files generated by GenKiraFiles[topoName, basis] to run Kira to perform \
the IBP reduction for idxList. Due to the feature of Kira, it's better to check that no scaleless \
integral appears in the input. ";
Options[RunKira] = {
	"Threads" -> 8,
	"rs" -> {Automatic, Automatic},
	"Preferred" -> {},
	"IntegralOrdering" -> 1,
	"OutDir" :> NotebookDirectory[]
};

RunKira[topoName_String, idxList_List, OptionsPattern[]] := 
	Module[{
			Threads = OptionValue["Threads"],
			rs = OptionValue["rs"],
			Preferred = OptionValue["Preferred"],
			IntegralOrdering = OptionValue["IntegralOrdering"],
			OutDir = OptionValue["OutDir"],
			topLoc, top, dot, rank, denom
		},
		(* 1. Delete old files *)
		DeletePath[FileNameJoin[{OutDir, topoName, "results"}]];
		DeletePath[FileNameJoin[{OutDir, topoName, "sectormappings"}]];
		DeletePath[FileNameJoin[{OutDir, topoName, "tmp"}]];
		DeletePath[FileNameJoin[{OutDir, topoName, "kira.log"}]];
		DeletePath[FileNameJoin[{OutDir, topoName, "preferred"}]];

		(* 2. Export target & preferred files *)
		Export[FileNameJoin[{OutDir, topoName, "target"}], idxList/.Idx->Symbol[topoName], "Text"];
		If[MatchQ[Preferred, {__}],
			Export[FileNameJoin[{OutDir, topoName, "preferred"}], Preferred/.Idx->Symbol[topoName], "Text"];
		];

		(* 3. Export job file *)
		topLoc = AnyTrue[#, #>0&]& /@ Transpose[Union[idxList, Preferred]/.Idx->List];
		top = Sum[If[topLoc[[i]], 2^(i-1), 0, 0], {i, Length[topLoc]}];
		dot = Max[Total@Select[#-1, #>0&]& /@ (Union[idxList, Preferred]/.Idx->List)];
		denom = Switch[rs[[1]],
			Automatic, Count[topLoc, True] + dot,
			_, rs[[1]]
		];
		rank = Switch[rs[[2]],
			Automatic, Max[-Total@Select[#, #<0&]& /@ (Union[idxList, Preferred]/.Idx->List)],
			_, rs[[2]]
		];
		FileTemplateApply[jobsTemp,
			<|
				"name" -> topoName,
				"top" -> top,
				"r" -> denom,
				"s" -> rank,
				"pf" -> If[MatchQ[Preferred, {__}], "preferred_masters: preferred", ""]
			|>,
			FileNameJoin[{OutDir, topoName, "jobs.yaml"}]
		];

		(* 4. Run Kira *)
		RunProcess[{$KiraExecutable, 
				StringTemplate["--parallel=``"][Threads], 
				StringTemplate["--integral_ordering=``"][IntegralOrdering], 
				"jobs.yaml"
			},
			ProcessDirectory -> FileNameJoin[{OutDir, topoName}],
			ProcessEnvironment -> <|"FERMATPATH" -> $FermatExecutable|>
		];

		(* 5. Get results *)
		Get[FileNameJoin[{OutDir, topoName, "results", topoName, "kira_target.m"}]]/.Symbol[topoName]->Idx
	]


(* ::Subsection:: *)
(*Polylogarithms*)


GPL2HPL::usage = 
"GPL2HPL[expr] converts GPL[] in expr into HPL[] by the convention of HPL.m (a-notation). "
GPL2HPL[expr_] := With[{GPLList = DDCasesAll[expr, _GPL]},
	expr /. Thread[GPLList -> Replace[GPLList,
		GPL[r:((0|1|-1)..), x_] :> (-1)^Count[{r}, 1] HPL`HPL[{r}, x],
		{1}
	]]
]


StartPLT::usage = 
"StartPLT[linkName] starts a new process running PolyLogTools and returns the process information. ";
StartPLT[linkName_String:""] := Module[{link, proc, realName},
	Enclose[
		link = ConfirmQuiet@If[linkName === "", LinkCreate[], LinkCreate[linkName]];
		realName = First[link];
		proc = ConfirmQuiet@StartProcess[
			{"wolframscript", "-file", FileNameJoin[{pd, "callPLT.wls"}], realName},
			ProcessDirectory -> $PLTHome
		];
		<|
			"Link" -> link,
			"Process" -> proc
		|>,
		Quiet[LinkClose[link]; KillProcess[proc]; $Failed]&
	]
]


CallPLT::usage = 
"CallPLT[expr, pltObj] evaluates expr by PolyLogTools. ";
CallPLT[expr_, pltObj_Association] := With[{
		link = pltObj["Link"],
		proc = pltObj["Process"]
	},
	If[ProcessStatus[proc] == "Running",
		LinkWrite[link, Hold[expr] /. GPL -> Global`G];
		Return@ReleaseHold[LinkRead[link, Hold] /. Global`G -> GPL];
	,(*Else*)
		Return[$Failed]
	]
]


KillPLT::usage = 
"KillPLT[pltObj] kills the PolyLogTools process designated by pltObj. ";
KillPLT[pltObj_Association] := With[{
		link = pltObj["Link"],
		proc = pltObj["Process"]
	},
	LinkWrite[link, Hold[Quit[0]]];
	Echo@ProcessStatus[proc];
	LinkClose[link];
]


(* ::Subsection:: *)
(*Iterative solution of DEs*)


(* ::Subsubsection:: *)
(*Full solution*)


Wrap::usage = "Wrap[x, a] stands for \!\(\*FractionBox[\(1\), \(x - a\)]\). ";


WrapLinearFraction::usage = 
"WrapLinearFraction[m, x] extracts linear fractions in matrix m and wraps them by Wrap[x, a]. ";
WrapLinearFraction[m_?MatrixQ, x_] := With[{
		polesFinite = Union@Flatten[SolveValues[Denominator@Together[#] == 0,x]& /@ Flatten[m]]
	},
	Apart[Factor[m, Extension -> polesFinite], x] /. {1/(a_. x + b_.) :> 1/a Wrap[x, -b/a]}
]


IntGPL::usage = 
"IntGPL[expr, x] evaluates the indefinite integral of GPLs in expr with repect to x. ";
IntGPL[expr_List, x_] := IntGPL[#, x]& /@ expr
IntGPL[0, x_] := 0
IntGPL[expr_, x_] := With[{exprEx = Expand[expr]}, IntGPL[exprEx, x] /; exprEx=!=expr]
IntGPL[expr_Plus, x_] := IntGPL[#, x]& /@ expr
IntGPL[c_ Shortest[subexpr_], x_]/;FreeQ[c, x] := c IntGPL[subexpr, x]

IntGPL[Wrap[x_, a_], x_] := GPL[a, x]
IntGPL[Wrap[x_, a_]GPL[r__, x_], x_] := GPL[a, r, x]


DysonGPL::usage = 
"DysonGPL[m, {x, x0}, order] calculates the matrix version of the Dyson series of the DEs with \
coefficient matrix m. Note that this function is a naive implementation for the iterative \
solution of the DEs. For high-order iterative solution, DysonGPLWithAsy[] may be more efficient. ";
DysonGPL::unknowint = "Some integrals cannot be expressed by GPLs. ";
DysonGPL[m_?MatrixQ, {x_, x0_}, order_] := Enclose[With[{
		mat = WrapLinearFraction[m, x]
	},
	NestList[
		With[{int = ConfirmBy[IntGPL[(mat . #), x],
			FreeQ[#, IntGPL]&, Message[DysonGPL::unknowint]
		]}, int - (int /. x->x0)]&,
		IdentityMatrix[Length[mat]],
		order
	]
], $Failed&]


DysonGPLWithAsy::usage = 
"DysonGPLWithAsy[m, x, i0] calculates the Dyson series of the DEs with given asymptotic \
solution i0 near x = 0. Note that the rows of i0 correspond to different integral basis, \
the columns of i0 correspond to the increasing \[Epsilon] orders. ";
DysonGPLWithAsy::pltsfail = "Failed to start a PolyLogTools process. ";
DysonGPLWithAsy::pltrfail = "PolyLogTools process returns a failure. ";
DysonGPLWithAsy::unknowint = "Some integrals cannot be expressed by GPLs. ";
DysonGPLWithAsy::asymismatch = "The asymptotic solution does not match the DEs. ";
DysonGPLWithAsy[m_?MatrixQ, x_, i0_?MatrixQ] := Enclose@Module[{
		mat = WrapLinearFraction[m, x],
		order = Dimensions[i0][[2]] - 1,
		plt = Confirm[StartPLT[], Message[DysonGPLWithAsy::pltsfail]],
		x0, boundary, GPLx0List, GPLx0AsyList
	},
	WithCleanup[
		Transpose@FoldList[
			With[{int = ConfirmBy[IntGPL[(mat . #1), x],
					FreeQ[#, IntGPL]&, Message[DysonGPLWithAsy::unknowint]
				]}, 
				boundary = -(int /. x->x0) + (i0[[;;, #2]] /. Log[x] -> GPL[0, x] /. x->x0);
				GPLx0List = DDCasesAll[boundary, GPL[__, x0]];
				GPLx0AsyList = Confirm[
					CallPLT[Global`ExpandPolyLogs[GPLx0List, {x0, 0, 0}], plt],
					Message[DysonGPLWithAsy::pltrfail]
				];
				Plus[int,
					ConfirmBy[
						Collect[boundary /. Thread[GPLx0List -> GPLx0AsyList], GPL[0, x0], Factor],
						FreeQ[#, x0]&, Message[DysonGPLWithAsy::asymismatch]
					]
				]
			]&,
			i0[[;;, 1]],
			Range[order] + 1
		],
		KillPLT[plt]
	]
]


(* ::Subsubsection:: *)
(*Asymptotic solution*)


WrapEpsPow::usage = 
"WrapEpsPow[m, {x, order}, eps] extracts \!\(\*SuperscriptBox[\(x\), \(a\\\ eps\)]\) in matrix m, then expands m to O[x]^order, \
assuming m starts from O[x]^0. ";
WrapEpsPow::unsuppfun = "Unsupported functional form. "
WrapEpsPow[m_?MatrixQ, {x_, order_}, eps_] := Enclose[Module[{Pow}, With[{
		ser = Series[
			m /. x^a_/;Not@FreeQ[a, eps]:> x^Coefficient[a, eps, 0] Pow[Factor[a-Coefficient[a, eps, 0]]], 
			{x, 0, order},
			Analytic -> False
		] + SeriesData[x, 0, {}, order+1, order+1, 1] (* Force SeriesData[] *)
	},
	ConfirmAssert[AllTrue[ser, Head[#] === SeriesData&, 2], Message[WrapEpsPow::unsuppfun]];
	Table[Map[(SeriesCoefficient[#, i] x^i /. Pow[a_] :> x^a)&, ser, {2}], {i, 0, order}]
]], $Failed&]


IntAsy::usage = 
"IntAsy[expr, x] evaluates the indefinite integral \[Integral]\[DifferentialD]x of \!\(\*SuperscriptBox[\(x\), \(a\)]\) in expr. ";
IntAsy[expr_, x_] := IntAsyInternal[Expand[expr], x]

IntAsyInternal[expr_List, x_] := IntAsyInternal[#, x]& /@ expr
IntAsyInternal[0, x_] := 0
IntAsyInternal[expr_Plus, x_] := IntAsyInternal[#, x]& /@ expr
IntAsyInternal[c_ Shortest[subexpr_], x_]/;FreeQ[c, x] := c IntAsyInternal[subexpr, x]

IntAsyInternal[c_, x_]/;FreeQ[c, x] := c x
IntAsyInternal[x_^a_., x_] := 1/(a+1) x^(a+1)
(* NOTE: The default result of Integrate[x^a Log[c x]^n, x] -> 0 as x -> 0 with a > -1 *)
IntAsyInternal[expr:(Log[c_. x_]^n_.)/;(IntegerQ[n]&&Positive[n]), x_] := Integrate[expr, x]
IntAsyInternal[expr:(x_^a_. Log[c_. x_]^n_.)/;(IntegerQ[n]&&Positive[n]), x_] := Integrate[expr, x]


DysonAsy::usage = 
"DysonAsy[m, {x, order}, eps] calculates the Dyson series of the DEs near x = 0 with arbitrary \
initial conditions. m is assumed to be free of 1/x poles as x \[Rule] 0. ";
DysonAsy::unknowint = "Some integrals cannot be calculated, e.g., ``. ";
DysonAsy[m_?MatrixQ, {x_, order_}, eps_, initial_:All] := Enclose[Module[{
		n = Dimensions[m][[1]],
		mat = WrapEpsPow[m, {x, order}, eps], conv
	},
	With[{rs = FoldList[
		ConfirmBy[
			conv = Table[IntAsy[
				Sum[mat[[o-i(*x^(o-i-1)*)]] . #1[[i-#2+2(*x^i*)]], {i, #2-1, Min[o-1, Length[#1]+#2-2]}], 
				x
				], {o, #2, order}],
			FreeQ[#, IntAsy]&, Message[DysonAsy::unknowint, FirstCase[conv, _IntAsy, Null, {0, \[Infinity]}]]
		]&,
		If[initial === All, {IdentityMatrix[n]}, initial],
		Range[order]
	]},
		Table[If[o === 0,
				rs[[1, 1]]
			(*Else*),
				Sum[rs[[i+1, o-i+1]], {i, 1, o}]
			],
			{o, 0, order}
		]
	]
], $Failed&]


DysonAsyCanonical::usage = 
"DysonAsyCanonical[m, {x, order}, eps] calculates the Dyson series of the DEs near x = 0 with arbitrary \
initial conditions specified by C[i]. m is assumed to be of at most single poles at x = 0 and has \
integral-power expansion of x. NOTE: It terms out that this approach is only applicable to the canonical \
forms (proportional to eps). 
\"SimplifyFunction\" \[Rule] Identity | f
	Function used to simplify the expression (default is Identity). 
\"ForceJordan\" \[Rule] True | False
	Whether to force the usage of JordanDecomposition[] (the default is False). 
\"Initial\" -> All | pattern
	Whether to start from the general initial condition or restrict to the eigenvalues that match \!\(\*SuperscriptBox[\(x\), \(pattern\\\ eps\)]\). 
\"ShowProgress\" \[Rule] True | False
	Whether to show progeress (default is False). 
";
DysonAsyCanonical::unsupp = "Unsupported form of matrix m. ";
Options[DysonAsyCanonical] = {
	"SimplifyFunction" -> Identity,
	"ForceJordan" -> False,
	"Initial" -> All,
	"ShowProgress" -> False
};
DysonAsyCanonical[m_?MatrixQ, {x_, order_}, eps_, OptionsPattern[]] := Enclose[Module[{
		mSimp = Apart[Simplify[m], x],
		mRes, U, jordan, sln0, initial,
		m1, T, time, rt
	},
	(* NOTE: Here Series[] is modified by Libra to always give SeriesData[] *)
	ConfirmQuiet@If[AnyTrue[Normal@Series[mSimp, {x, 0, -2}], #=!=0&, 2], 
		Message[DysonAsyCanonical::unsupp]
	];
	mRes = SeriesCoefficient[mSimp, {x, 0, -1}];

	(* U^-1 M U = j *)
	{U, jordan} = If[OptionValue["ForceJordan"] === True || Not@DiagonalizableMatrixQ[mRes],
		Print["Use JordanDecomposition[]"];
		JordanDecomposition[mRes]
	(*Else*),
		Print["Use Eigensystem[]"];
		(* Multiply by common denominators to get a simpler result *)
		{Transpose[(LCM@@@Denominator[#2]) #2], DiagonalMatrix[#1]}& @@ Eigensystem[mRes]
	];
	sln0 = U . Echo[MatrixExp[Integrate[1/x jordan, x]], "\[Integral]jordan", TraditionalForm];
	initial = If[OptionValue["Initial"] === All,
		All,
		{DiagonalMatrix[
			If[MatchQ[#, OptionValue["Initial"]/.List->Alternatives], 1, 0]& /@ Diagonal[jordan]
		]}
	];

	m1 = Inverse[sln0] . (mSimp . sln0 - \!\(
\*SubscriptBox[\(\[PartialD]\), \(x\)]sln0\)) // Factor;
	Echo[m1, "m1", TraditionalForm];
	{time, T} = AbsoluteTiming[Confirm@DysonAsy[m1, {x, order}, eps, initial]];
	If[OptionValue["ShowProgress"] === True, Print@StringTemplate["DysonAsy[] finished in ``s. "][time]];

	(*Return*)
	rt = sln0 . # . Array[C, Dimensions[sln0][[2]]]& /@ T;
	If[OptionValue["ShowProgress"] === True,
		DynamicModule[{prog = {0, 0}},
			PrintTemporary[Dynamic[StringTemplate["Calling SimplifyFunction: order = `1`, i = `2`"][prog[[1]]-1, prog[[2]]]]];
			rt = MapIndexed[(prog = #2; OptionValue["SimplifyFunction"][#1])&, rt, {2}]
		]; rt,
	(*Else*)
		Map[OptionValue["SimplifyFunction"], rt, {2}]
	]
], $Failed&]


DotConvolve::usage =
"DotConvolve[m1, m2, order] calculates {\!\(\*SubscriptBox[\(\[Sum]\), \(i\)]\)m1\[LeftDoubleBracket]i+1\[RightDoubleBracket].m2\[LeftDoubleBracket]j-i+1\[RightDoubleBracket] | j=0, \[Ellipsis], order}. 
DotConvolve[m1, m2, orderList] calculates {\!\(\*SubscriptBox[\(\[Sum]\), \(i\)]\)m1\[LeftDoubleBracket]i+1\[RightDoubleBracket].m2\[LeftDoubleBracket]j-i+1\[RightDoubleBracket] | j \[Element] orderList}. 
";
DotConvolve[m1_List, m2_List, orderList_List] := 
	With[{l1 = Length[m1], l2 = Length[m2]},
		Table[
			Sum[m1[[i+1]] . m2[[j-i+1]], {i, Max[0, j-l2+1], Min[j, l1-1]}],
			{j, orderList}
		]
	]
DotConvolve[m1_List, m2_List, order_Integer] := DotConvolve[m1, m2, Range[0, order]]


(* ::Section:: *)
(*End*)


End[]
EndPackage[]
