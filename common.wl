(* ::Package:: *)

(* ::Text:: *)
(*Author: Zhewen Mo (mozhewen@outlook.com, mozw@ihep.ac.cn)*)
(**)
(*Mathematica version: 13.3*)
(**)
(*Last update: 2023.11.5*)


(* Kinematics *)
ClearAll[EnumSP]
ClearAll[MomentumQ]
ClearAll[QuadV, ToSqForm]
ClearAll[\[CapitalOmega]]

(* Scalar integral representations *)
j;
II;
ClearAll[II2j, j2II]

(* Wrappers *)
ClearAll[NSeries0, NSeries0IJ]
ClearAll[DDCasesAll]
ClearAll[PSLQ]
ClearAll[AddToAssoc, RemoveFromAssoc]

(* Asymptotics *)
ClearAll[LeadingPower, LeadingOrderTerm]
ClearAll[ResumLog, \[ScriptCapitalC]]
ClearAll[LeadingAsymptotic0]

(* I/O *)
ClearAll[MapAllStruct]
ClearAll[MapAtValues]
ClearAll[DepthStruct]
ClearAll[ScalarCount]

ClearAll[EncodeIntoYAML]
ClearAll[ToStr]
ClearAll[DeletePath]


Begin["`Private`"]


(* ::Section::Closed:: *)
(*Kinematics*)


EnumSP::usage =
"EnumSP[kList, sp:Times] gives all scalar products of the momenta in kList. The function used to represent \
scalar products are defined by sp. 
EnumSP[{intList, extList}, sp:Times] gives all scalar products of the momenta in intList and extList, excluding \
the ones formed only by those in extList. The function used to represent scalar products are defined by sp. "

EnumSP[{intList_List, extList_List}, sp_:Times] := Join[
	EnumSP[intList, sp],
	Flatten[Outer[sp, intList, extList], 1]
]
EnumSP[kList_List, sp_:Times] := Replace[#, {
	{a_} :> sp[a, a],
	{a_, b_} :> sp[a, b]
}]& /@ Subsets[kList, {1, 2}]


MomentumQ::usage =
"MomentumQ[expr_, kList] checks whether expr is a plain linear (return True) or quadratic (return False) \
form of the momenta in kList. It fails when expr is invalid. "

MomentumQ::invalid = "Invalid expression `1`. "

MomentumQ[p:HoldPattern@Plus[mono__], kList_List] :=
	Enclose[Which[
		AllTrue[{mono}, Confirm@MomentumQ[#, kList]&], True,
		NoneTrue[{mono}, Confirm@MomentumQ[#, kList]&], False,
		True, Confirm[$Failed, Message[MomentumQ::invalid, p]]
	], $Failed &]
MomentumQ[t_Times, kList_List] :=
	Enclose[Switch[
		Total@Cases[FactorList[t],
			{a_?(Confirm@MomentumQ[#, kList]&), i_} :>
			(If[i<0, Confirm@MomentumQ[a^i, kList]]; i)
		],
		0 | 2, False,
		1, True,
		_, Confirm[$Failed, Message[MomentumQ::invalid, t]]
	], $Failed &]
MomentumQ[p:Power[a_, i_], kList_List] :=
	Enclose[If[Confirm@MomentumQ[a, kList],
		Switch[i,
			0 | 2, False,
			1, True,
			_, Confirm[$Failed, Message[MomentumQ::invalid, p]]
		],
		(*Else*)False
	], $Failed &]
MomentumQ[sym_, kList_List] := MatchQ[sym, Alternatives@@kList]


QuadV::usage =
"QuadV[a, x, h, k] stands for a (x - h\!\(\*SuperscriptBox[\()\), \(2\)]\) + k. \
V for \"vertex form\". "

ToSqForm::usage =
"ToSqForm[quad, l, SPrules:{}] constructs the standard form of quadratic form quad with respect to variable l. \
SPrules is used to simplify scalar products of the constant term. 
ToSqForm[quad, {\!\(\*SubscriptBox[\(l\), \(1\)]\), \!\(\*SubscriptBox[\(l\), \(2\)]\), ...}, SPrules:{}] uses \
the first \!\(\*SubscriptBox[\(l\), \(i\)]\) that appears in quad as the variable. 
\"QuadV\" \[Rule] False | True
	Whether use QuadV[] as a wrapper. "

Options[ToSqForm] = {
	"QuadV" -> False
}
ToSqForm[quadList_List, l_, SPrules_List:{}, op:OptionsPattern[]] := ToSqForm[#, l, SPrules, op]& /@ quadList
ToSqForm[quad_, lList_List, SPrules_List:{}, op:OptionsPattern[]] := 
	ToSqForm[quad, FirstCase[lList, _?(MemberQ[Variables[quad],#]&)], SPrules, op]
ToSqForm[quad_, l_, SPrules_List:{}, OptionsPattern[]] := 
	Module[{a = Coefficient[quad, l, 2], b = Coefficient[quad, l, 1], c = Coefficient[quad, l, 0]},
		If[a =!= 0,
			If[OptionValue["QuadV"],
				QuadV[a, l, -b/(2a), Together[Expand[(4 a c - b^2 )/(4a)]//.SPrules]],
				a (Expand[l + b/(2a)])^2 - Together[Expand[(4 a c - b^2)/(4a)]//.SPrules]
			],
		(*Else*)
			quad
		]
	]


\[CapitalOmega]::usage =
"\[CapitalOmega][d] is the surface area of a d-dimensional unit sphere. "

\[CapitalOmega][d_] := (2 \[Pi]^(d/2)) / Gamma[d/2]


(* ::Section:: *)
(*Scalar integral representations*)


II::usage = 
	If[ValueQ[II::usage, Method->"TrialEvaluation"], II::usage <> "\n", ""] \
	<> "II[a1, a2, ...] represents the indices of propagators in a specific basis. "


II2j::usage =
"II2j[family][expr] converts II[a1, a2, ...] in expr into j[family, a1, a2, ...]. "

II2j[family_][expr_] := expr /. II[as__] :> j[family, as]


j2II::usage =
"j2II[expr] converts j[family, a1, a2, ...] in expr into II[a1, a2, ...]. "

j2II::mulfam = "Multiple families `` of j can not be converted into II simultaneously. "

j2II[expr_] :=
	Enclose[Module[{familyList = {}},
		expr /. j[family_, as__] :> (
			familyList = Union[familyList, {family}]; 
			ConfirmAssert[Length[familyList] <= 1, Message[j2II::mulfam, familyList]]; 
			II[as]
		)
	], $Failed &]


(* ::Section:: *)
(*Wrappers*)


NSeries0::usage =
"NSeries0[expr, eps, order] is a wrapper for Normal@Series[expr, {eps, 0, order}]. "

NSeries0[expr_, eps_, order_] := Normal@Series[expr, {eps, 0, order}]
NSeries0[expr_, eps_, order_, assum_] := Normal@Series[expr, {eps, 0, order}, Assumptions -> assum]


NSeries0IJ::usage =
"NSeries0IJ[expr, eps, {ordI, ordJ}] Choose the \!\(\*SuperscriptBox[\(eps\), \(ordI\)]\) to \!\(\*SuperscriptBox[\(eps\), \(ordJ\)]\) terms of the series expansion of expr. "

NSeries0IJ[expr_, eps_, {ordI_, ordJ_}] := Sum[eps^n SeriesCoefficient[expr, {eps, 0, n}], {n, ordI, ordJ}]


DDCasesAll::usage =
"DDCasesAll[expr, pattern] is a wrapper for DeleteDuplicates@Cases[expr, pattern, All]. "

DDCasesAll[expr_, pattern_] := DeleteDuplicates@Cases[expr, pattern, All]


PSLQ::usage =
"PSLQ[num, xList, bound] tries to express num as a linear combination of the numbers in xList. \
bound is used to constrain the magnitude of the numerators and denominators of the coefficients. "

PSLQ[num_Real, xList_List, bound_:10000] := Enclose[With[{
		result = ConfirmQuiet@FindIntegerNullVector[Append[xList, num], Sqrt[Length[xList]+1] bound]
	},
	-(Most[result] / Last[result])
], num&]


AddToAssoc::usage =
"AddToAssoc[assoc, key -> value] adds a key-value pair to assoc. 
AddToAssoc[assoc, list] adds a list of key-value pairs. "

SetAttributes[AddToAssoc, HoldFirst]
AddToAssoc[assoc_, r_Rule] := AppendTo[assoc, r]
AddToAssoc[assoc_, rules_List] := (assoc = Join[assoc, Association[rules]])


RemoveFromAssoc::usage =
"RemoveFromAssoc[assoc, key] removes key from assoc. 
RemoveFromAssoc[assoc, key1, key2, ...] removes a sequence of keys from assoc. "

SetAttributes[RemoveFromAssoc, HoldFirst]
RemoveFromAssoc[assoc_, keys__] := (assoc = Delete[assoc, {Key[#]}&/@{keys}])


(* ::Section::Closed:: *)
(*Asymptotics*)


LeadingPower[expr_List, x_, x0_] := LeadingPower[#, x, x0]& /@ expr
LeadingPower[expr_, x_, x0_] := With[{ser = Series[expr, x -> x0]},
	Switch[ser, _SeriesData, ser[[-3]], _, 0]
]


LeadingOrderTerm[expr_List, x_, x0_] := LeadingOrderTerm[#, x, x0]& /@ expr
LeadingOrderTerm[expr_, x_, x0_] := With[{ser = Series[expr, x -> x0]},
	Switch[ser, _SeriesData, Normal[ser], _, ser]
]


ResumLog::usage = "ResumLog[expand, {\!\(\*SubscriptBox[\(f\), \(1\)]\), \!\(\*SubscriptBox[\(f\), \(2\)]\),...}, x, {\[Epsilon], order0, order}] matches the expansion \"expand\" \
with the expression
\!\(\*UnderscriptBox[\(\[Sum]\), \(i\)]\) \!\(\*SubscriptBox[\(f\), \(i\)]\)(x, \[Epsilon]) (\[ScriptCapitalC][i,order0]\!\(\*SuperscriptBox[\(\[Epsilon]\), \(order0\)]\) + \[Ellipsis] + \[ScriptCapitalC][i,j]\!\(\*SuperscriptBox[\(\[Epsilon]\), \(j\)]\) + \[Ellipsis] )
up to \!\(\*SuperscriptBox[\(\[Epsilon]\), \(order\)]\) in the whole expression. "
\[ScriptCapitalC]::usage = "The indeterminate constant returned by ResumLog[]. "

ResumLog::mismatch = "The given functional form cannot match the expression. "

ResumLog[expand_, form_List, x_, {eps_, order0_, order_}] := Enclose[Module[{
		expr, CList,
		xOrder0, epsOrder0,
		eqs, eqsCoef
	},
	expr = Table[
		form[[i]]Sum[\[ScriptCapitalC][i, j] eps^j, {j, order0, order - LeadingPower[form[[i]], eps, 0]}],
		{i, Length[form]}
	];
	CList = DeleteDuplicates@Cases[expr, _\[ScriptCapitalC], {0, \[Infinity]}];
	eqs = Normal@Series[Total[expr]-expand, {eps, 0, order}];
	xOrder0 = LeadingPower[eqs, x, 0];
	epsOrder0 = LeadingPower[eqs, eps, 0];
	eqsCoef = CoefficientList[x^-xOrder0 eps^-epsOrder0 eqs, {x, Log[x], eps}];
	expr /. First[ConfirmBy[
		Solve[eqsCoef == 0, CList],
		# =!= {}&, Message[ResumLog::mismatch]
	]]
], $Failed&]


ClearAll[LeadingAsymptotic0Internal]

LeadingAsymptotic0Internal::indef = "Indefinite orders in ``"
LeadingAsymptotic0Internal::unsupp = "Unsupported functional form ``"

LeadingAsymptotic0Internal[HoldPattern@Plus[a__], varOrder__List] := Module[{
		mono = LeadingAsymptotic0Internal[#, varOrder]& /@ {a},
		lo, vars
	},
	vars = Variables[mono[[;;, 1]]];
	lo = Simplify[Min@@mono[[;;, 1]], AllTrue[vars, #\[Element]Reals&]];
	If[Not@FreeQ[lo, _Min], 
		Message[LeadingAsymptotic0Internal::indef, Plus[a]]; Abort[]
	];
	{lo, Total@Cases[mono, {lo2_/;Expand[lo2 == lo], ex_} :> ex]}
]
LeadingAsymptotic0Internal[HoldPattern@Times[a__], varOrder__List] := Module[{
		mono = LeadingAsymptotic0Internal[#, varOrder]& /@ {a}
	},
	{Total[mono[[;;, 1]]], Times@@(mono[[;;, 2]])}
]
LeadingAsymptotic0Internal[a_^p_, varOrder__List] /; FreeQ[p, Alternatives@@({varOrder}[[;;, 1]])] := Module[{
		mono = LeadingAsymptotic0Internal[a, varOrder]
	},
	{mono[[1]] p, mono[[2]]^p}
]
LeadingAsymptotic0Internal[(h:UnitStep|HeavisideTheta)[a__], varOrder__List] := Module[{
		mono = LeadingAsymptotic0Internal[#, varOrder]& /@ {a}
	},
	{0, h@@(mono[[;;, 2]])}
]
LeadingAsymptotic0Internal[DiracDelta[a_], varOrder__List] :=
	{-#1, DiracDelta[#2]}& @@ LeadingAsymptotic0Internal[a, varOrder]
LeadingAsymptotic0Internal[x_, varOrder__List] := FirstCase[{varOrder}, 
	{x, ord_} :> {ord, x}, 
	If[FreeQ[x, Alternatives@@({varOrder}[[;;, 1]])], 
		{0, x},
		Message[LeadingAsymptotic0Internal::unsupp, x]; Abort[]
	]
]

LeadingAsymptotic0[a_, varOrder__List]:=LeadingAsymptotic0Internal[a, varOrder][[2]]


(* ::Section::Closed:: *)
(*I/O*)


MapAllStruct[f_, list_List] := f[MapAllStruct[f, #]& /@ list]
MapAllStruct[f_, ass_Association] := f@KeyValueMap[f[MapAllStruct[f, #1], MapAllStruct[f, #2]]&, ass]
MapAllStruct[f_, expr_] := f[expr]


MapAtValues[f_, struct:(_List|_Association)] := MapAtValues[f, #]& /@ struct
MapAtValues[f_, expr_] := f[expr]


DepthIter[list_List] := Max[list] + 1
DepthIter[key_, value_] := Max[key, value]
DepthIter[expr_] := 1

DepthStruct[expr_] := MapAllStruct[DepthIter, expr]


ScalarIter[list_List] := Total[list]
ScalarIter[key_, value_] := key + value
ScalarIter[expr_] := 1

ScalarCount[expr_] := MapAllStruct[ScalarIter, expr]


Options[EncodeIntoYAML] = {
	"Type" -> Automatic(*"Block" | "Inline"*)
};

EncodeIntoYAML[expr_, op:OptionsPattern[]] := EncodeIntoYAML[expr, 0, op]
EncodeIntoYAML[expr_, indent_, OptionsPattern[]] := 
	First@EncodeIntoYAMLInternal[expr, indent, OptionValue["Type"]]

ClearAll[AutoInlineQ]
AutoInlineQ[expr_] := (DepthStruct[expr] <= 2 || ScalarCount[expr] <= 6)

ClearAll[EncodeIntoYAMLInternal]

EncodeIntoYAMLInternal[list_List, indent_:0, type_] := 
	Switch[If[type === Automatic && AutoInlineQ[list], "Inline", type],
		"Inline", {StringRiffle[First@EncodeIntoYAMLInternal[#, "Inline"]& /@ list, {"[", ", ", "]"}], "Inline"},
		_, {StringRiffle[
			First@EncodeIntoYAMLInternal[#, indent+2, Automatic]& /@ list,
			{"- ", "\n"<>StringRepeat[" ", indent]<>"- ", ""}
		], "Block"}
	]

EncodeIntoYAMLInternal[ass_Association, indent_:0, type_] := 
	Switch[If[type === Automatic && AutoInlineQ[ass], "Inline", type],
		"Inline", {StringRiffle[
			KeyValueMap[
				StringTemplate["``: ``"][
					First@EncodeIntoYAMLInternal[#1, "Inline"],
					First@EncodeIntoYAMLInternal[#2, "Inline"]
				]&,
				ass
			],
			{"{", ", ", "}"}
		], "Inline"},
		_, {StringRiffle[
			KeyValueMap[
				Module[{
					key = EncodeIntoYAMLInternal[#1, indent+2, Automatic],
					value = EncodeIntoYAMLInternal[#2, indent+2, Automatic]
				}, 
					Switch[Last[key],
						"Inline", StringTemplate["``: ``"][
							First[key], 
							Switch[Last[value], 
								"Inline", "", 
								"Block", "\n"<>StringRepeat[" ", indent+2]
							] <> First[value]
						],
						"Block", "? " <> First[key] <> "\n" <> StringRepeat[" ", indent]<>": " <> First[value]
					]
				]&,
				ass
			],
			{"", "\n"<>StringPadLeft["", indent], ""}
		], "Block"}
	]

EncodeIntoYAMLInternal[str_String, indent_:0, type_] := {str, "Inline"}

EncodeIntoYAMLInternal[expr_, indent_:0, type_] := {ToString[expr, InputForm], "Inline"}


ToStr::usage =
"ToStr[data] is used for encoding data into a file name. "

ToStr[s_String] := s
ToStr[i_Integer] := TextString[i]
ToStr[r_Rational] := ToStr[Numerator[r]] <> "db" <> ToStr[Denominator[r]]


DeletePath[path_String] :=
	Switch[FileType[path],
		Directory, DeleteDirectory[path, DeleteContents -> True],
		File, DeleteFile[path],
		None, Null
	]


(* ::Section:: *)
(*End*)


End[]
