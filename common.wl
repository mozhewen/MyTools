(* ::Package:: *)

(* ::Text:: *)
(*Author: Zhewen Mo (mozhewen@outlook.com, mozw@ihep.ac.cn)*)
(**)
(*Mathematica version: 13.1*)
(**)
(*Last update: 2022.10.28*)


ClearAll[EnumSP]
ClearAll[MomentumQ]
ClearAll[ToSqForm]
ClearAll[\[CapitalOmega]]

j;
ClearAll[Idx]
ClearAll[Idx2j, j2Idx]

ClearAll[NSeries0]
ClearAll[DDCasesAll]
ClearAll[AddToAssoc, RemoveFromAssoc]

ClearAll[MapAllStruct]
ClearAll[MapAtValues]
ClearAll[DepthStruct]
ClearAll[ScalarCount]

ClearAll[EncodeIntoYAML]
ClearAll[ToStr]
ClearAll[DeletePath]


Begin["`Private`"]


(* ::Section:: *)
(*Kinematics*)


EnumSP::usage =
"EnumSP[kList, sp] gives all scalar products of momenta in kList. The function used to represent scalar \
products are defined by sp. ";
EnumSP[kList_List, sp_:Times] := sp@@@DeleteDuplicates[Tuples[kList, 2], ContainsExactly]


MomentumQ::usage = 
"MomentumQ[expr_, kList] checks whether expr is a plain linear (return True) or quadratic (return False) \
form of the momenta in kList. It fails when expr is invalid. "
MomentumQ::invalid = "Invalid expression `1`. ";
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
		]
		,(*Else*)False
	], $Failed &]
MomentumQ[sym_, kList_List] := MatchQ[sym, Alternatives@@kList]


ToSqForm::usage = 
"ToSqForm[quad, l, SPrules:{}] constructs the standard form of quadratic form quad with respect to variable l. \
SPrules is used to simplify scalar products of the constant term. 
ToSqForm[quad, {\!\(\*SubscriptBox[\(l\), \(1\)]\), \!\(\*SubscriptBox[\(l\), \(2\)]\), ...}, SPrules:{}] uses \
the first \!\(\*SubscriptBox[\(l\), \(i\)]\) that appears in quad as the variable. ";
ToSqForm[quadList_List, l_, SPrules_:{}] := ToSqForm[#, l, SPrules]& /@ quadList
ToSqForm[quad_, lList_List, SPrules_:{}] := ToSqForm[quad, FirstCase[lList, _?(MemberQ[Variables[quad],#]&)], SPrules]
ToSqForm[quad_, l_, SPrules_:{}] := 
	Module[{a = Coefficient[quad, l, 2], b = Coefficient[quad, l, 1], c = Coefficient[quad, l, 0]},
		If[a =!= 0,
			a (Expand[l + b/(2a)])^2- Together[Expand[(b^2 - 4 a c)/(4a)]//.SPrules]
		,(*Else*)
			quad
		]
	]


\[CapitalOmega]::usage =
"\[CapitalOmega][d] is the surface area of a d-dimensional unit sphere. ";
\[CapitalOmega][d_] := (2 \[Pi]^(d/2))/Gamma[d/2]


(* ::Section:: *)
(*Scalar integral representations*)


Idx::usage = "Idx[a1, a2, ] represents the indices of propagators in a specific basis. ";


Idx2j::usage = "Idx2j[family][expr] converts Idx[idx..] in expr into j[family, idx..]. ";
Idx2j[family_][expr_] := expr /. Idx[idx__] :> j[family, idx]


j2Idx::usage = "j2Idx[expr] converts j[family, idx..] in expr into Idx[idx..]. ";
j2Idx::mulfam = "Multiple families `` of j can not be converted into Idx simultaneously. ";
j2Idx[expr_] := 
	Enclose[Module[{familyList = {}},
		expr /. j[family_, idx__] :> (
			familyList = Union[familyList, {family}]; 
			ConfirmAssert[Length[familyList] <= 1, Message[j2Idx::mulfam, familyList]]; 
			Idx[idx]
		)
	], $Failed &]


(* ::Section:: *)
(*Wrappers*)


NSeries0::usage = 
"NSeries0[expr, eps, order] is a wrapper for Normal@Series[expr, {eps, 0, order}]. "
NSeries0[expr_, eps_, order_] := Normal@Series[expr, {eps, 0, order}]
NSeries0[expr_, eps_, order_, assum_] := Normal@Series[expr, {eps, 0, order}, Assumptions -> assum]


DDCasesAll::usage =
"DDCasesAll[expr, pattern] is a wrapper for DeleteDuplicates@Cases[expr, pattern, {0, \[Infinity]}]"
DDCasesAll[expr_, pattern_] := DeleteDuplicates@Cases[expr, pattern, {0, \[Infinity]}]


SetAttributes[AddToAssoc, HoldFirst]
AddToAssoc::usage = 
"AddToAssoc[assoc, key -> value] adds a key-value pair to assoc. 
AddToAssoc[assoc, list] adds a list of key-value pairs. ";
AddToAssoc[assoc_, r_Rule] := AppendTo[assoc, r]
AddToAssoc[assoc_, rules_List] := (assoc = Join[assoc, Association[rules]])

SetAttributes[RemoveFromAssoc, HoldFirst]
RemoveFromAssoc::usage =
"RemoveFromAssoc[assoc, key] removes key from assoc. 
RemoveFromAssoc[assoc, key1, key2, ...] removes a sequence of keys from assoc. ";
RemoveFromAssoc[assoc_, keys__] := (assoc = Delete[assoc, {Key[#]}&/@{keys}])


(* ::Section:: *)
(*For I/O*)


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
"ToStr[data] is used for encoding data into a file name. ";
ToStr[s_String] := s
ToStr[i_Integer] := TextString[i]
ToStr[r_Rational] := ToStr[Numerator[r]] <> "db" <> ToStr[Denominator[r]]


DeletePath[path_String] := 
	Switch[FileType[path],
		Directory, DeleteDirectory[path, DeleteContents -> True],
		File, DeleteFile[path],
		None, Null
	]


End[]
