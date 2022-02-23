(* ::Package:: *)

ClearAll[EnumSP]
ClearAll[MomentumQ]
ClearAll[\[CapitalOmega]]
ClearAll[Idx]
j;(* Register j to the context *)
ClearAll[Idx2j, j2Idx]
ClearAll[NSeries0]


Begin["`Private`"]


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


\[CapitalOmega]::usage =
"\[CapitalOmega][d] is the surface area of a d-dimensional unit sphere. ";
\[CapitalOmega][d_] := (2 \[Pi]^(d/2))/Gamma[d/2]


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


NSeries0::usage = 
"NSeries0[expr, eps, order] is a wrapper for Normal@Series[expr, {eps, 0, order}]. "
NSeries0[expr_, eps_, order_] := Normal@Series[expr, {eps, 0, order}]
NSeries0[expr_, eps_, order_, assum_] := Normal@Series[expr, {eps, 0, order}, Assumptions -> assum]


End[]
