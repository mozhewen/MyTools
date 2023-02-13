#!/usr/bin/env wolframscript
(* ::Package:: *)

$PolyLogPath = Directory[]

<< PolyLogTools`

link = LinkConnect[$ScriptCommandLine[[2]]]
Enclose@While[True,
	ConfirmQuiet[LinkWrite[link, 
		Enclose@ConfirmQuiet[ReleaseHold@LinkRead[link]]
	]]
]


(*ListMessages[sym_Symbol]:=Module[{},FileNameJoin[{System`Private`$MessagesDir,$Language,"Messages.m"}]//Get//Once;
Block[{MessageName},Grid[Messages[sym]/. RuleDelayed->List/. MessageName[a_,b_]:>(ToString[a]<>"::"<>ToString[b])/. HoldPattern->Identity,Alignment->{Left}]]]*)
