#!/usr/bin/env wolframscript
(* ::Package:: *)

$PolyLogPath = Directory[]

<< PolyLogTools`

link = LinkConnect[$ScriptCommandLine[[2]]]
Enclose@While[True,
	ConfirmQuiet@LinkWrite[link, ReleaseHold@LinkRead[link]]
]
