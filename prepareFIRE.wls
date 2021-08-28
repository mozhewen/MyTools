#!/usr/bin/env wolframscript
(* ::Package:: *)

Get@FileNameJoin[{$ScriptCommandLine[[2]], "FIRE6.m"}];


{Internal, External, Propagators, Replacements} = Import[StringTemplate["``.wl"][$ScriptCommandLine[[3]]]];

PrepareIBP[];
Prepare[AutoDetectRestrictions->True, LI->True];

SaveStart[$ScriptCommandLine[[3]]];
