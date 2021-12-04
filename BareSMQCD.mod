(* Patched for use with FeynCalc *)
(*
	(SM|THDM)QCD.mod
		Addendum classes model file for SM.mod
		to include the strong interactions
		by Christian Schappacher
		last modified 06 Feb 17 by cs
		
		Modified by Zhewen Mo (29 Aug 2021)

This file introduces the following symbols in addition to the ones in
SM.mod:

	FAGS: the strong coupling constant

	FASUNT[a, i, j]: the generators of SU(N)
		(half the Gell-Mann matrices)

	FASUNF[a, b, c]: the structure constants of SU(N)

	FASUNF[a, b, c, d]: a short-hand for the sum
		\sum_i FASUNF[a, b, i] FASUNF[i, c, d]

	FAGaugeXi[g]: gluon gauge parameter

	dZGG1: gluon field RC
        dZgs1: strong coupling-constant RC
*)


LoadModel[ StringReplace[$Input, {"Bare" -> "", "QCD" -> ""}], "" ]

If[ $NoElectroweak === True, M$CouplingMatrices = {} ]


IndexRange[ Index[Gluon] ] = NoUnfold[Range[8]]

M$ClassesDescription = Join[ M$ClassesDescription, {

  V[5] == {
	SelfConjugate -> True,
	Indices -> {Index[Gluon]},
	Mass -> 0,
	QuantumNumbers -> {Sqrt[3] ColorCharge},
	PropagatorLabel -> "g",
	PropagatorType -> Cycles,
	PropagatorArrow -> None },

  U[5] == {
	SelfConjugate -> False,
	Indices -> {Index[Gluon]},
	Mass -> 0,
	QuantumNumbers -> {Sqrt[3] ColorCharge, GhostNumber},
	PropagatorLabel -> ComposedChar["u", "g"],
	PropagatorType -> GhostDash,
	PropagatorArrow -> Forward }
} ]


FAGaugeXi[ V[5, ___] ] = FAGaugeXi[g];
FAGaugeXi[ U[5, ___] ] = FAGaugeXi[g]


M$CouplingMatrices = Join[

  (* Modified existing rules *)
  M$CouplingMatrices/.{
    (*--- quark-quark -----------------------------------------------------*)
    ((c:C[ -F[gen: 3|4, {j1, o1}], F[gen_, {j2, o2}] ]) == rhs_) :> (
      c == I IndexDelta[o1, o2] *
        { {0, 0, 0},
          {0, 0, 0},
          {0, - IndexDelta[j1, j2] dMf1[gen, j1], - IndexDelta[j1, j2] dMf2[gen, j1]},
          {0, - IndexDelta[j1, j2] dMf1[gen, j1], - IndexDelta[j1, j2] dMf2[gen, j1]} }
    ),

    (*--- For external Higgs vertex ---------------------------------------*)
    ((c:C[ -F[gen: 3|4, {j1, o1}], F[gen_, {j2, o2}], S[1] ]) == rhs_) :> (
      c == -I FCGV["EL"]/(2 FCGV["SW"] FCGV["MW"]) IndexDelta[o1, o2] *
    	{ {Mass[F[gen, {j1}]] IndexDelta[j1, j2],
           dMf1[gen, j1] IndexDelta[j1, j2],
           dMf2[gen, j1] IndexDelta[j1, j2] },
          {Mass[F[gen, {j1}]] IndexDelta[j1, j2],
           dMf1[gen, j1] IndexDelta[j1, j2],
           dMf2[gen, j1] IndexDelta[j1, j2] } }
    )
  },

  {


  (*--- gluon-gluon counter term -----------------------------------------

    No such counter term: 

    C[ V[5, {g1}], V[5, {g2}] ] == I IndexDelta[g1, g2] *
      { {0, dZGG1},
        {0, 0},
        {0, -dZGG1} },
  *)


  (*--- gluon-gluon-gluon-gluon ------------------------------------------*)

    C[ V[5, {g1}], V[5, {g2}], V[5, {g3}], V[5, {g4}] ] == -I FAGS^2 *
      { ( FASUNF[g1, g3, g2, g4] - FASUNF[g1, g4, g3, g2] ) * 
        {1, 2 (dZgs1), dZgs1^2 + 2 dZgs2},
        ( FASUNF[g1, g2, g3, g4] + FASUNF[g1, g4, g3, g2] ) * 
        {1, 2 (dZgs1), dZgs1^2 + 2 dZgs2},
        (-FASUNF[g1, g2, g3, g4] - FASUNF[g1, g3, g2, g4] ) * 
        {1, 2 (dZgs1), dZgs1^2 + 2 dZgs2} },


  (*--- gluon-gluon-gluon ------------------------------------------------*)

    C[ V[5, {g1}], V[5, {g2}], V[5, {g3}] ] == FAGS FASUNF[g1, g2, g3] *
      { {1, dZgs1, dZgs2} },
 

  (*--- ghost-ghost-gluon ------------------------------------------------*)

    C[ -U[5, {g1}], U[5, {g2}], V[5, {g3}] ] == FAGS FASUNF[g1, g2, g3] *
      { {1, dZgs1, dZgs2}, {0, 0, 0} },


  (*--- quark-quark-gluon ------------------------------------------------*)

    C[ -F[3, {j1, o1}], F[3, {j2, o2}], V[5, {g1}] ] == -I FAGS *
      FASUNT[g1, o1, o2] * IndexDelta[j1, j2] *
      { {1, dZgs1, dZgs2}, 
        {1, dZgs1, dZgs2} },

    C[ -F[4, {j1, o1}], F[4, {j2, o2}], V[5, {g1}] ] == -I FAGS *
      FASUNT[g1, o1, o2] * IndexDelta[j1, j2] *
      { {1, dZgs1, dZgs2}, 
        {1, dZgs1, dZgs2} }

  }
]


(* dZGG1 = Alfas/(4 Pi) Divergence *)
RenConst[ dZGG1 ] := UVDivergentPart[FieldRC[V[5]]]

RenConst[ dZgs1 ] := -7/2 dZGG1
