(* ::Package:: *)

ClearAll[UF];
Options[UF] := { Variables -> Table[x[i],{i,100}] };
UF[ks_,ds_,cs_,opt___Rule] :=
  Module[{degree,coeff,i,t2,t1,t0,zz,v},
(* 29.10.10: added by AP *)
  vs = Take[Variables /. {opt} /. Options[UF], Length[ds]];
  cz = Map[Rationalize[##,0]&, cs, {0,Infinity}];
  degree = - Sum[ds[[i]] * vs[[i]], {i,1,Length[ds]}];
  coeff = 1;
  For[i = 1, i <= Length[ks], i++,
    t2 = Coefficient[degree, ks[[i]], 2];
    t1 = Coefficient[degree, ks[[i]], 1];
    t0 = Coefficient[degree, ks[[i]], 0];
    coeff = coeff * t2;
(* 21.10.10: added by AP to avoid division by 0 *)
    If[t2 === 0, Return[{0,0,{}}]];
    degree = Together[t0 - ((t1^2)/(4*t2))]];
  degree = Together[- coeff * degree] //. cz;
  coeff = Together[coeff] //. cz;
  {coeff,Expand[degree],vs}]




(*******************************************************************************)
(* p: polynomial, return orderings of variables so that p is in canonical form *)

PolynomialOrderings[
  pn_, vs_List:{}, n_Integer:-1] :=
  Module[
    {vt, crs, gcd, cmx, cns, cas, cps, cvs, ord, max},
    (* check: variables *)
    vt = vs;
    If[vt === {}, vt = Variables[pn]];
    (* -- (1) -- *)
    (* polynomial -> coefficient rules *)
    crs = Echo@CoefficientRules[pn, vt];
    (* possible common factor *)
    gcd = PolynomialGCD @@ (Last /@ crs);
    (* rules -> matrix of exponents, coefficients *)
    cmx = Append[First[#], Simplify[Last[#]/gcd]] & /@ crs;
    (* operate on the transposed *)
    cmx = Echo[Transpose[(*Sort*)cmx], "cmx"];
    (* -- (2) -- *)
    (* initialize list of column numbers, permutations *)
    cns = Range[Length[vt]];
    cas = {{}};
    (* iterate until all variables ordered *)
    While[
      Length[First[cas]] < Length[vt],
      (* -- (3) -- *)
      (* extended permutations *)
      cps = Echo[Join @@
        (Function[ca, Append[ca, #] & /@ Complement[cns, ca]] /@ cas), "cps"];
      (* -- (4) -- *)
      (* candidate vectors *)
      cvs = Echo[(cmx[[Prepend[#, -1]]]  (* coefficients, swap rows *)
             // Transpose           (* -> columns *)
             // Sort                (* sort rows *)
             // Transpose           (* -> columns *)
             // Last) & /@ cps, "cvs"];     (* extract vector *)
      (* -- (5) -- *)
      (* lexicographical ordering *)
      ord = Ordering[cvs];
      (* maximum vector *)
      max = cvs[[Last[ord]]];
      (* -- (6) -- *)
      (* select (maximum number of) candidate permutations *)
      cas = Part[cps, Select[ord, cvs[[#]] === max & ]];
      cas = If[n >= 0 && n < Length[cas], Take[cas, n], cas]];
    (* -- (7) -- *)
    (* result: canonical orderings *)
    cas];

\[AliasDelimiter]


FindEquivalents[listt_] :=
 Module[{corners, functions, up, fp, vs, upc, fpc, op, H, temp, pn,vector,result,rep},
(*If[Head[Problems]===Symbol,
    If[Head[Propagators]===Symbol,Print["Please define propagators"];Return[{}]];
    If[Head[Replacements]===Symbol,Replacements={}]
  ,
    (
      If[Head[Propagators[##]]===Propagators,Print["Please define propagators ",##];Abort[]];
      If[Head[Replacements[##]]===Replacements,Replacements[##]={}];
    )&/@Problems
];*)
 (* If[listt === All,
   	corners = {Number2RealSector[##][[1]],
       SPoint[Number2RealSector[##][[2]]]} & /@ Range[RealSectors]
   , *)corners = listt(*];*)
  functions = Map[({(
       temp = ##;


     temp = {temp[[1]], If[## == 0, 0, 1] & /@ (temp[[2]])};
       pn = temp[[1]];
       vector=temp[[2]];
      (*If[Head[Problems]===Symbol,
	  {up, fp, vs} = UF[Internal, Propagators * vector, Replacements];
	,*)
	  {up, fp, vs} = UF[Internal[pn], Propagators[pn] * vector, Replacements[pn]];
      (*];*)

      vs=Array[x,Max@@(First/@vs)];
      rep=(x[ind_]:>If[##[[2]][[ind]]===1,x[ind],AAA[##[[2]][[ind]]]*x[ind]]);
      If[Or[vs==={},up*fp===0],Print["Zero integral: ",temp];H[0,0,0],
       op = PolynomialOrderings[Expand[(up*fp)/.rep], vs, 1];



{upc, fpc} = {up, fp} /.
         Table[vs[[op[[1, i]]]]->vs[[i]], {i, Length[vs]}];

         temp = op[[1]];
       (*MyInversePermutation[op[[1]]];*)


       H[Expand[upc],Expand[fpc],Table[##[[2]][[temp[[i]]]], {i, Length[vs]}]]

]
       ), ##})&,corners];
(*Print[functions];*)
result=  Reap[Sow[##[[2]], ##[[1]]] & /@ functions, _, If[({##}[[1]])===H[0,0,0],Append[({##}[[2]]),G[Infinity]],({##}[[2]])] &][[2]];
Print["Input: ",Length[listt],", output: ",Length[DeleteCases[result,{__,G[Infinity]}]]];
result
  ]


FindRules[listt_] := Module[{temp},
  temp = FindEquivalents[listt];
  temp = Select[temp, (Length[##] > 1) &];
  temp = Sort[##, HigherPair] & /@ temp;
  temp = {Drop[##, -1], Table[Last[##], {Length[##] - 1}]} & /@ temp;
  temp = Transpose /@ temp;
  temp = Flatten[temp, 1];
  temp = Apply[Rule, temp, {1}];
  temp = Apply[G, temp, {2}];
  Replace[temp,G[Infinity]->0,{2}]
]
