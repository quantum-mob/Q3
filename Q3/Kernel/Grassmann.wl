(* -*- mode: math; -*- *)
(* Some features in this file were adopted from a package by M. Headrick (April 2003). *)
BeginPackage["QuantumMob`Q3`", {"System`"}]

{ Grassmann, GrassmannQ, AnyGrassmannQ };
{ GrassmannD, GrassmannIntegrate };
{ GrassmannGrade }


Begin["`Private`"]

$symbs = Unprotect[Power]


(**** <Grassmann> ****)

Grassmann::usage = "Grassmann represents a set of generators of a Grassmann algebra."

Grassmann /:
Let[Grassmann, {ls__Symbol}] := (
  Let[NonCommutative, {ls}];
  Scan[setGrassmann, {ls}];
)

setGrassmann[x_Symbol] := (
  MultiplyKind[x] ^= Grassmann;
  MultiplyKind[x[___]] ^= Grassmann;
  
  GrassmannQ[x] ^= True;
  GrassmannQ[x[___]] ^= True;
  
  GrassmannGrade[x] ^= 1;
  GrassmannGrade[x[___]] ^= 1;
)

(**** </Grassmann> ****)


(**** <GrassmannQ> ****)

GrassmannQ::usage = "GrassmannQ[z] returns True if z is a *generator* (but not a generic element) of the Grassmann algebra over complex numbers."

GrassmannQ[_] = False


AnyGrassmannQ::usage = "AnyGrassmannQ[z] returns true z itself a Grassmann generator or a conjugate z = Conjugate[x] of another Grassmann generator x."

AnyGrassmannQ[ _?GrassmannQ ] = True

AnyGrassmannQ[ Conjugate[_?GrassmannQ] ] = True

AnyGrassmannQ[_] = False

(**** </GrassmannQ> ****)


Power[a_?GrassmannQ, n_Integer?NonNegative] := MultiplyPower[a, n]

Dagger[ z_?AnyGrassmannQ ] := Conjugate[z]

Tee[ z_?GrassmannQ ] := z

Multiply /:
HoldPattern @ Conjugate[ Multiply[ops__?AnyGrassmannQ] ] :=
  Multiply @@ Reverse[Conjugate @ {ops}]


(**** <Multiply> ****)

HoldPattern @ Multiply[___, op_?AnyGrassmannQ, op_?AnyGrassmannQ, ___] = 0

HoldPattern @ 
Multiply[pre___, a_?GrassmannQ, b:Conjugate[_?GrassmannQ], post___] :=
  -Multiply[pre, b, a, post]

HoldPattern @ Multiply[pre___, ops__?GrassmannQ, post___] :=
  Multiply[pre, Sequence @@ ReverseSort @ {ops}, post] * Signature[Reverse @ {ops}] /;
    Not @ OrderedQ @ Reverse @ {ops}

HoldPattern @ Multiply[pre___, ops:Conjugate[_?GrassmannQ].., post___] :=
  Multiply[pre, Sequence @@ Sort @ {ops}, post] * Signature[{ops}] /;
    Not @ OrderedQ @ {ops}


HoldPattern @ 
  Multiply[pre___, op_?AnyGrassmannQ, v_Ket, post___] :=
    ParityValue[v, Fermions @ v] * Multiply[pre, v, op, post]

HoldPattern @ 
  Multiply[pre___, v_Bra, op_?AnyGrassmannQ, post___] :=
    ParityValue[v, Fermions @ v] * Multiply[pre, op, v, post]

(**** </Multiply> ****)


(**** <GrassmannD> ****)

GrassmannD::usage = "GrassmannD[expr, g] returns the Grassmann derivative of expr with respect to the Grassmann generator g.\nGrassmannD[expr, {g1, g2, \[Ellipsis]}] returns the derivative with respect to multiple Grassmann generators g1, g2, \[Ellipsis].\nGrassmannD[g] or GrassmannD[{g1, g2, \[Ellipsis]}] represents the operator form of GrassmannD acting on an expression."

GrassmannD[gg_][expr_] := GrassmannD[expr, gg]

GrassmannD[expr_, g_?AnyGrassmannQ] := GrassmannD[expr, {g}]

GrassmannD[z_?CommutativeQ * expr_, gg_] := z * GrassmannD[expr, gg]

GrassmannD[expr_Plus, gg_] := Map[GrassmannD[gg], expr]


grsFreeQ[expr_, gg:{__?AnyGrassmannQ}] := Module[
  { gnr, new },
  gnr = Cases[gg, _Conjugate];
  If[AnyTrue[gnr, FreeQ[expr, #, Heads -> False]&], Return @ True];
  gnr = DeleteCases[gg, _Conjugate];
  new = DeleteCases[{expr}, Alternatives @@ Conjugate @ gnr, Infinity];
  AnyTrue[gnr, FreeQ[new, #, Heads -> False]&]
]

GrassmannD[expr_, gg:{__?AnyGrassmannQ}] := 0 /; 
  grsFreeQ[expr, gg]


GrassmannD[g_?AnyGrassmannQ, {g_?AnyGrassmannQ}] = 1


GrassmannD[CoherentState[aa_Association], gg:{__?AnyGrassmannQ}] :=
  Module[
    { bb = Select[aa, Not @ FreeQ[#, Alternatives @@ gg]&] },
    ReplaceAll[GrassmannD[FockCat[CoherentState @ bb], gg], Ket[Vacuum] -> 1] **
      CoherentState[KeyDrop[aa, Keys @ bb]]
  ]

HoldPattern @
  GrassmannD[Multiply[ff__?AnyGrassmannQ], gg:{__?AnyGrassmannQ}] := 
    With[
      { ss = Supplement[{ff}, gg] },
      SignatureTo[{ff}, Join[Reverse @ gg, ss]] * Apply[Multiply, ss]
    ]


HoldPattern @
  GrassmannD[Multiply[op:Longest[ff__?AnyGrassmannQ], post__], gg:{__?AnyGrassmannQ}] := 
    GrassmannD[Multiply[op], gg] ** Multiply[post] + 
        IntegerParity[Length[{ff}] * Length[gg]] * op ** GrassmannD[Multiply[post], gg]

HoldPattern @
  GrassmannD[Multiply[v_CoherentState, post___], gg:{__?AnyGrassmannQ}] :=
    GrassmannD[v, gg] ** Multiply[post] + v ** GrassmannD[Multiply[post], gg]

HoldPattern @
  GrassmannD[Multiply[v_Ket, post___], gg:{__?AnyGrassmannQ}] :=
    Power[ParityValue[v, Fermions @ v], Length @ gg] * 
      Multiply[v, GrassmannD[Multiply[post], gg]]

HoldPattern @
  GrassmannD[Multiply[ff__?AnyFermionQ, post___], gg:{__?AnyGrassmannQ}] :=
    IntegerParity[Length[{ff}] * Length[gg]] * Multiply[ff, GrassmannD[Multiply[post], gg]]

(**** </GrassmannD> ****)


(**** <GrassmannIntegrate> ****)

GrassmannIntegrate::usage = "GrassmannIntegrate[expr, g] returns the Grassmann integration of expr with respect to the Grassmann generator g.\nGrassmannIntegrate[expr, {g1, g2, \[Ellipsis]}] returns the integration with respect to multiple Grassmann generators g1, g2, \[Ellipsis].\nGrassmannIntegrate[g] or GrassmannIntegrate[{g1, g2, \[Ellipsis]}] represents the operator form of GrassmannIntegrate acting on an expression."

GrassmannIntegrate = GrassmannD

(**** </GrassmannIntegrate> ****)


(**** <GrassmannGrade> ****)

GrassmannGrade::usage = "GrassmannGrade[expr] returns a non-negative integer: 0, if expr is a pure boson, which can be multiplied using Times; positive and odd, if expr has fermionic statistics; or positive and even, if expr has bosonic statistics but involves Grassmann generators. Any generator whose grading is not explicitly declared is assumed to be purely bosonic."

GrassmannGrade[_?AnyGrassmannQ] = 1

GrassmannGrade[expr_Times] :=
  GrassmannGrade[DeleteCases[expr, _?CommutativeQ]]

GrassmannGrade[expr_Plus] := 
  Max @ Map[GrassmannGrade, List @@ expr]

GrassmannGrade[HoldPattern @ Multiply[ops__]] := 
  Total @ Map[GrassmannGrade, {ops}]

GrassmannGrade[GrassmannD[a_, _]] := GrassmannGrade[a] + 1

GrassmannGrade[_] = 0

(**** </GrassmannGrade> ****)


Protect[ Evaluate @ $symbs ]

End[]

EndPackage[]
