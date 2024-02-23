(* -*- mode: math; -*- *)
(* Many features in this file were adopted from a package by M. Headrick (April 2003). *)
BeginPackage["Q3`"]

{ Grassmann, GrassmannQ, AnyGrassmannQ };
{ GD, GIntegrate };
{ GrassmannGrade }


Begin["`Private`"]

$symbs = Unprotect[Power]


(**** <Grassmann> ****)

Grassmann::usage = "Grassmann refers to the generators of a Grassmann algebra."

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


(**** <Conjugate> ****)

Multiply /:
HoldPattern @ Conjugate[ Multiply[ops__?AnyGrassmannQ] ] :=
  Multiply @@ Reverse[Conjugate @ {ops}]

Dagger[ z_?AnyGrassmannQ ] := Conjugate[z]

Tee[ z_?GrassmannQ ] := z

(**** </Conjugate> ****)


Power[a_?GrassmannQ, n_Integer?NonNegative] := MultiplyPower[a, n]


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


(**** <GD> ****)

GD::usage="GD[expr, g] returns the Grassmann derivative of expr with respect to the Grassmann variable g.\nGD[expr, {g1, g2, \[Ellipsis]}] returns the derivative with respect to multiple Grassmann variables g1, g2, \[Ellipsis].\nGD[g] or GD[{g1, g2, \[Ellipsis]}] represents the operator form of GD acting on an expression."

GD[gg_][expr_] := GD[expr, gg]


GD[z_?CommutativeQ * expr_, gg_] := z * GD[expr, gg]

GD[expr_Plus, gg_] := Map[GD[gg], expr]


GD[expr_, gg:{__?AnyGrassmannQ}] /; 
  AnyTrue[gg, FreeQ[expr, #, Heads -> False]&] = 0


HoldPattern @ 
GD[Multiply[ff__?AnyGrassmannQ], gg:{__?AnyGrassmannQ}] := With[
  { ss = Supplement[{ff}, gg] },
  SignatureTo[{ff}, Join[Reverse @ gg, ss]] * Apply[Multiply, ss]
]

GD[expr_, gg:{__?AnyGrassmannQ}] := Fold[GD, expr, Reverse @ gg]


(* NOTE:  In general, GD[..., g] != GD[..., {g}]. *)
HoldPattern @ 
GD[op:Multiply[__?AnyGrassmannQ], g_?AnyGrassmannQ] := GD[op, {g}]

GD[g_?AnyGrassmannQ, g_?AnyGrassmannQ] = 1

GD[expr_, g_?AnyGrassmannQ] /; FreeQ[expr, g] = 0

GD[a_?AnyGrassmannQ ** expr_, g_?AnyGrassmannQ] :=
  GD[a, g] ** expr - a ** GD[expr, g]

(**** </GD> ****)


(**** <GIntegrate> ****)

GIntegrate::usage="GIntegrate[expr, g] returns the Grassmann integration of expr with respect to the Grassmann variable g.\nGIntegrate[expr, {g1, g2, \[Ellipsis]}] returns the integration with respect to multiple Grassmann variables g1, g2, \[Ellipsis].\nGIntegrate[g] or GIntegrate[{g1, g2, \[Ellipsis]}] represents the operator form of GIntegrate acting on an expression."

GIntegrate = GD

(**** </GIntegrate> ****)


(**** <GrassmannGrade> ****)

GrassmannGrade::usage="GrassmannGrade[expr] returns a non-negative integer: 0, if expr is a pure boson, which can be multiplied using Times; positive and odd, if expr has fermionic statistics; or positive and even, if expr has bosonic statistics but involves Grassmann variables. Values of the function GrassmannGrade may also be defined explicitly; for example,

  GrassmannGrade[ f[x_] ] := GrassmannGrade[ x ] 

defines the function f to have the same grading as its argument. Any variable whose grading is not explicitly declared is assumed to be purely bosonic."

GrassmannGrade[_?AnyGrassmannQ] = 1

GrassmannGrade[expr_Times] :=
  GrassmannGrade[DeleteCases[expr, _?CommutativeQ]]

GrassmannGrade[expr_Plus] := 
  Max @ Map[GrassmannGrade, List @@ expr]

HoldPattern @ GrassmannGrade[Multiply[ops__]] := 
  Total @ Map[GrassmannGrade, {ops}]

GrassmannGrade[GD[a_, _]] := GrassmannGrade[a] + 1

GrassmannGrade[_] = 0

(**** </GrassmannGrade> ****)


Protect[ Evaluate @ $symbs ]

End[]

EndPackage[]
