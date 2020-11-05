(* -*- mode: math; -*- *)

(* Adopted from a package by M. Headrick (April 2003) *)
(* Mahn-Soo Choi *)
(* $Date: 2020-11-05 19:48:14+09 $ *)
(* $Revision: 1.4 $ *)

BeginPackage[ "Q3`Grassmann`", { "Q3`Cauchy`" } ]

Unprotect[Evaluate[$Context<>"*"]]

Print @ StringJoin[
  $Input, " v",
  StringSplit["$Revision: 1.4 $"][[2]], " (",
  StringSplit["$Date: 2020-11-05 19:48:14+09 $"][[2]], ") ",
  "Mahn-Soo Choi"
 ]

{ Let, Grassmann, GrassmannQ, AnyGrassmanQ };
{ GD, GIntegrate };
{ GrassmannExpand, GrassmannCollect };
{ GrassmannGrade }


Begin["`Private`"]

$symbs = Unprotect[
  Power, Multiply, Dagger, Tee
 ]

Grassmann /:
Let[Grassmann, {ls__Symbol}] := (
  Let[NonCommutative, {ls}];
  Scan[setGrassmann, {ls}];
 )

setGrassmann[x_Symbol] := (
  Kind[x] ^= Grassmann;
  Kind[x[___]] ^= Grassmann;
  
  GrassmannQ[x] ^= True;
  GrassmannQ[x[___]] ^= True;
  
  GrassmannGrade[x] ^= 1;
  GrassmannGrade[x[___]] ^= 1;
 )


GrassmannQ::usage = "GrassmannQ[z] returns True if z is a *generator* (but not a generic element) of the Grassmann algebra over complex numbers."

GrassmannQ[_] = False


AnyGrassmannQ::usage = "AnyGrassmannQ[z] returns true z itself a Grassmann generator or a conjugate z = Conjugate[x] of another Grassmann generator x."

AnyGrassmannQ[ _?GrassmannQ ] = True

AnyGrassmannQ[ Conjugate[_?GrassmannQ] ] = True

AnyGrassmannQ[_] = False


HoldPattern @ Multiply[___, op_, op_, ___] := 0 /; GrassmannQ[op]

HoldPattern @ Multiply[pre___, op___?GrassmannQ, post___] :=
  Multiply[pre, Sequence @@ Sort @ {op}, post] Signature @ {op} /;
  Not @ OrderedQ @ {op}


fieldQ::usage = "Grassmann`Private`fieldQ[z] returns True if z is a complex field over which the Grassmann algebra is defined."

fieldQ[_?NumberQ] = True

fieldQ[_?NumericQ] = True

fieldQ[_?ComplexQ] = True


Power[a_?GrassmannQ, n_Integer?NonNegative] := MultiplyPower[a, n]


(*** Conjugate ***)

(* By default, if z is a Grassmann generator, so is Conjugate[z]. *)
GrassmannQ[ Conjugate[_?GrassmannQ] ] = True

Multiply /:
HoldPattern @ Conjugate[ Multiply[a_?GrassmannQ, b__?GrassmannQ] ] :=
  Multiply[ Conjugate[Multiply[b]], Conjugate[a] ]
(* NOTE: Do not generalize it too much. For example, <a|op|b> is a complex
   number and under Dagger switches to complex conjugation. If the above is
   generalized too much, then it may results in, i.e., Conjugate[Ket[]]
   instead of <b|Dagger[op]|a>. *)

Dagger[ z_?GrassmannQ ] := Conjugate[z]

Tee[ z_?GrassmannQ ] := z


(*** Differentiation and Integration ***)

GD::usage="GD[z1, z2, ..., expr] for Grassmann variables z1, z2, ... is like D[expr, z1, z2, ...] for real variables z1, z2, .... Notice that the variable list comes before the integrand expression."

SetAttributes[GD, Listable]

GD[a__?GrassmannQ, b_?GrassmannQ, expr_] := GD[a, GD[b,expr]]

GD[a_, a_] /; GrassmannQ[a] = 1

GD[a_?GrassmannQ, expr_] /; FreeQ[expr,a] = 0

GD[a_?GrassmannQ, expr_] /; GrassmannGrade[expr]==0  = 0

GD[a_?GrassmannQ, b_+c_] := GD[a,b] + GD[a,c]

GD[a_?GrassmannQ, b_?fieldQ c_] := b GD[a,c]

GD[a_?GrassmannQ, b_?GrassmannQ**c_?GrassmannQ] := GD[a,b]**c - b**GD[a,c]

GD[a_?GrassmannQ, b_?GrassmannQ**c_?GrassmannQ**expr__] :=
  GD[a,b]**c**expr - b**GD[a,c**expr]
(* Note that the above two CANNOT be combined by GD[a_,b_**c_**expr___] *)

(* GIntegrate -- the Grassmann integration *)

GIntegrate::usage="GIntegrate[z1, z2, ..., expr] for Grassmann variables z1, z2, ... is like Integrate[expr, z1, z2, ...] for real variables z1, z2, .... Notice that the variable list comes before the integrand expression."

GIntegrate[a_,b__] = GD[a,b]

(*** GrassmannGrade ***)

GrassmannGrade::usage="GrassmannGrade[expr] returns a non-negative integer: 0, if expr is a pure boson, which can be multiplied using Times; positive and odd, if expr has fermionic statistics; or positive and even, if expr has bosonic statistics but involves Grassmann variables. Values of the function GrassmannGrade may also be defined explicitly; for example,

  GrassmannGrade[ f[x_] ] := GrassmannGrade[ x ] 

defines the function f to have the same grading as its argument. Any variable whose grading is not explicitly declared is assumed to be purely bosonic."

GrassmannGrade[a_+b_] := Max[GrassmannGrade[a],GrassmannGrade[b]]

GrassmannGrade[a_ b_] := GrassmannGrade[a]+GrassmannGrade[b]

GrassmannGrade[a_**b_] := GrassmannGrade[a]+GrassmannGrade[b]

GrassmannGrade[Derivative[__][f_][x__]] := GrassmannGrade[f[x]]

GrassmannGrade[GD[a_,_]] := GrassmannGrade[a]+1

GrassmannGrade[_] = 0


Protect[ Evaluate @ $symbs ]

End[]


Q3`Grassmann`Private`symbs = Protect[Evaluate[$Context<>"*"]]

SetAttributes[Evaluate[Q3`Grassmann`Private`symbs], ReadProtected]

EndPackage[]
