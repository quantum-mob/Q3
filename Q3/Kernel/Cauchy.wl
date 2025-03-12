(* ::Package:: *)

(* -*- mode:math -*- *)
BeginPackage["QuantumMob`Q3`", {"System`"}]

{ Complex, ComplexQ,
  Real, QuantumMob`Q3`RealQ,
  Integer, IntegerQ, HalfIntegerQ,
  Binary, BinaryQ, Binaries };

{ CauchySimplify, CauchyFullSimplify };

{ NGrad };


Begin["`Private`"]

$symb = Unprotect[Conjugate, Abs, Power, NonNegative]

(*** Conjugate[] and Power[] ***)

SetAttributes[{Conjugate, Power}, {ReadProtected}]

Conjugate[expr_Plus] := Map[Conjugate, expr]

Conjugate[expr_Times] := Map[Conjugate, expr]

Conjugate[ Power[b_,-1] ] := 1 / Conjugate[b]

Conjugate[ Power[b_,-1/2] ] := 1 / Conjugate[Sqrt[b]]

Conjugate[ Power[b_, 1/2] ] := Sqrt[Conjugate[b]]
(* NOTE: Branch cut is assumed to be the negative real axis. *)


(* Conjugate[ x_?QuantumMob`Q3`RealQ ] := x *)

NonNegative[ Times[_?NonNegative, a__] ] := NonNegative[ Times[a] ]

NonNegative[ z_ * Conjugate[z_] ] = True;

NonNegative[ Power[_?QuantumMob`Q3`RealQ, _?EvenQ] ] = True;

NonNegative[ HoldPattern[ _?NonNegative + _?NonNegative ] ] = True;

Power[E, Times[z_Complex, Pi, n_]] /; EvenQ[n*z/I] = +1;

Power[E, Times[z_Complex, Pi, n_]] /; OddQ[n*z/I] = -1;


(**** <Formatting> ****)

(* Tip: TeXForm[expr] is equivalent to TeXForm[TraditionalForm[expr]].
   Use TeXForm[StandardForm[expr]] to use StandarfForm. *)

Format @ HoldPattern @ Conjugate[expr_] := Interpretation[
  SpeciesBox[expr, {}, {"\[RawStar]"}],
  Conjugate[expr]
]

Format @ HoldPattern @ Abs[z_] := Interpretation[BracketingBar @ z, Abs @ z]

(**** </Formatting> ****)


AddElaborationPatterns[ Abs[z_] :> Sqrt[z Conjugate[z]] ]

Protect[ Evaluate @ $symb ]

End[]


Begin["`Private`"] (* Complex *)

$symb = Unprotect[Mod, Power, IntegerQ, OddQ, EvenQ]


Let[Complex, {ls__Symbol}] := (
  Let[Species, {ls}];
  Scan[setComplex, {ls}];
 )

setComplex[z_Symbol] := (
  ComplexQ[z] ^= True;
  ComplexQ[z[___]] ^= True;

  AtomQ[z[___]] ^= True; (* EXPERIMENTAL *)

  MultiplyKind[z] ^= Complex;
  MultiplyKind[z[___]] ^= Complex;

  z /: Element[z, Complexes] = True;
  z /: Element[z[___],Complexes] = True;

  z[j___, $] := z[j];
  z[] := z;
 )


Let[Real, {ls__Symbol}] := (
  Let[Complex, {ls}];
  Scan[setReal, {ls}]
 )

setReal[x_Symbol] := (
  MultiplyKind[x] ^= Real;
  MultiplyKind[x[___]] ^= Real;
  x /: QuantumMob`Q3`RealQ[x] = True;
  x /: QuantumMob`Q3`RealQ[x[___]] = True;
  x /: Element[x, Reals] = True;
  x /: Element[x[___], Reals] = True;
  x /: Re[x] = x;
  x /: Im[x] = 0;
  x /: Conjugate[x] = x;
  x /: Conjugate[x[j___]] = x[j];
 )


Let[Integer, {ls__Symbol}] := (
  Let[Real, {ls}];
  Scan[setInteger, {ls}]
 )

setInteger[n_Symbol] := (
  MultiplyKind[n] ^= Integer;
  MultiplyKind[n[___]] ^= Integer;
  n /: IntegerQ[n] = True;
  n /: IntegerQ[n[___]] = True;
  n /: Element[n, Integers] = True;
  n /: Element[n[___], Integers] = True;
 )

IntegerQ[ Mod[_?IntegerQ, 2] ] = True

Mod[ a_?IntegerQ + Mod[b_?IntegerQ, 2], 2] := Mod[a+b, 2]

Mod[ a_?IntegerQ - Mod[b_?IntegerQ, 2], 2] := Mod[a-b, 2]

Mod[ a_?EvenQ + b_, 2 ] := Mod[b, 2]

Mod[ a_?OddQ + b_, 2 ]  := Mod[b+1, 2] /; a != 1

Format[ Mod[nn_Plus, 2] ] := CirclePlus @@ nn


(**** <Binary> ****)

Binary::usage = "Binary represents a binary digit.\nLet[Binary, a, b, \[Ellipsis]] declares a, b, \[Ellipsis] as binary digits."

Let[Binary, {ls__Symbol}] := (
  Let[Integer, {ls}];
  Scan[setBinary, {ls}]
 )

setBinary[n_Symbol] := (
  MultiplyKind[n] ^= Binary;
  MultiplyKind[n[___]] ^= Binary;
  n /: BinaryQ[n] = True;
  n /: BinaryQ[n[___]] = True;
  n /: Element[n, Binaries] = True;
  n /: Element[n[___], Binaries] = True;
 )


BinaryQ::usage = "BinaryQ[x] returns True if x is a binary digit, and False otherwise."

SetAttributes[BinaryQ, Listable]

BinaryQ[0] = True

BinaryQ[1] = True

BinaryQ[Mod[_?IntegerQ, 2]] = True

BinaryQ[expr_Times] := AllTrue[List @@ expr, BinaryQ]

BinaryQ[_] = False


Binaries::usage = "Binaries represents the domain of binary digits, as in x\[Element]Binaries."

Binaries /: Element[0, Binaries] = True

Binaries /: Element[1, Binaries] = True


(* Simplification rules *)

Mod[n_?BinaryQ, 2] = n

Power[n_?BinaryQ, _Integer?Positive] = n
(* NOTE: Here, the Positive test is required for the following reasons:
   * 1 / 0 must cause Power::infy.
   * Note that 1 / 0 is regarded different from Divide[1, 0];
   * 1 / 0 is regarded as 1 * Power[0, -1].
   * Power[0, 0] must cause Power::indet.
   *)

(**** </Binary> ****)


(**** <ComplexQ> ****)

ComplexQ::usage = "ComplexQ[z] returns True if z is complex numbers."

SetAttributes[ComplexQ, Listable]

ComplexQ[_?NumberQ] = True

ComplexQ[_?NumericQ] = True

ComplexQ[_KroneckerDelta] = True

ComplexQ[
  fun : Alternatives @@ Blank /@ {Plus, Times, Power, Log}
 ] := And @@ ComplexQ[ List @@ fun ]
(* Sqrt = Exp = Power *)
  
ComplexQ[
  fun : Alternatives @@ Blank /@ {
    Sin, Csc, Sinh, Csch, ArcSin, ArcCsc, ArcSinh, ArcCsch,
    Cos, Sec, Cosh, Sech, ArcCos, ArcSec, ArcCosh, ArcSech,
    Tan, Cot, Tanh, Coth, ArcTan, ArcTanh, ArcCot, ArcCoth,
    Conjugate, Abs, Sinc, UnitStep
   }
 ] := ComplexQ @@ fun
  
ComplexQ[_] = False

(**** </ComplexQ> ****)


(**** <RealQ> ****)

QuantumMob`Q3`RealQ::usage = "RealQ[z] returns True if z is a real quantity, and False otherwise."

SetAttributes[QuantumMob`Q3`RealQ, Listable]

QuantumMob`Q3`RealQ[I] = False

QuantumMob`Q3`RealQ[ Pi | E | EulerGamma | Infinity ] = True

QuantumMob`Q3`RealQ[_Real] = True

QuantumMob`Q3`RealQ[_Integer] = True

QuantumMob`Q3`RealQ[_Rational] = True

QuantumMob`Q3`RealQ[ z_ * Conjugate[z_] ] = True

QuantumMob`Q3`RealQ[ z_ + Conjugate[z_] ] = True

QuantumMob`Q3`RealQ[ Power[z_, n_Integer] Power[Conjugate[z_], n_Integer] ] /; ComplexQ[z] = True

QuantumMob`Q3`RealQ[ Power[z_, n_Integer] + Power[Conjugate[z_], n_Integer] ] /; ComplexQ[z] = True

QuantumMob`Q3`RealQ[ z_ - Conjugate[z_] ] /; ComplexQ[z] = False

QuantumMob`Q3`RealQ[ Conjugate[z_] - z_ ] /; ComplexQ[z] = False

QuantumMob`Q3`RealQ[ Power[_?NonNegative, _?Positive] ] = True

QuantumMob`Q3`RealQ[ Power[_?Positive, _?QuantumMob`Q3`RealQ] ] = True

QuantumMob`Q3`RealQ[ Power[_?QuantumMob`Q3`RealQ, _?IntegerQ] ] = True

QuantumMob`Q3`RealQ[ Abs[_?CommutativeQ] ] = True

Scan[
  (QuantumMob`Q3`RealQ[#[_?QuantumMob`Q3`RealQ]] = True;) &,
  {Abs, Exp, Sinc, Sin, Csc, Sinh, Csch, Cos, Sec, Cosh, Sech, Tan, Tanh, Cot, Coth}
 ]

QuantumMob`Q3`RealQ[Times[_?QuantumMob`Q3`RealQ, a__]] := QuantumMob`Q3`RealQ[Times[a]]

QuantumMob`Q3`RealQ[Plus[_?QuantumMob`Q3`RealQ, a__]] := QuantumMob`Q3`RealQ[Plus[a]]

QuantumMob`Q3`RealQ[_] = False
(* Like IntegerQ, EvenQ, OddQ, etc., it returns False unless expr passes
   definitely the corresponding test. Namely, they return False if expr is
   undetermined. *)

(**** </RealQ> ****)


(* IntegerQ, EvenQ, OddQ *)

(* NOTE: IntegerQ[expr], EvenQ[expr], and OddQ[expr] return False unless expr
   passes definitely the corresponding test. Namely, they return False if expr
   is undetermined. For example, Information[IntegerQ] says, "IntegerQ[expr]
   returns False unless expr is manifestly an integer (i.e. has head
   Integer)." *)

IntegerQ[Times[a_?IntegerQ, b_?IntegerQ]] = True

IntegerQ[Plus[a_?IntegerQ, b_?IntegerQ]] = True


EvenQ[Times[m_?EvenQ, n_?IntegerQ]] = True

OddQ[Times[m_?OddQ, n_?OddQ]] = True

EvenQ[Plus[x_?EvenQ, y_?EvenQ]] = True

EvenQ[Plus[x_?OddQ, y_?OddQ]] = True

OddQ[Plus[x_?EvenQ, y_?OddQ]] = True


HalfIntegerQ::usage = "HalfIntegerQ[z] returns True if z is exclusively a half-integer. Integer is not regarded as a half-integer."

HalfIntegerQ[Rational[_, 2]] = True

HalfIntegerQ[n_] := OddQ[ Expand[2 n] ]


(**** <Simplification> ****)

CauchySimplify::usage = "CauchySimplify[expr] calls the built-in function Simplify but performs some extra transformations concerning complex variables. All options of Simplify are also available to CauchySimplify."

CauchyFullSimplify::usage = "CauchyFullSimplify[expr] call the built-in function FullSimplify and performs some extra transformations concerning complex variables. All options of FullSimplify is also available to CauchyFullSimplify."

CauchySimplify[expr_, opts___?OptionQ] := Simplify[
  expr,
  opts,
  TransformationFunctions->
    {Automatic, doCauchySimplify}
 ]

CauchyFullSimplify[expr_, opts___?OptionQ] := FullSimplify[
  expr,
  opts,
  TransformationFunctions->
    {Automatic, doCauchySimplify}
 ]

doCauchySimplify[expr_] := expr //. rulesCauchySimplify

rulesCauchySimplify = {
  z_ * Conjugate[z_] :> Abs[z]^2,
  z_ + Conjugate[z_] :> 2 Re[z],
  z_ - Conjugate[z_] :> 2 I Im[z],
  Conjugate[z_] - z_ :> -2 I Im[z],
  Power[z_,1/2] * Power[Conjugate[z_],1/2] :> Abs[z],
  Cos[a_. * Sqrt[z_] * Sqrt[Conjugate[z_]]] :> Cos[a Abs[z]],
  Cosh[a_. * Sqrt[z_] * Sqrt[Conjugate[z_]]] :> Cosh[a Abs[z]],
  Sin[a_. * Sqrt[z_] * Sqrt[Conjugate[z_]]] :> 
    Sin[a * Abs[z]] * Sqrt[z] Sqrt[Conjugate[z]] / Abs[z],
  Sinh[a_. * Sqrt[z_] * Sqrt[Conjugate[z_]]] :> 
    Sinh[a * Abs[z]] * Sqrt[z] Sqrt[Conjugate[z]] / Abs[z],
  Tan[a_. * Sqrt[z_] * Sqrt[Conjugate[z_]]] :> 
    Tan[a * Abs[z]] * Sqrt[z] Sqrt[Conjugate[z]] / Abs[z],
  Tanh[a_. * Sqrt[z_] * Sqrt[Conjugate[z_]]] :> 
    Tanh[a * Abs[z]] * Sqrt[z] Sqrt[Conjugate[z]] / Abs[z]
 }

(**** </Simplifications> ****)


(**** <NGrad> ****)

NGrad::usage = "NGrad[f, {x1,x2,\[Ellipsis]}] returns a numerical approximation of function f at point {x1,x2,\[Ellipsis]}."

Options[NGrad] = {
  Method -> "Central"
}

NGrad[f_, pnt_?VectorQ, opts:OptionsPattern[]] :=
  NGrad[f, pnt, 1.0*^-6, opts] /; VectorQ[pnt, NumericQ]

NGrad[f_, pnt_?VectorQ, h_?NumericQ, OptionsPattern[]] :=
Switch[ OptionValue[Method],
  "Central", grad2Central[f, pnt, h],
  "Forward", grad2Forward[f, pnt, h],
  "Backward", grad2Backward[f, pnt, h],
  "ThreePointForward", grad3Forward[f, pnt, h],
  "ThreePointBackward", grad3Backward[f, pnt, h],
  _, grad2Central[f, pnt, h]
] /; VectorQ[pnt, NumericQ]

grad2Central[f_, x_, h_] := Module[
  { xx = h*One[Length @ x] },
  (Map[f[x + #]&, xx] - Map[f[x - #]&, xx]) / (2*h)
]

grad2Forward[f_, x_, h_] := Module[
  { xx = h*One[Length @ x] },
  (Map[f[x + #]&, xx] - f[x]) / h
]

grad2Backward[f_, x_, h_] := Module[
  { xx = h*One[Length @ x] },
  (f[x] - Map[f[x - #]&, xx]) / h
]

grad3Forward[f_, x_, h_] := Module[
  { xx = h*One[Length @ x] },
  (4*Map[f[x + #]&, xx] - Map[f[x + 2*#]&, xx] - 3*f[x]) / (2*h)
]

grad3Backward[f_, x_, h_] := Module[
  { xx = h*One[Length @ x] },
  -(4*Map[f[x - #]&, xx] - Map[f[x - 2*#]&, xx] - 3*f[x]) / (2*h)
]

(**** </NGrad> ****)


Protect[ Evaluate @ $symb ]

End[] (* Complex *)

EndPackage[]
