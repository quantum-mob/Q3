(* ::Package:: *)
BeginPackage["QuantumMob`Q3`", {"System`"}];

{ Complex, ComplexQ,
  Real, RealQ,
  Integer, IntegerQ, HalfIntegerQ,
  Binary, BinaryQ, Binaries };

{ CauchySimplify, CauchyFullSimplify };

{ NGrad };


Begin["`Private`"];
$symb = Unprotect[E, NonNegative, Mod, IntegerQ, OddQ, EvenQ];

(**** <Conjugate> ****)
(* Conjugate carries NO definitions of any kind. Measured on Mathematica
   15.0.1: any values attached to Conjugate disable its packed-array fast
   path (values on Power additionally disable Abs, Re, Im), and because
   Conjugate is Listable, attribute threading precedes DownValue lookup,
   so no whole-array bypass rule can ever intercept an array argument.
   The former automatic distribution rules are therefore relocated: species
   conjugation stays immediate through the UpValues installed by setReal
   below, while distribution over sums, products, and powers is performed
   by Elaborate and CauchySimplify via the patterns registered here.
   BEHAVIOR CHANGE: a bare Conjugate[a + b] now stays wrapped (and is
   displayed with the star) until Elaborate or CauchySimplify is applied. *)

AddElaborationPatterns[
  HoldPattern @ Conjugate[expr_Plus] :> Map[Conjugate, expr],
  HoldPattern @ Conjugate[expr_Times] :> Map[Conjugate, expr],
  HoldPattern @ Conjugate[ Power[b_, -1] ] :> 1 / Conjugate[b],
  HoldPattern @ Conjugate[ Power[b_, -1/2] ] :> 1 / Conjugate[Sqrt[b]],
  HoldPattern @ Conjugate[ Power[b_, 1/2] ] :> Sqrt[Conjugate[b]]
];
(* NOTE: Branch cut is assumed to be the negative real axis. *)


(* WARNING (2026-08-15 v4.7.0): This makes Conjugate on array 100 times slower. *)
(* Unprotect[Conjugate]; *)
(* Conjugate[ x_?RealQ ] := x *)
(* Protect[Conjugate]; *)

NonNegative[ Times[_?NonNegative, a__] ] := NonNegative[ Times[a] ];

NonNegative[ z_ * Conjugate[z_] ] = True;

NonNegative[ Power[_?RealQ, _?EvenQ] ] = True;

NonNegative[ HoldPattern[ _?NonNegative + _?NonNegative ] ] = True;

(* installed as UpValues on E: consulted only when E appears literally as
   an argument, so numeric arrays are never affected *)
E /: Power[E, Times[n_, z_Complex, Pi]] /; EvenQ[n*z/I] = +1;

E /: Power[E, Times[n_, z_Complex, Pi]] /; OddQ[n*z/I] = -1;


(**** <Formatting> ****)
(* Tip: TeXForm[expr] is equivalent to TeXForm[TraditionalForm[expr]].
   Use TeXForm[StandardForm[expr]] to use StandarfForm. *)
MakeBoxes[expr : Conjugate[z_], fmt_] := ToBoxes[
  Interpretation[SpeciesBox[z, {}, {"\[RawStar]"}], expr],
  fmt
]

MakeBoxes[expr : Abs[z_], fmt_] :=
  ToBoxes[Interpretation[BracketingBar @ z, expr], fmt]
(**** </Formatting> ****)


AddElaborationPatterns[ Abs[z_] :> Sqrt[z Conjugate[z]] ];


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
);


Let[Real, {ls__Symbol}] := (
  Let[Complex, {ls}];
  Scan[setReal, {ls}]
);

setReal[x_Symbol] := (
  MultiplyKind[x] ^= Real;
  MultiplyKind[x[___]] ^= Real;
  x /: RealQ[x] = True;
  x /: RealQ[x[___]] = True;
  x /: Element[x, Reals] = True;
  x /: Element[x[___], Reals] = True;
  x /: Re[x] = x;
  x /: Im[x] = 0;
  x /: Conjugate[x] = x;
  x /: Conjugate[x[j___]] = x[j];
);


Let[Integer, {ls__Symbol}] := (
  Let[Real, {ls}];
  Scan[setInteger, {ls}]
);

setInteger[n_Symbol] := (
  MultiplyKind[n] ^= Integer;
  MultiplyKind[n[___]] ^= Integer;
  n /: IntegerQ[n] = True;
  n /: IntegerQ[n[___]] = True;
  n /: Element[n, Integers] = True;
  n /: Element[n[___], Integers] = True;
);


IntegerQ[ Mod[_?IntegerQ, 2] ] = True;

Mod[ a_?IntegerQ + Mod[b_?IntegerQ, 2], 2 ] := Mod[a+b, 2];

Mod[ a_?IntegerQ - Mod[b_?IntegerQ, 2], 2 ] := Mod[a-b, 2];

Mod[ a_?EvenQ + b_, 2 ] := Mod[b, 2];

Mod[ a_?OddQ + b_, 2 ]  := Mod[b+1, 2] /; a != 1;

MakeBoxes[expr : Mod[nn_Plus, 2], fmt_] :=
  ToBoxes[Interpretation[CirclePlus @@ nn, expr], fmt];


(**** <Binary> ****)
Binary::usage = "Binary represents a binary digit.\nLet[Binary, a, b, \[Ellipsis]] declares a, b, \[Ellipsis] as binary digits.";

Let[Binary, {ls__Symbol}] := (
  Let[Integer, {ls}];
  Scan[setBinary, {ls}]
);

setBinary[n_Symbol] := (
  MultiplyKind[n] ^= Binary;
  MultiplyKind[n[___]] ^= Binary;
  n /: Power[n, _Integer?Positive] = n;
  n /: Power[n[j___], _Integer?Positive] = n[j];
  n /: BinaryQ[n] = True;
  n /: BinaryQ[n[___]] = True;
  n /: Element[n, Binaries] = True;
  n /: Element[n[___], Binaries] = True;
);


BinaryQ::usage = "BinaryQ[x] returns True if x is a binary digit, and False otherwise.";

SetAttributes[BinaryQ, Listable];

BinaryQ[0] = True;

BinaryQ[1] = True;

BinaryQ[Mod[_?IntegerQ, 2]] = True;

BinaryQ[expr_Times] := AllTrue[List @@ expr, BinaryQ];

BinaryQ[_] = False;


Binaries::usage = "Binaries represents the domain of binary digits, as in x\[Element]Binaries.";

Binaries /: Element[0, Binaries] = True;

Binaries /: Element[1, Binaries] = True;


(* Simplification rules *)
Mod[n_?BinaryQ, 2] = n;

(* Power[0|1, k] is native; Binary species carry UpValues from setBinary;
   the remaining BinaryQ case, Mod[_?IntegerQ, 2], is covered here as an
   UpValue on Mod (which already carries the Mod-arithmetic rules above) *)
Mod /: Power[m : Mod[_?IntegerQ, 2], _Integer?Positive] := m;
(* NOTE: Here, the Positive test is required for the following reasons:
   * 1 / 0 must cause Power::infy.
   * Note that 1 / 0 is regarded different from Divide[1, 0];
   * 1 / 0 is regarded as 1 * Power[0, -1].
   * Power[0, 0] must cause Power::indet.
   *)
(**** </Binary> ****)


(**** <ComplexQ> ****)
ComplexQ::usage = "ComplexQ[z] returns True if z is complex numbers.";

SetAttributes[ComplexQ, Listable];

ComplexQ[_?NumberQ] = True;

ComplexQ[_?NumericQ] = True;

ComplexQ[_KroneckerDelta] = True;

ComplexQ[
  fun : Alternatives @@ Blank /@ {Plus, Times, Power, Log}
] := And @@ ComplexQ[ List @@ fun ];
(* Sqrt = Exp = Power *)
  
ComplexQ[
  fun : Alternatives @@ Blank /@ {
    Sin, Csc, Sinh, Csch, ArcSin, ArcCsc, ArcSinh, ArcCsch,
    Cos, Sec, Cosh, Sech, ArcCos, ArcSec, ArcCosh, ArcSech,
    Tan, Cot, Tanh, Coth, ArcTan, ArcTanh, ArcCot, ArcCoth,
    Conjugate, Abs, Sinc, UnitStep
  }
] := ComplexQ @@ fun;
  
ComplexQ[_] = False;
(**** </ComplexQ> ****)


(**** <RealQ> ****)
RealQ::usage = "RealQ[z] returns True if z is a real quantity, and False otherwise.";

SetAttributes[RealQ, Listable];

RealQ[I] = False;

RealQ[ Pi | E | EulerGamma | Infinity ] = True;

RealQ[_Real] = True;

RealQ[_Integer] = True;

RealQ[_Rational] = True;

RealQ[ z_ * Conjugate[z_] ] = True;

RealQ[ z_ + Conjugate[z_] ] = True;

RealQ[ Power[z_, n_Integer] Power[Conjugate[z_], n_Integer] ] /; ComplexQ[z] = True;

RealQ[ Power[z_, n_Integer] + Power[Conjugate[z_], n_Integer] ] /; ComplexQ[z] = True;

RealQ[ z_ - Conjugate[z_] ] /; ComplexQ[z] = False;

RealQ[ Conjugate[z_] - z_ ] /; ComplexQ[z] = False;

RealQ[ Power[_?NonNegative, _?Positive] ] = True;

RealQ[ Power[_?Positive, _?RealQ] ] = True;

RealQ[ Power[_?RealQ, _?IntegerQ] ] = True;

RealQ[ Abs[_?CommutativeQ] ] = True;

Scan[
  (RealQ[#[_?RealQ]] = True;) &,
  {Abs, Exp, Sinc, Sin, Csc, Sinh, Csch, Cos, Sec, Cosh, Sech, Tan, Tanh, Cot, Coth}
]

RealQ[Times[_?RealQ, a__]] := RealQ[Times[a]];

RealQ[Plus[_?RealQ, a__]] := RealQ[Plus[a]];

RealQ[_] = False;
(* Returns False unless expr passes definitely the corresponding test. 
   Namely, they return False if expr is undetermined. *)
(**** </RealQ> ****)


(* IntegerQ, EvenQ, OddQ *)

(* NOTE: IntegerQ[expr], EvenQ[expr], and OddQ[expr] return False unless expr
   passes definitely the corresponding test. Namely, they return False if expr
   is undetermined. For example, Information[IntegerQ] says, "IntegerQ[expr]
   returns False unless expr is manifestly an integer (i.e. has head
   Integer)." *)

IntegerQ[Times[_?IntegerQ, _?IntegerQ]] = True;

IntegerQ[Plus[_?IntegerQ, _?IntegerQ]] = True;


EvenQ[Times[_?EvenQ, _?IntegerQ]] = True;

OddQ[Times[_?OddQ, _?OddQ]] = True;

EvenQ[Plus[_?EvenQ, _?EvenQ]] = True;

EvenQ[Plus[_?OddQ, _?OddQ]] = True;

OddQ[Plus[_?EvenQ, _?OddQ]] = True;


HalfIntegerQ::usage = "HalfIntegerQ[z] returns True if z is exclusively a half-integer. Integer is not regarded as a half-integer.";

HalfIntegerQ[Rational[_, 2]] = True;

HalfIntegerQ[n_] := OddQ[Expand[2 n]];


(**** <Simplification> ****)
CauchySimplify::usage = "CauchySimplify[expr] calls the built-in function Simplify but performs some extra transformations concerning complex variables. All options of Simplify are also available to CauchySimplify.";

CauchyFullSimplify::usage = "CauchyFullSimplify[expr] call the built-in function FullSimplify and performs some extra transformations concerning complex variables. All options of FullSimplify is also available to CauchyFullSimplify.";

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
  HoldPattern @ Conjugate[expr_Plus] :> Map[Conjugate, expr],
  HoldPattern @ Conjugate[expr_Times] :> Map[Conjugate, expr],
  HoldPattern @ Conjugate[ Power[b_, -1] ] :> 1 / Conjugate[b],
  HoldPattern @ Conjugate[ Power[b_, -1/2] ] :> 1 / Conjugate[Sqrt[b]],
  HoldPattern @ Conjugate[ Power[b_, 1/2] ] :> Sqrt[Conjugate[b]],
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
(**** </Simplification> ****)


(**** <NGrad> ****)
NGrad::usage = "NGrad[f, {x1,x2,\[Ellipsis]}] returns a numerical approximation of function f at point {x1,x2,\[Ellipsis]}.";

Options[NGrad] = {
  Method -> "Central"
};

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
] /; VectorQ[pnt, NumericQ];

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


Protect[ Evaluate @ $symb ];
End[]; (* Complex *)

EndPackage[];
