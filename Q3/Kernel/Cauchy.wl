(* -*- mode:math -*- *)

BeginPackage["Q3`Cauchy`", {"Q3`Abel`"}]

`Information`$Version = StringJoin[
  $Input, " v",
  StringSplit["$Revision: 2.16 $"][[2]], " (",
  StringSplit["$Date: 2021-04-16 11:40:04+09 $"][[2]], ") ",
  "Mahn-Soo Choi"
 ];

Q3`Q3Clear[];

{ Complex, ComplexQ,
  Real, RealQ,
  Integer, IntegerQ, HalfIntegerQ };

{ LinearMap, LinearMapFirst }

{ CauchySimplify, CauchyFullSimplify };

{ CauchyExpand }; (* OBSOLETE *)


Begin["`Prelude`"]

$symb = Unprotect[
  Conjugate, Abs, Power, NonNegative, Re, Im
 ]

(*** Conjugate[] and Power[] ***)

SetAttributes[{Conjugate, Power}, {ReadProtected}]

Conjugate[ HoldPattern[ Plus[expr__] ] ] := Plus @@ Conjugate @ {expr}

Conjugate[ HoldPattern[ Times[expr__] ] ] := Times @@ Conjugate @ {expr}

Conjugate[ Power[b_,-1] ] := 1 / Conjugate[b]

Conjugate[ Power[b_,-1/2] ] := 1 / Conjugate[Sqrt[b]]

Conjugate[ Power[b_, 1/2] ] := Sqrt[Conjugate[b]]
(* NOTE: Branch cut is assumed to be the negative real axis. *)


(* Conjugate[ x_?RealQ ] := x *)

NonNegative[ Times[_?NonNegative, a__] ] := NonNegative[ Times[a] ]

NonNegative[ z_ Conjugate[z_] ] = True

NonNegative[ Power[_?RealQ, _?EvenQ] ] = True

NonNegative[ HoldPattern[ _?NonNegative + _?NonNegative ] ] = True

(* Abs[z_Times] := Times[ Abs /@ z ] *)
(* Mathematica 12.2: Use FunctionExpand[expr] *)

(* Abs[Power[z_,-1]] := 1 / Abs[z] *)
(* Integrated into Mathematica v12.2 *)

(* Abs[Power[z_,-1/2]] := 1 / Sqrt[Abs[z]] *)
(* Integrated into Mathematica v12.2 *)

(* Power[ Abs[x_?RealQ], n_?EvenQ ] := Power[x, n] *)
(* Mathematica 12.2: Use Simplify[expr, Element[x, Reals]] *)

(* Power[ Power[x_?RealQ, n_?EvenQ], 1/2] :=   Power[Abs[x], n/2] *)
(* Mathematica 12.2: Use Simplify[expr, Element[x, Reals]] *)

(* Power[-Power[x_?RealQ, n_?EvenQ], 1/2] := I Power[Abs[x], n/2] *)
(* Mathematica 12.2: Use Simplify[expr, Element[x, Reals]] *)

Power[E, Times[z_Complex, Pi, n_]] /; EvenQ[n*z/I] = +1

Power[E, Times[z_Complex, Pi, n_]] /; OddQ[n*z/I] = -1


(**** <Formatting> ****)

(* Tip: TeXForm[expr] is equivalent to TeXForm[TraditionalForm[expr]].
   Use TeXForm[StandardForm[expr]] to use StandarfForm. *)

$Star = Style["*", FontColor -> Red]

Format[ HoldPattern[ Conjugate[z_Symbol] ] ] :=
  SpeciesBox[z, {}, {$Star}] /; $FormatSpecies
 
Format[ HoldPattern[ Conjugate[z_Symbol?SpeciesQ[j___]] ] ] :=
  SpeciesBox[z, {j}, {$Star}] /; $FormatSpecies

(* f[...] with f not declared as a Species is regarded as a normal function. *)
Format[ HoldPattern[ Conjugate[f_Symbol[z___]] ] ] :=
  SpeciesBox[
    Row @ { "(", f[z], ")" },
    {},
    {$Star}
   ] /; $FormatSpecies

Format[ HoldPattern[ Abs[z_] ] ] := BracketingBar[z]

(**** </Formatting> ****)


(* If all internal handlings fail, then these are the final resort. *)

Re[ z:Except[_?NumericQ] ] := ( z + Conjugate[z] ) / 2

Im[ z:Except[_?NumericQ] ] := ( z - Conjugate[z] ) / (2 I)


Protect[ Evaluate @ $symb ]

End[] (* `Prelude` *)

(**********************************************************************)

Begin["`Complex`"]

$symb = Unprotect[
  Mod, IntegerQ, OddQ, EvenQ,
  Let
]

Let[Complex, {ls__Symbol}] := (
  Let[Species, {ls}];
  Scan[setComplex, {ls}];
 )

setComplex[z_Symbol] := (
  ComplexQ[z] ^= True;
  ComplexQ[z[___]] ^= True;

  z /: Element[z, Complexes] = True;
  z /: Element[z[___],Complexes] = True;
 )


Real::usage = "In Cauchy package, Let[Real, a,b,...] declares a, b, ... as real numbers.\n" <> Real::usage

Let[Real, {ls__Symbol}] := (
  Let[Complex, {ls}];
  Scan[setReal, {ls}]
 )

setReal[x_Symbol] := (
  x /: RealQ[x] = True;
  x /: RealQ[x[___]] = True;
  x /: Element[x, Reals] = True;
  x /: Element[x[___], Reals] = True;
  x /: Conjugate[x] := x;
  x /: Conjugate[x[j___]] := x[j];
 )

Integer::usage = "In Cauchy` package, Let[Integer, a,b,...] declares a, b, ... as integer numbers.\n" <> Integer::usage

Let[Integer, {ls__Symbol}] := (
  Let[Real, {ls}];
  Scan[setInteger, {ls}]
 )

setInteger[n_Symbol] := (
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


(*** Tests for numeric constants ***)

ComplexQ::usage = "ComplexQ[z] returns True if z is complex numbers."

SetAttributes[ComplexQ, Listable]

ComplexQ[_?NumberQ] = True

ComplexQ[_?NumericQ] = True

ComplexQ[ _KroneckerDelta ] = True

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


RealQ::usage = "RealQ[z] returns True if z is a real quantity, and False otherwise."

RealQ[I] = False

RealQ[Pi] = True

RealQ[Infinity] = True

RealQ[_Real] = True

RealQ[_Integer] = True

RealQ[_Rational] = True

RealQ[ z_ Conjugate[z_] ] = True

RealQ[ z_ + Conjugate[z_] ] = True

RealQ[ Power[z_, n_Integer] Power[Conjugate[z_], n_Integer] ] /; ComplexQ[z] = True

RealQ[ Power[z_, n_Integer] + Power[Conjugate[z_], n_Integer] ] /; ComplexQ[z] = True

RealQ[ z_ - Conjugate[z_] ] /; ComplexQ[z] = False

RealQ[ Conjugate[z_] - z_ ] /; ComplexQ[z] = False

RealQ[ Power[_?NonNegative, _?Positive] ] = True

RealQ[ Power[_?Positive, _?RealQ] ] = True

RealQ[ Power[_?RealQ, _?IntegerQ] ] = True

RealQ[ Abs[_?CommutativeQ] ] = True

Scan[
  (RealQ[#[_?RealQ]] = True;) &,
  {Abs, Exp, Sinc, Sin, Csc, Sinh, Csch, Cos, Sec, Cosh, Sech, Tan, Tanh, Cot, Coth}
 ]

RealQ[Times[_?RealQ, a__]] := RealQ[Times[a]]

RealQ[Plus[_?RealQ, a__]] := RealQ[Plus[a]]

RealQ[_] := False
(* Like IntegerQ, EvenQ, OddQ, etc., it returns False unless expr passes
   definitely the corresponding test. Namely, they return False if expr is
   undetermined. *)


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
  z_ Conjugate[z_] -> Abs[z]^2,
  z_ + Conjugate[z_] -> 2 Re[z],
  z_ - Conjugate[z_] -> 2 I Im[z],
  Conjugate[z_] - z_ -> -2 I Im[z],
  Power[z_,1/2] Power[Conjugate[z_],1/2] -> Abs[z],
  Cos[a_. Sqrt[z_] Sqrt[Conjugate[z_]]] -> Cos[a Abs[z]],
  Cosh[a_. Sqrt[z_] Sqrt[Conjugate[z_]]] -> Cosh[a Abs[z]],
  Sin[a_. Sqrt[z_] Sqrt[Conjugate[z_]]] -> 
    Sin[a Abs[z]] Sqrt[z] Sqrt[Conjugate[z]] / Abs[z],
  Sinh[a_. Sqrt[z_] Sqrt[Conjugate[z_]]] -> 
    Sinh[a Abs[z]] Sqrt[z] Sqrt[Conjugate[z]] / Abs[z],
  Tan[a_. Sqrt[z_] Sqrt[Conjugate[z_]]] -> 
    Tan[a Abs[z]] Sqrt[z] Sqrt[Conjugate[z]] / Abs[z],
  Tanh[a_. Sqrt[z_] Sqrt[Conjugate[z_]]] -> 
    Tanh[a Abs[z]] Sqrt[z] Sqrt[Conjugate[z]] / Abs[z]
 }

(**** </Simplifications> ****)


CauchyExpand::usage = "CauchyExpand[expr] expands out functions of complex variables."

CauchyExpand[expr_] := (
  Message[Q3`Q3General::obsolete, CauchyExpand, Elaborate];
  Elaborate[expr]
 )

Protect[ Evaluate @ $symb ]

End[] (* `Complex` *)


Q3`Q3Protect[]


EndPackage[]
