(* -*- mode:math -*- *)
(* Mahn-Soo Choi *)
(* $Date: 2021-01-15 10:06:32+09 $ *)
(* $Revision: 1.6 $ *)

BeginPackage["Q3`Abel`"]

Unprotect[Evaluate[$Context<>"*"]]

Notice::usage = "Notice is a symbol to which general messages concerning Q3 are attached.\nIt is similar to General, but its Context is Q3."

Notice::obsolete = "The symbol `` is OBSOLETE. Use `` instead."

Notice::newUI = "An angle should come first. The order of the input arguments of `` has been changed since Q3 v1.2.0."


{ Supplement, SupplementBy, Common, CommonBy };
{ Choices, Successive };
{ ShiftLeft, ShiftRight };
{ PseudoDivide };

{ Chain };

{ Let };

{ Base, Flavors, FlavorMost, FlavorLast, FlavorNone, FlavorMute, Any };

{ Species, SpeciesQ, AnySpeciesQ };

{ SpeciesBox,
  $FormatSpecies,
  $SubscriptDelimiter, $SuperscriptDelimiter };

{ NonCommutative, NonCommutativeQ, AnyNonCommutativeQ,
  NonCommutativeSpecies,
  CommutativeQ,
  ObscureQ,
  Kind, Dimension,
  Hermitian, HermitianQ,
  Antihermitian, AntihermitianQ };

{ Dagger, HermitianConjugate = Dagger,
  Topple, DaggerTranspose = Topple,
  Tee, TeeTranspose,
  Peel };

{ Primed, DoublePrimed };

{ PlusDagger, TimesDaggerRight, TimesDaggerLeft };

{ CoefficientTensor, MultiplyDegree };

{ ReplaceBy, ReplaceByFourier, ReplaceByInverseFourier };

{ Garner, $GarnerHeads, $GarnerTests };

{ Elaborate, $ElaborationRules, $ElaborationHeads };

{ Commutator, Anticommutator };

{ Multiply, MultiplyExp, MultiplyPower, MultiplyDot,
  DistributableQ };

{ MultiplyExpand };

{ Lie, LiePower, LieSeries, LieExp };


Begin["`Private`"]

$symb = Unprotect[
  Conjugate, NonCommutativeMultiply, Inverse
 ]

Choices::usage = "Choices[a,n] gives all possible choices of n elements out of the list a.\nUnlike Subsets, it allows to choose duplicate elements.\nSee also: Subsets, Tuples."

Choices[a_List, n_Integer] := Union[Sort /@ Tuples[a, n]]


Supplement::usage = "Supplement[a, b, c, ...] returns the elements in a that are not in any of b, c, .... It is similar to the builtin Complement, but unlike Complement, treats a as a List (not Mathematical set). That is, the order is preserved."

Supplement[a_List, b__List] := DeleteCases[ a, Alternatives @@ Union[b], 1 ]
(* Implementation 3: Fast and versatile. *)

(* Supplement[a_List, b__List] := a /. Thread[Union[b] -> Nothing] *)
(* Implementation 2: Faster than the obvious approach as in Implementation 1 below.
   However, it works only when a and b are simple arrays (not allowed to
   include sublists, in which case unexpected results will arise).
   *)

(* Supplement[a_List, b_List] := Select[a, ! MemberQ[b, #] &] *)
(* Implementation 1: Straightforward, but slow. *)


SupplementBy::usage = "SupplementBy[a, b, c, ..., f] returns the elements in a that do not appear in any of sets on b, c, ... with all the tests made after applying f on a, b, c, ... .\nLike Supplement, the order is preserved."
  
SupplementBy[a_List, b__List, f_] := Module[
  { aa = f /@ a,
    form = Alternatives @@ Map[f, Union[b]] },
  aa = Map[ Not @ MatchQ[#, form]&, aa ];
  Pick[ a, aa ]
 ]

Common::usage = "Common[a, b, c, ...] returns the elements of a that appear in all subsequent lists.\nIt is similar to the built-in function Intersection, but treats the first argument as a List (not mathematical sets) and hence preserves the order."

Common[a_List, b__List] := Cases[ a, Alternatives @@ Intersection[b], 1 ]
(* Implementation 3: Fast and versatile. *)

(* Common[a_List, b_List] := Select[a, MemberQ[b,#]& ] *)
(* Implementation 1: Straightforward, but slow. *)

CommonBy::usage = "CommonBy[a, b, c, ..., f] returns the elements of a that appear in all of b, c, ..., after applying f.\nLike Common, the order is preserved."
  
CommonBy[a_List, b__List, f_] := Module[
  { aa = f /@ a,
    form = Alternatives @@ Map[f, Intersection[b]] },
  aa = Map[ MatchQ[#, form]&, aa ];
  Pick[ a, aa ]
 ]

Successive::usage = "Successive[f, {x1,x2,x3,...}] returns {f[x1,x2], f[x2,x3], ...}. Successive[f, list, n] applies f on n successive elements of list. Successive[f, list, 2] is equivalent to Successive[f,list]. Successive[f, list, 1] is equivalent to Map[f, list]."

Successive[f_, a_List] := f @@@ Transpose @ {Most @ a, Rest @ a}

Successive[f_, a_List, n_Integer] := f @@@ Transpose @ Table[
  Drop[RotateLeft[a, j], 1 - n],
  {j, 0, n - 1}
 ] /; n > 0


ShiftLeft::usage = "ShiftLeft[list, n] shifts the elements in list by n positions to the left and pad n 0s on the right.\nSimilar to RotateLeft, but does not cycle the elements.\nIf n is omitted, it is assumed to be 1."

ShiftLeft[a_List, n_Integer, x_:0] := PadRight[Drop[a,n], Length[a], x] /; n>0

ShiftLeft[a_List, n_Integer, x_:0] := PadLeft[Drop[a,n], Length[a], x] /; n<0

ShiftLeft[a_List, 0, x_:0] := a

ShiftLeft[a_List] := ShiftLeft[a, 1, 0]


ShiftRight::usage = "ShiftRight[list, n] shifts the elements in list by n positions to the right and pad n 0s on the left.\nSimilar to RotateRight, but does not cycle the elements.\nIf n is omitted, it is assumed to be 1."

ShiftRight[a_List, n_Integer, x_:0] := PadLeft[Drop[a,-n], Length[a], x] /; n>0

ShiftRight[a_List, n_Integer, x_:0] := PadRight[Drop[a,-n], Length[a], x] /; n<0

ShiftRight[a_List, 0, x_:0] := a

ShiftRight[a_List] := ShiftRight[a, 1, 0]


PseudoDivide::usage = "PseudoDivide[x, y] returns x times the PseudoInverse of y."

SetAttributes[PseudoDivide, Listable]

PseudoDivide[x_, 0] = 0

PseudoDivide[x_, 0.] = 0.

PseudoDivide[x_, y_] := x/y


Chain::usage = "Chain[a, b, ...] constructs a chain of links connecting a, b, ... consecutively."

Chain[a:Except[_List]] := {}

Chain[a:Except[_List], b:Except[_List]] := Rule[a, b]

Chain[m_List] := 
  Flatten[Chain /@ Transpose[m]] /; ArrayQ[m, Except[1]]

Chain[m_List, b_] := Flatten @ { Chain@m, Chain[Last@m, b] } /;
  ArrayQ[m, Except[1]]

Chain[m_?VectorQ, b_] := Flatten @ Map[Chain[#, b] &, m]

Chain[a_, m_List] := Flatten @ { Chain[a, First@m], Chain@m } /;
  ArrayQ[m, Except[1]]

Chain[a_, m_?VectorQ] := Map[Chain[a, #] &, m]

Chain[a__, m_List, b__] :=
  Flatten @ { Chain[a, First@m], Chain@m, Chain[Last@m, b] } /;
  ArrayQ[m, Except[1]]

Chain[a_, b_, c__] := Flatten @ { Chain[a, b], Chain[b, c] }

Chain[aa_List] := Chain @@ aa


Base::usage = "Base[c[j,...,s]] returns the generator c[j,...] with the Flavor indices sans the final if c is a Species and the final Flavor index is special at all; otherwise just c[j,...,s]."

SetAttributes[Base, Listable]

Base[z_] := z


Flavors::usage = "Flavors[c[j]] returns the list of Flavor indices {j} of the generator c[j]."

SetAttributes[Flavors, Listable]

Flavors[ Conjugate[c_?SpeciesQ] ] := Flavors[c]

Flavors[ Dagger[c_?SpeciesQ] ] := Flavors[c]

HoldPattern @ Flavors[ Tee[c_?SpeciesQ] ] := Flavors[c]

Flavors[ _Symbol?SpeciesQ[j___] ] := {j} (* List @@ c[j] *)

Flavors[ _Symbol?SpeciesQ ] = {} (* NOT equal to List @@ c *)

FlavorMost::usage = "FlavorMost[c[j]] returns the list of Flavor indices dropping the last one, i.e., Most[{j}]."

SetAttributes[FlavorMost, Listable]

FlavorMost[ Conjugate[c_?SpeciesQ] ] := FlavorMost[c]

FlavorMost[ Dagger[c_?SpeciesQ] ] := FlavorMost[c]

HoldPattern @ FlavorMost[ Tee[c_?SpeciesQ] ] := FlavorMost[c]

FlavorMost[ _Symbol?SpeciesQ[j__] ] := Most @ {j}

FlavorMost[ _?SpeciesQ ] = Missing["NoFlavor"]

FlavorLast::usage = "FlavorLast[c[j]] returns the last Flavor index of the element c[j], i.e., Last[{j}]."

SetAttributes[FlavorLast, Listable]

FlavorLast[ Conjugate[c_?SpeciesQ] ] := FlavorLast[c]

FlavorLast[ Dagger[c_?SpeciesQ] ] := FlavorLast[c]

HoldPattern @ FlavorLast[ Tee[c_?SpeciesQ] ] := FlavorLast[c]

FlavorLast[ _Symbol?SpeciesQ[___,j_] ] := j

FlavorLast[ _?SpeciesQ ] = Missing["NoFlavor"]


FlavorNone::usage = "FlavorNone[S[i, j, ...]] for some Species S gives S[i, j, ..., None]. Notable examples are Qubit in Quisso package and Spin in Wigner package. Note that FlavorNone is Listable."
  
SetAttributes[FlavorNone, Listable]

FlavorNone[a_] := a (* Does nothing unless specified explicitly *)


FlavorMute::usage = "FlavorMute[S[i, j, ..., k]] for some Species S gives S[i, j, ..., None], i.e., with the last Flavor replaced with None. Notable examples are Qubit in Quisso package and Spin in Wigner package. Note that FlavorMute is Listable."
  
SetAttributes[FlavorMute, Listable]

FlavorMute[a_] := a (* Does nothing unless specified explicitly *)


Any::usage = "Any represents a dummy Flavor index."

SetAttributes[Any, ReadProtected]

Format[Any] = "\[SpaceIndicator]"


Kind::usage = "Kind[a] returns the type of Species."

SetAttributes[Kind, Listable]

Kind[ Inverse[x_] ] := Kind[x]

Kind[ Conjugate[x_] ] := Kind[x]

Kind[ Dagger[x_] ] := Kind[x]

Kind[ Tee[x_] ] := Kind[x]

Kind[_] = "UnknownSpecies"


Dimension::usage = "Dimension[A] gives the Hilbert space dimension associated with the system A."

SetAttributes[Dimension, Listable]


Let::usage = "Let[Symbol, a, b, ...] defines the symbols a, b, ... to be Symbol, which can be Species, Complex, Real, Integer, etc."

Species::usage = "Species represents a tensor-like quantity, which is regarded as a multi-dimensional regular array of numbers.\nLet[Species, a, b, ...] declares the symbols a, b, ... to be Species.\nIn the Wolfram Language, a tensor is represented by a multi-dimenional regular List. A tensor declared by Let[Species, ...] does not take a specific structure, but only regarded seemingly so."

SetAttributes[Let, {HoldAll, ReadProtected}]

Let[name_Symbol, ls__Symbol, opts___?OptionQ] := Let[name, {ls}, opts]

Let[Species, {ls__Symbol}] := (
  ClearAll[ls];
  Scan[setSpecies, {ls}]
 )

setSpecies[x_Symbol] := (
  SetAttributes[x, {NHoldAll, ReadProtected}];

  SpeciesQ[x] ^= True;
  SpeciesQ[x[___]] ^= True;

  Dimension[x] ^= 1;
  Dimension[x[___]] ^= 1;

  x[jj__] := x @@ ReplaceAll[{jj}, q_?SpeciesQ :> ToString[q]] /;
    Or @@ SpeciesQ /@ {jj};
  (* NOTE: If a Flavor index itself is a species, many tests fail to work
     properly. A common example is CommutativeQ. To prevent nasty errors, such
     Flavors are converted to String. *)

  x[i___][j___] := x[i,j];
  
  x[j___] := Flatten @ ReplaceAll[ Distribute[Hold[j], List], Hold -> x ] /;
    MemberQ[{j}, _List];
  (* NOTE: Flatten is required for All with spinful bosons and fermions.
     See Let[Bosons, ...] and Let[Fermions, ...]. *)
  (* NOTE: Distribute[x[j], List] will hit the recursion limit. *)

  Format[ x[j___] ] := DisplayForm @ SpeciesBox[x, {j}, {}] /; $FormatSpecies;
 )


SpeciesQ::usage = "SpeciesQ[a] returns True if a is a Species."

SpeciesQ[_] = False


AnySpeciesQ::usaage = "AnySpeciesQ[z] returns True if z itself is an Species or a modified form z = Conjugate[x], Dagger[x], Tee[x] of another Species x."

AnySpeciesQ[ _?SpeciesQ ] = True

AnySpeciesQ[ Inverse[_?SpeciesQ] ] = True

AnySpeciesQ[ Conjugate[_?SpeciesQ] ] = True

AnySpeciesQ[ Dagger[_?SpeciesQ] ] = True

AnySpeciesQ[ Tee[_?SpeciesQ] ] = True

AnySpeciesQ[ _ ] = False


NonCommutative::usage = "NonCommutative represents a non-commutative element.\nLet[NonCommutative, a, b, ...] declares a[...], b[...], ... to be NonCommutative."

Let[NonCommutative, {ls__Symbol}] := (
  Let[Species, {ls}];
  Scan[setNonCommutative, {ls}]
 )

setNonCommutative[x_Symbol] := (
  NonCommutativeQ[x] ^= True;
  NonCommutativeQ[x[___]] ^= True;

  Kind[x] ^= NonCommutative;
  Kind[x[___]] ^= NonCommutative;
 )


Format[ Inverse[op_?NonCommutativeQ] ] :=
  DisplayForm @ SpeciesBox[op, { }, {"-1"}] /; $FormatSpecies
 
Format[ Inverse[op_Symbol?NonCommutativeQ[j___]] ] :=
  DisplayForm @ SpeciesBox[op, {j}, {"-1"}] /; $FormatSpecies

Inverse[ Power[E, expr_] ] := MultiplyExp[-expr] /;
  Not @ CommutativeQ @ expr
(* NOTE: Recall that Not[CommutativeQ[expr]] is not the same as
   NonCommutativeQ[expr]. *)


NonCommutativeQ::usage = "NonCommutativeQ[a] returns True of a is a non-commutative element."

SetAttributes[NonCommutativeQ, Listable]

NonCommutativeQ[_] = False


AnyNonCommutativeQ::usaage = "AnyNonCommutativeQ[z] returns True if z itself is a NonCommutative element or has the form Conjugate[x], Dagger[x], Tee[x] of another NonCommutative x."

SetAttributes[AnyNonCommutativeQ, Listable]

AnyNonCommutativeQ[ _?NonCommutativeQ ] = True

AnyNonCommutativeQ[ Inverse[_?NonCommutativeQ] ] = True

AnyNonCommutativeQ[ Conjugate[_?NonCommutativeQ] ] = True

AnyNonCommutativeQ[ Dagger[_?NonCommutativeQ] ] = True

AnyNonCommutativeQ[ Tee[_?NonCommutativeQ] ] = True

AnyNonCommutativeQ[ _ ] = False


CommutativeQ::usage = "CommutativeQ[expr] returns True if the expression expr is free of any non-commutative element.\nCommutativeQ[expr] is equivalent to FreeQ[expr, _?NonCommutativeQ]."

SetAttributes[CommutativeQ, Listable]

CommutativeQ[z_] := FreeQ[z, _?NonCommutativeQ]


NonCommutativeSpecies::usage = "NonCommutativeSpecies[expr] returns the list of all NonCommutative Species appearing in EXPR."

NonCommutativeSpecies[expr_] := Select[
  Union @ FlavorMute @
    Cases[ { Normal[expr, Association] }, _?SpeciesQ, Infinity ],
  NonCommutativeQ
 ]


$FormatSpecies::usage = "$FormatSpecies controls the formatting of Species. If True, the ouputs of Species are formatted."

Once[ $FormatSpecies = True; ]

$SuperscriptDelimiter::usage = "$SuperscriptDelimiter stores the character delimiting superscripts in SpeciesBox."

$SubscriptDelimiter::usage = "$SubscriptDelimiter gives the character delimiting subscripts in SpeciesBox."

Once[
  $SuperscriptDelimiter = ",";
  $SubscriptDelimiter = ",";
 ]

SpeciesBox::usage = "SpeciesBox[c,sub,sup] formats a tensor-like quantity."

SpeciesBox[c_, {}, {}] := c

SpeciesBox[c_, {}, sup:{__}, delimiter_String:"\[ThinSpace]"] :=
  Superscript[
    Row @ {c},
    Row @ Riffle[sup, delimiter]
   ]

SpeciesBox[c_, sub:{__}, {}] :=
  Subscript[
    Row @ {c},
    Row @ Riffle[sub, $SubscriptDelimiter]
   ]

SpeciesBox[ c_, sub:{__}, sup:{__} ] :=
  Subsuperscript[
    Row @ {c},
    Row @ Riffle[sub, $SubscriptDelimiter],
    Row @ Riffle[sup, $SuperscriptDelimiter]
   ]
(* NOTE(2020-10-14): Superscript[] instead of SuperscriptBox[], etc.
   This is for Complex Species with NonCommutative elements as index
   (see Let[Complex, ...]), but I am not sure if this is a right choice.
   So far, there seems to be no problem. *)
(* NOTE(2020-08-04): The innner-most RowBox[] have been replaced by Row[]. The
   former produces a spurious multiplication sign ("x") between subscripts
   when $SubscriptDelimiter=Nothing (or similar). *)
(* NOTE: ToBoxes have been removed; with it, TeXForm generates spurious
   \text{...} *)


LinearMap::usage = "LinearMap represents linear maps.\nLet[LinearMap, f, g, ...] defines f, g, ... to be linear maps."

LinearMapFirst::usage = "LinearMapFirst represents functions that are linear for the first argument.\nLet[LinearMapFirst, f, g, ...] defines f, g, ... to be linear maps for their first argument."

Let[LinearMap, {ls__Symbol}] := Scan[setLinearMap, {ls}]

setLinearMap[op_Symbol] := (
  op[a___, b1_ + b2_, c___] := op[a, b1, c] + op[a, b2, c];
  op[a___, z_?ComplexQ, b___] := z op[a, b];
  op[a___, z_?ComplexQ b_, c___] := z op[a, b, c];
 )


Let[LinearMapFirst, {ls__Symbol}] := Scan[setLinearMapFirst, {ls}]

setLinearMapFirst[op_Symbol] := (
  op[z_?ComplexQ] := z;
  op[z_?ComplexQ, b__] := z op[b];
  op[z_?ComplexQ b_, c___] := z op[b, c]; (* NOTE: b_, not b__ ! *)
  op[b1_ + b2_, c___] := op[b1, c] + op[b2, c];
 )


Peel::usage = "Peel[op] removes any conjugation (such as Dagger and Conjugate) from op."

SetAttributes[Peel, Listable]

Peel[ a_ ] := a

Peel[ HoldPattern @ Tee[a_] ] := a

Peel[ Dagger[a_] ] := a

Peel[ Conjugate[a_] ] := a


Tee::usage = "Tee[expr] or equivalanetly Tee[expr] represents the Algebraic transpose of the expression expr. It is distinguished from the native Transpose[] as it respects symbols.\nSee also Transpose, TeeTranspose, Conjugate, Dagger, Topple."

SetAttributes[Tee, {Listable, ReadProtected}]

HoldPattern @ Tee[ Tee[a_] ] := a

HoldPattern @ Tee[ z_?CommutativeQ ] := z

HoldPattern @ Tee[ a_?HermitianQ ] := Conjugate[a];

HoldPattern @ Tee[ z_?CommutativeQ a_ ] := z Tee[a]

HoldPattern @ Tee[ expr_Plus ] := Total @ Tee[ List @@ expr ]

HoldPattern @ Tee[ expr_Times ] := Times @@ Tee[ List @@ expr ]

HoldPattern @ Tee[ expr_Dot ] := Dot @@ Reverse @ Tee[ List @@ expr ]

HoldPattern @ Tee[ expr_Multiply ] := Multiply @@ Reverse @ Tee[ List @@ expr ]

Tee /: HoldPattern[ Power[a_, Tee] ] := Tee[a]

Format[ HoldPattern @ Tee[ c_Symbol?SpeciesQ[j___] ] ] := 
  DisplayForm @ SpeciesBox[c, {j}, {"T"} ] /; $FormatSpecies

Format[ HoldPattern @ Tee[ c_Symbol?SpeciesQ ] ] := 
  DisplayForm @ SpeciesBox[c, {}, {"T"} ] /; $FormatSpecies


Primed::usage = "Primed[a] represents another object closely related to a."

DoublePrimed::usage = "DoublePrimed[a] represents another object closely related to a."

SetAttributes[{Primed, DoublePrimed}, Listable]

Format[ Primed[a_] ] := Superscript[a,"\[Prime]"]

Format[ DoublePrimed[a_] ] := Superscript[a,"\[DoublePrime]"]


TeeTranspose::usage = "TeeTranspose[expr] = Tee[Transpose[expr]]. It is similar to the native function Transpose, but operates Tee on every element in the matrix.\nSee also Transpose[], and Topple[]."

TeeTranspose[v_?VectorQ] := Tee[v]

TeeTranspose[m_?TensorQ, spec___] := Tee @ Transpose[m, spec]

TeeTranspose[a_] := Tee[a]


(* Relations among conjugations *)

(* Conjugate[ Dagger[x_] ] := Tee[x] *)
(* NOTE: ruins Bosons and Fermions *)

(* Conjugate[ HoldPattern @ Tee[x_] ] := Dagger[x] *)

(* Dagger[ Conjugate[x_] ] := Tee[x] *)

(* Dagger[ HoldPattern @ Tee[x_] ] := Conjugate[x] *)

(* HoldPattern @ Tee[ Dagger[x_] ] := Conjugate[x] *)

(* HoldPattern @ Tee[ Conjugate[x_] ] := Dagger[x] *)


DaggerTranspose::usage = "DaggerTranspose is an alias to Topple."

Topple::usage = "Topple \[Congruent] Dagger @* Transpose; i.e., applies Transpose and then Dagger.\nNot to be confused with Dagger or ConjugateTranspose.\nIt is similar to ConjugateTranspose, but applies Dagger instead of Conjugate. Therefore it acts also on a tensor of operators (not just numbers)."

Topple[v_?VectorQ] := Dagger[v]

Topple[m_?TensorQ, spec___] := Dagger @ Transpose[m, spec]

Topple[a_] := Dagger[a]


HermitianConjugate::usage = "HermitianConjugate is an alias to Dagger."

Dagger::usage = "Dagger[expr] returns the Hermitian conjugate the expression expr.\nWARNING: Dagger has the attribute Listable, meaning that the common expectation Dagger[m] == Tranpose[Conjugate[m]] for a matrix m of c-numbers does NOT hold any longer. For such purposes use Topple[] instead.\nSee also Conjugate[], Topple[], and TeeTranspose[]."

SetAttributes[Dagger, {Listable, ReadProtected}]
(* Enabling Dagger[...] Listable makes many things much simpler. One notable
   drawback is that it is not applicable to matrices. This is why a separate
   function Topple[m] has been defined for matrix or vector m. *)

Dagger[ Dagger[a_] ] := a

Dagger[ z_?CommutativeQ ] := Conjugate[z]

HoldPattern @ Dagger[ Conjugate[z_?CommutativeQ] ] := z

HoldPattern @ Dagger[ expr_Plus ] := Total @ Dagger[ List @@ expr ]

HoldPattern @ Dagger[ expr_Times ] := Times @@ Dagger[ List @@ expr ]

HoldPattern @ Dagger[ expr_Dot ] := Dot @@ Reverse @ Dagger[ List @@ expr ]

HoldPattern @ Dagger[ expr_Multiply ] :=
  Multiply @@ Reverse @ Dagger[ List @@ expr ]

(* Conjugation of exponential terms *)
HoldPattern @ Dagger[ Power[E, expr_] ] := MultiplyExp[ Dagger[expr] ]

(* Dagger threads over Rule *)
HoldPattern @ Dagger[ Rule[a_, b_] ] := Rule[Dagger[a], Dagger[b]]

(* Allows op^Dagger as a equivalent to Dagger[op] *)
Dagger /:
HoldPattern[ Power[expr_, Dagger] ] := Dagger[expr]

Dagger /:
HoldPattern[ Power[op_Dagger, n_Integer] ] := MultiplyPower[op, n]


Format[ HoldPattern @ Dagger[ c_Symbol?SpeciesQ[j___] ] ] :=
  DisplayForm @ SpeciesBox[c, {j}, {"\[Dagger]"} ] /; $FormatSpecies

Format[ HoldPattern @ Dagger[ c_Symbol?SpeciesQ ] ] :=
  DisplayForm @ SpeciesBox[c, {}, {"\[Dagger]"} ] /; $FormatSpecies

Format[ HoldPattern @ Dagger[a_] ] := Superscript[a, "\[Dagger]"]
(* for the undefined *)


PlusDagger::usage = "PlusDagger[expr] returns expr + Dagger[expr]."

TimesDaggerRight::usage = "TimesDaggerRight[expr] returns expr**Dagger[expr]."

TimesDaggerLeft::usage = "TimesDaggerLeft[expr] returns Dagger[expr]**expr."

PlusDagger[expr_] := expr + Dagger[expr]

TimesDaggerRight[expr_] := Multiply[expr, Dagger @@ expr]

TimesDaggerLeft[expr_]  := Multiply[Dagger @@ expr, expr]


(* A quick support for Mathematica v12.2 *)
$tempMessage = If[ NameQ["System`Hermitian"],
  Hermitian::usage <> "\n",
  ""
 ]

Hermitian::usage = $tempMessage <> "Hermitian represents Hermitian operators (Q3`Cauchy`Hermitian).\nLet[Hermitian, a, b, ...] declares a, b, ... as Hermitian operators.\nSee \!\(\*TemplateBox[{\"Q3`Cauchy`Hermitian\", \"paclet:Q3/ref/Hermitian\"}, \"RefLink\", BaseStyle->\"InlineFunctionSans\"]\) for more details."

Let[Hermitian, {ls__Symbol}] := (
  Let[NonCommutative, {ls}];
  Scan[setHermitian, {ls}];
 )

setHermitian[a_Symbol] := (
  HermitianQ[a] ^= True;
  HermitianQ[a[___]] ^= True;
  
  Dagger[a] ^= a;
  Dagger[a[j___]] ^:= a[j];
 )

HermitianQ[ HoldPattern @ Tee[a_?HermitianQ] ] = True;

HermitianQ[ Conjugate[a_?HermitianQ] ] = True;


(* A quick support for Mathematica v12.2 *)
$tempMessage = If[ NameQ["System`Antihermitian"],
  Antihermitian::usage <> "\n",
  ""
 ]

Antihermitian::usage = $tempMessage <> "Antihermitian represents Antihermitian operators (Q3`Cauchy`Antihermitian).\nLet[Antihermitian, a, b, ...] declares a, b, ... as Antihermitian operators.\nSee \!\(\*TemplateBox[{\"Q3`Cauchy`Antihermitian\", \"paclet:Q3/ref/Antihermitian\"}, \"RefLink\", BaseStyle->\"InlineFunctionSans\"]\) for more details."

Let[Antihermitian, {ls__Symbol}] := (
  Let[NonCommutative, {ls}];
  Scan[setAntihermitian, {ls}];
 )

setAntihermitian[a_Symbol] := (
  AntihermitianQ[a] ^= True;
  AntihermitianQ[a[___]] ^= True;
  
  Dagger[a] ^= -a;
  Dagger[a[j___]] ^:= -a[j];
 )

AntihermitianQ[ HoldPattern @ Tee[a_?AntihermitianQ] ] = True;

AntihermitianQ[ Conjugate[a_?AntihermitianQ] ] = True;


(*** Commutation and Anticommutation Relations ***)

Commutator::usage = "Commutator[a,b] = Multiply[a,b] - Multiply[b,a].\nCommutator[a, b, n] = [a, [a, ... [a, b]]],
this is order-n nested commutator."

Anticommutator::usage = "Anticommutator[a,b] = Multiply[a,b] + Multiply[b,a].\nAnticommutator[a, b, n] = {a, {a, ... {a, b}}}, this is order-n nested anti-commutator."

SetAttributes[{Commutator, Anticommutator}, {Listable, ReadProtected}]

Commutator[a_, b_] := Garner[ Multiply[a, b] - Multiply[b, a] ]

Commutator[a_, b_, 0] := b

Commutator[a_, b_, 1] := Commutator[a, b]

Commutator[a_, b_, n_Integer] := 
  Commutator[a, Commutator[a, b, n-1] ] /; n > 1


Anticommutator[a_, b_] := Garner[ Multiply[a, b] + Multiply[b, a] ]

Anticommutator[a_, b_, 0] := b

Anticommutator[a_, b_, 1] :=  Anticommutator[a, b]

Anticommutator[a_, b_, n_Integer] := 
  Anticommutator[a, Anticommutator[a, b, n-1] ] /; n > 1


CoefficientTensor::usage = "CoefficientTensor[expr, opList1, opList2, ...] returns the tensor of coefficients of Multiply[opList1[i], opList2[j], ...] in expr. Note that when calculating the coefficients, lower-order terms are ignored.\nCoefficientTensor[expr, list1, list2, ..., func] returns the tensor of coefficients of func[list1[i], list2[j], ...]."

CoefficientTensor[expr_List, ops:{__?AnySpeciesQ} ..] :=
  Map[ CoefficientTensor[#,ops]&, expr ]

CoefficientTensor[expr_, ops:{__?AnySpeciesQ}] := Coefficient[expr, ops]

CoefficientTensor[expr_, ops:{__?AnySpeciesQ}..] := 
  CoefficientTensor[expr, ops, Multiply]

CoefficientTensor[expr_, ops:{__?AnySpeciesQ}.., func_Symbol] :=  Module[
  { k = Length @ {ops},
    mn = Length /@ {ops},
    pp, qq, rr, cc, ij,
    G },
  pp = G @@@ Tuples @ {ops};
  qq = GroupBy[pp, Sort];
  rr = Cases[expr, x:Blank[func] :> Sort[G @@ x], {0, Infinity}];
  (* NOTE: The 0th level should be included. *)

  rr = Intersection[rr, Keys @ qq];

  If[ rr == {}, Return[SparseArray[{}, mn]] ];
  
  qq = Catenate @ KeyTake[qq, rr];
  pp = ArrayReshape[pp, mn];
  ij = Map[FirstPosition[pp, #] &, qq];
  
  pp = func @@@ qq;
  rr = Cases[#, HoldPattern[func][Repeated[_, {k}]], {0, Infinity}] & /@ pp;
  rr = Flatten @ rr;
  cc = Coefficient @@@ Transpose @ {pp, rr};
  cc = PseudoDivide[qq, cc];
  
  rr = Normal @ Merge[Thread[rr -> cc], Mean];
  rr = Coefficient[expr /. rr, qq];

  SparseArray[Thread[ij -> rr], mn]
 ]

(* Times[...] is special *)
CoefficientTensor[expr_, ops:{__?AnySpeciesQ}.., Times] := Module[
  { pp = Times @@@ Tuples @ {ops},
    cc, mm },
  cc = pp /. Counts[pp];
  mm = Coefficient[expr, pp] / cc;
  ArrayReshape[mm, Length /@ {ops}]
 ]


MultiplyPower::usage = "MultiplyPower[expr, i] raises an expression to the i-th
power using the non-commutative multiplication Multiply."

MultiplyPower::negativePower = "Negative power detected: (``)^(``)";

SetAttributes[MultiplyPower, {Listable, ReadProtected}];

(* Recursive calculation, it makes better use of Mathematica's result caching
   capabilities! *)

MultiplyPower[op_, 0] = 1

MultiplyPower[op_, 1] := op

MultiplyPower[op_, n_Integer] := Multiply[MultiplyPower[op, n-1], op] /; n > 1

MultiplyPower[op_, n_?Negative] := (
  Message[MultiplyPower::negativePower, op, n];
  Null
 )

MultiplyDot::usage = "MultiplyDot[a, b, ...] returns the products of vectors, matrices, and tensors of Species.\nMultiplyDot is a non-commutative equivalent to the native Dot with Times replaced with Multiply"

(* Makes MultiplyDot associative for the case
   MultiplyDot[vector, matrix, matrix, ...] *)
SetAttributes[ MultiplyDot, { Flat, OneIdentity, ReadProtected } ]

MultiplyDot[a:(_List|_SparseArray), b:(_List|_SparseArray)] :=
  Inner[Multiply, a, b]
(* TODO: Special algorithm is required for SparseArray *)


$GarnerHeads::usage = "$GarnerHeads gives the list of Heads to be considered in Garner."

$GarnerTests::usage = "$GarnerTests gives the list of Pattern Tests to be considered in Garner."

Once[ $GarnerHeads = {Multiply}; ]

Once[ $GarnerTests = {}; ]

Garner::usage = "Garner[expr] collects together terms involving the same Species objects (operators, Kets, Bras, etc.)."

SetAttributes[Garner, Listable]

Garner[expr_] := Module[
  { bb = Blank /@ $GarnerHeads,
    tt = PatternTest[_, #]& /@ $GarnerTests,
    qq },
  bb = Union @ Cases[expr, Alternatives @@ bb, Infinity];
  qq = expr /. {_Multiply -> 0};
  qq = Union @ Cases[qq, Alternatives @@ tt, Infinity];
  Collect[expr, Join[qq, bb], Simplify]
 ]


Elaborate::usage = "Elaborate[expr] transforms expr into a more explicit form."

Elaborate[expr_] := With[
  { pttn = Alternatives @@ Blank /@ $ElaborationHeads },
  Garner[ expr /. { v:pttn :> Elaborate[v] } //. $ElaborationRules ]
 ] /; Not @ MemberQ[$ElaborationHeads, Head[expr]]

$ElaborationHeads::usage = "$ElaborationHeads is a list of heads to be directly used in Elaborate."

$ElaborationRules::usage = "$ElaborationRules is a list of replacement rules to be used by Elaborate."

Once[
  $ElaborationHeads = {};
  
  $ElaborationRules = {
    Abs[z_] :> Sqrt[z Conjugate[z]]
   }
]


(* ****************************************************************** *)
(*     <Multiply>                                                     *)
(* ****************************************************************** *)

DistributableQ::usage = "DistributableQ[x, y, ...] returns True if any of the arguments x, y, ... has head of Plus."

DistributableQ[args__] := Not @ MissingQ @ FirstCase[ {args}, _Plus ]


Multiply::usage = "Multiply[a, b, ...] represents non-commutative multiplication of a, b, etc. Unlike the native NonCommutativeMultiply[...], it does not have the attributes Flat and OneIdentity."

SetAttributes[Multiply, {Listable, ReadProtected}]

Format[ HoldPattern @ Multiply[a__] ] :=
  DisplayForm @ RowBox @ List @ RowBox[ DisplayForm /@ MakeBoxes /@ {a} ]
(* NOTE 1: The outer RowBox is to avoid spurious parentheses around the Multiply
   expression. For example, without it, -2 Dagger[f]**f is formated as
   -2(f^\dag f). For more details on spurious parentheses, see
   https://goo.gl/MfCwMF
   NOTE 2 (Version 12.1.1): The inner DisplayForm is to avoid the spurious
   multiplication ("x") sign for non-Species symbols. *)

NonCommutativeMultiply[a___] := Multiply[a]
(* NOTE: This definition is different from the following:
   a_ ** b_ := Multiply[a, b]
   Still one can now use '**' for Multiply. *)

Multiply[] = 1 (* See also Times[]. *)

Multiply[ c_ ] := c

(* Associativity *)

HoldPattern @ Multiply[a___, Multiply[b__], c___] := Multiply[a, b, c]
(* NOTE: An alternative approach is to set the attributes Flat and
   OneIdentity. But then infinite recursion loop can easily happen. It is
   possible to avoid it, but tedious and sometimes slow. *)

(* NOTICE the following two poitns about the Flat attribute:
   1. For a Flat function f, the variables x and y in the pattern f[x_,y_] can
   correspond to any sequence of arguments.
   2. The Flat attribute must be assigned before defining any values for a
   Flat function.
   See also the discussions on the forum
   https://goo.gl/fv4uTJ
   https://goo.gl/bkjy3U *)


(* Linearity *)

(* Let[LinearMap, Multiply] *)
(* NOTE: This can easily hit the recursion limit, hence the same effect is
   implemented differently. *)

HoldPattern @ Multiply[ args__ ] := Garner @ Block[
  { F },
  Distribute[ F[args] ] /. { F -> Multiply }
 ] /; DistributableQ[args]

HoldPattern @ Multiply[ a___, z_?CommutativeQ, b___] :=
  Garner[ z Multiply[a, b] ]

HoldPattern @ Multiply[ a___, z_?CommutativeQ b_, c___] :=
  Garner[ z Multiply[a, b, c] ]


HoldPattern @ Multiply[ pre___, Power[E, expr_], post___] :=
  Multiply[pre, MultiplyExp[expr], post]


(*** Baker-Hausdorff relations for simple cases ***)

HoldPattern @
  Multiply[ pre___, MultiplyExp[a_], MultiplyExp[b_], post___ ] :=
  Multiply[ Multiply[pre], MultiplyExp[a+b], Multiply[post] ] /;
  Garner[ Commutator[a, b] ] === 0

(*
HoldPattern @ Multiply[pre___, Power[E, a_], Power[E, b_], post___] :=
  Multiply[ Multiply[pre], MultiplyExp[a+b], Multiply[post] ] /;
  Garner[ Commutator[a, b] ] === 0
 *)

HoldPattern @
  Multiply[pre___, MultiplyExp[a_], MultiplyExp[b_], post___] :=
  Multiply[
    Multiply[pre],
    MultiplyExp[ a + b + Commutator[a, b]/2 ],
    Multiply[post]
   ] /;
  Garner[ Commutator[a, b, 2] ] === 0 /;
  Garner[ Commutator[b, a, 2] ] === 0

(*
HoldPattern @ Multiply[pre___, Power[E, a_], Power[E, b_], post___] :=
  Multiply[
    Multiply[pre],
    MultiplyExp[ a + b + Commutator[a, b]/2 ],
    Multiply[post]
   ] /;
  Garner[ Commutator[a, b, 2] ] === 0 /;
  Garner[ Commutator[b, a, 2] ] === 0
 *)

HoldPattern @
  Multiply[pre___, MultiplyExp[a_], b_?AnySpeciesQ, post___] :=
  Multiply[ Multiply[pre, b], MultiplyExp[a], Multiply[post] ] /;
  Garner[ Commutator[a, b] ] === 0
(* Exp is pushed to the right if possible *)

HoldPattern @
  Multiply[pre___, MultiplyExp[a_], b_?AnySpeciesQ, post___] :=
  With[
    { new = Multiply[post] },
    Multiply[ Multiply[pre, b], MultiplyExp[a], new] +
      Multiply[ Multiply[pre, Commutator[a, b]], MultiplyExp[a], new]
   ] /; Garner[ Commutator[a, b, 2] ] === 0
(* NOTE: Exp is pushed to the right. *)
(* NOTE: Here notice BlankSequence(__), which allows for more than one
   operators. At the same time, the PatternTest AnySpeciesQ is put in order to
   skip Exp[op]. Commutators involving Exp[op] usually takes long in vain. *)


(* General rules *)

ObscureQ::usage = "ObscureQ[op] returns True if Kind[op] === NonCommutative.\nNote that most NonCommuative Species are associated with a definite Kind."

ObscureQ[op_?AnyNonCommutativeQ] := SameQ[Kind[op], NonCommutative]

ObscureQ[_] := False

(* NOTE: Notice _?AnyNonCommutativeQ NOT _?AnySpeciesQ .
   This is to handle the case involving Ket and Bra. *)
HoldPattern @ Multiply[ops__?AnyNonCommutativeQ] := Module[
  { aa = SplitBy[{ops}, ObscureQ],
    bb },
  ( bb = Multiply @@@ aa;
    Multiply @@ bb ) /;
    Not @ AllTrue[Kind[aa], OrderedQ]
 ] /;
  Not @ AllTrue[
    DeleteCases[Kind @ SplitBy[{ops}, ObscureQ], NonCommutative, {2}],
    OrderedQ
   ] /;
  Not @ AllTrue[{ops}, ObscureQ] /;
  AnyTrue[{ops}, ObscureQ]

Once[ (* To be redefined in Fock for Fermion, Majorana, Grassmann *)
  (* NOTE: At first, __?AnySpeciesQ.
     Now __?AnyNonCommutativeQ to handle Dyad. *)
  HoldPattern @ Multiply[ops__?AnyNonCommutativeQ] := Module[
    { aa = Values @ KeySort @ GroupBy[{ops}, Kind],
      bb },
    bb = Multiply @@@ aa;
    Multiply @@ bb
   ] /;
    Not @ OrderedQ[ Kind @ {ops} ] /;
    NoneTrue[{ops}, ObscureQ]
 ]

(* ****************************************************************** *)
(*     </Multiply>                                                    *)
(* ****************************************************************** *)

MultiplyExp::usage = "MultiplyExp[expr] evaluates the Exp function of operator expression expr.\nIt has been introduced to facilitate some special rules in Exp[]."

SetAttributes[MultiplyExp, Listable]

Format[ HoldPattern @ MultiplyExp[expr_] ] := Power[E, expr]

(* Exp for Grassmann- or Clifford-like Species *)
MultiplyExp[op_] := Module[
  { z = Garner @ MultiplyPower[op, 2] },
  If[ z === 0,
    1 + op,
    FunctionExpand[ Cosh[Sqrt[z]] + op Sinh[Sqrt[z]]/Sqrt[z] ]
   ] /; CommutativeQ[z]
 ]

MultiplyExp /:
HoldPattern @ Dagger[ MultiplyExp[expr_] ] := MultiplyExp[ Dagger[expr] ]

MultiplyExp /:
HoldPattern @ Inverse[ MultiplyExp[op_] ] := MultiplyExp[-op]

MultiplyExp /:
HoldPattern @ Power[ MultiplyExp[op_], z_?CommutativeQ ] :=
  MultiplyExp[z * op]


(* ****************************************************************** *)
(*     <Lie>                                                          *)
(* ****************************************************************** *)

Lie::usage = "Lie[a, b] returns the commutator [a, b]."

Lie[a_, b_] := Commutator[a, b]


LiePower::usage = "LiePower[a, b, n] returns the nth order commutator [a, [a, ..., [a, b]...]]."

LiePower[a_, b_List, n_Integer] := Map[LiePower[a, #, n]&, b] /; n>1

LiePower[a_, b_, 0] := b

LiePower[a_, b_, 1] := Commutator[a, b]

LiePower[a_, b_, n_Integer] := Garner[
  Power[-1, n] Fold[ Commutator, b, ConstantArray[a, n] ]
 ] /; n>1


LieSeries::usage = "LieSeries[a, b, n] returns the finite series up to the nth order of Exp[a] ** b ** Exp[-a].\nLieSeries[a, b, Infinity] is equivalent to LieExp[a, b]."

LieSeries[a_, b_, Infinity] := LieExp[a, b]

LieSeries[a_, b_, n_Integer] := With[
  { aa = FoldList[Commutator, b, ConstantArray[a, n]],
    ff = Table[Power[-1, k]/(k!), {k, 0, n}] },
  Garner[ aa.ff ]
 ] /; n>=0


LieExp::usage = "LieExp[a, b] returns Exp[a] ** b ** Exp[-a]."

LieExp[a_, z_?CommutativeQ] := z

LieExp[a_, z_?CommutativeQ b_] := z LieExp[a, b]

LieExp[a_, expr_List] := Map[ LieExp[a, #]&, expr ]

LieExp[a_, expr_Plus] :=
  Garner @ Total @ LieExp[a, List @@ expr]

LieExp[a_, Exp[expr_]] := MultiplyExp @ LieExp[a, expr]

LieExp[a_, MultiplyExp[expr_]] := MultiplyExp @ LieExp[a, expr]

(* Baker-Hausdorff Lemma. *)

LieExp[a_, b_] := b /;
  Garner[ Commutator[a, b] ] == 0

LieExp[a_, b_] := b + Commutator[a, b] /;
  Garner[ Commutator[a, b, 2] ] == 0

(* Mendas-Milutinovic Lemma: The anticommutator analogues of the
   Baker-Hausdorff lemma.  See Mendas and Milutinovic (1989a) *)

LieExp[a_, b_] := Multiply[MultiplyExp[2 a], b] /;
  Garner @ Anticommutator[a, b] == 0
(* NOTE: Exp is pushed to the left. *)

LieExp[a_, b_] :=
  Multiply[ MultiplyExp[2 a], b ] -
  Multiply[ MultiplyExp[2 a], Anticommutator[a, b] ] /;
  Garner @ Anticommutator[a, b, 2] == 0 
(* NOTE: Exp is pushed to the left. *)

(* ****************************************************************** *)
(*     </Lie>                                                         *)
(* ****************************************************************** *)


MultiplyDegree::usage = "MultiplyDegree[expr] returns the highest degree of the terms in the expression expr. The degree of a term is the sum of the exponents of the Species that appear in the term. The concept is like the degree of a polynomial."

(* NOTE: For Grassmann variables, which form a graded algebra, 'grade' is
   defined. *)

SetAttributes[ MultiplyDegree, Listable ]

MultiplyDegree[ HoldPattern[ Plus[a__] ] ] := Max @ MultiplyDegree @ {a}

MultiplyDegree[ HoldPattern[ Times[a__] ] ] := Total @ MultiplyDegree @ {a}

MultiplyDegree[ HoldPattern[ Multiply[a__] ] ] := Total @ MultiplyDegree @ {a}

MultiplyDegree[ _?CommutativeQ ] = 0

MultiplyDegree[ MultiplyExp[expr_] ] := Infinity /; MultiplyDegree[expr] > 0

MultiplyDegree[ expr_ ] := 0 /; FreeQ[expr, _?AnySpeciesQ]

MultiplyExpand::usage = "MultiplyExpand[expr] expands expr according to certain rules. Typically expr involves non-commutative multiply Multiply."

MultiplyExpand::unknown = "Unknown expand method: ``. \"Basic\" is used."

Options[MultiplyExpand] = {Method->"Basic"}

expandMethods = {"Basic", "BakerHausdorff", "BakerHausdorffPlus"}

MultiplyExpand[expr_, opts___?OptionQ] := Module[
  { method, func },
  method = Method /. {opts} /. Options[MultiplyExpand] /.
    { s_Symbol :> SymbolName[s],
      s_ :> ToString[s] };
  If[ !MemberQ[expandMethods, method],
    Message[MultiplyExpand::unknown, method];
    method = "Basic";
   ];
  func = Symbol[ Context[method] <> "doExpand" <> method];
  func[expr]
 ]

(* To be called through MultiplyExpand[expr, Method->"Basic"] *)
doExpandBasic[expr_] := expr /. {
  Power[E, op_] :> MultiplyExp[op]
 }
(* TODO *)

(* To be called through MultiplyExpand[expr, Method->"BakerHausdorff"] *)
doExpandBakerHausdorff[expr_] := expr
(* TODO *)


ReplaceBy::usage = "ReplaceBy[old \[RightArrow] new, M] construct a list of Rules to be used in ReplaceAll by applying the linear transformation associated with the matrix M on new. That is, the Rules old$i \[RightArrow] \[CapitalSigma]$j M$ij new$j. If new is a higher dimensional tensor, the transform acts on its first index.\nReplaceBy[expr, old \[RightArrow] new] applies ReplaceAll on expr with the resulting Rules."

ReplaceBy[old_List -> new_List, M_?MatrixQ] :=
  Thread[ Flatten @ old -> Flatten[M . new] ]

ReplaceBy[a:Rule[_List, _List], b:Rule[_List, _List].., M_?MatrixQ] :=
  ReplaceBy[ Transpose /@ Thread[{a, b}, Rule], M ]

ReplaceBy[expr_, rr:Rule[_List, _List].., M_?MatrixQ] :=
  Garner[ expr /. ReplaceBy[rr, M] ]


ReplaceByFourier::usage = "ReplaceByFourier[v] is formally equivalent to Fourier[v] but v can be a list of non-numeric symbols. If v is a higher dimensional tensor the transform is on the last index.\nReplaceByFourier[old \[RightArrow] new] returns a list of Rules that make the discrete Fourier transform.\nReplaceByFourier[expr, old \[RightArrow] new] applies the discrete Fourier transformation on expr, which is expressed originally in the operators in the list old, to the expression in terms of operators in the list new."

ReplaceByFourier[vv_List, opts___?OptionQ] :=
  vv . FourierMatrix[Last @ Dimensions @ vv, opts]

ReplaceByFourier[old_List -> new_List, opts___?OptionQ] :=
  Thread[ Flatten @ old -> Flatten @ ReplaceByFourier[new, opts] ]

ReplaceByFourier[a:Rule[_List, _List], b:Rule[_List, _List]..,
  opts___?OptionQ] :=
  ReplaceByFourier @ Thread[{a, b}, Rule]

ReplaceByFourier[expr_, rr:Rule[_List, _List].., opts___?OptionQ1] :=
  Garner[ expr /. ReplaceByFourier[rr, opts] ]


ReplaceByInverseFourier::usage = "ReplaceByInverseFourier[old -> new] \[Congruent] Fourier[old -> new, -1].\nReplaceByInverseFourier[expr, old -> new] \[Congruent] Fourier[expr, old -> new, -1]"

ReplaceByInverseFourier[args__, opts___?OptionQ] :=
  ReplaceByFourier[args, opts, FourierParameters -> {0,-1}]


Protect[ Evaluate @ $symb ]

End[]

(* Section 2. Motifications to some built-in functions *)
Begin["`Prelude`"]

$symb = Unprotect[
  KroneckerDelta, DiscreteDelta, UnitStep
 ]

(* KroneckerDelta[] & UnitStep[] *)

SetAttributes[{KroneckerDelta, UnitStep}, NumericFunction]

KroneckerDelta /:
HoldPattern[ Power[KroneckerDelta[x__],_?Positive] ] :=
  KroneckerDelta[x]

DiscreteDelta /:
HoldPattern[ Power[DiscreteDelta[x__],_?Positive] ] :=
  DiscreteDelta[x]

Format[ KroneckerDelta[x__List], StandardForm ] :=
  Times @@ Thread[KroneckerDelta[x]]

Format[ KroneckerDelta[x__List], TraditionalForm ] :=
  Times @@ Thread[KroneckerDelta[x]]
(* Also for TeXForm[ ] *)

Format[ KroneckerDelta[x__], StandardForm ] := Style[
  Subscript["\[Delta]", x],
  ScriptSizeMultipliers -> 1, 
  ScriptBaselineShifts -> {1,1}
 ]
(* TranditionalForm is already defined in the above way. *)

Format[ DiscreteDelta[j__] ] :=
  KroneckerDelta[ {j}, ConstantArray[0, Length @ {j}] ]

Format[ UnitStep[x_], StandardForm ] := Row[{"\[Theta]", "(", x, ")"}]

SetAttributes[{DiscreteDelta, UnitStep}, {ReadProtected}]


Protect[ Evaluate @ $symb ]

End[]


Q3`Abel`Private`$symb = Protect[Evaluate[$Context<>"*"]]

SetAttributes[Evaluate[Q3`Abel`Private`$symb], {ReadProtected}]

Q3`Abel`Private`$symb = Unprotect[Evaluate[$Context<>"$*"]]

ClearAttributes[Evaluate[Q3`Abel`Private`$symb], ReadProtected]

SetAttributes[$ElaborationRules, ReadProtected]
(* $ElaborationRules is too messay to show the value. *)

EndPackage[]
