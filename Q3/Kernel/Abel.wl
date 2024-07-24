(* -*- mode:math -*- *)
BeginPackage["Q3`"]

$::usage = "$ is a flavor index referring to the species itself."

{ Let };

{ Species, SpeciesQ, AnySpeciesQ };

{ Agents, AgentQ, AnyAgentQ };

{ Dimension, LogicalValues };

{ Any, Base, Flavors, FlavorMost, FlavorLast,
  FlavorNone, FlavorNoneQ, FlavorMute, FlavorThread };

{ CoefficientTensor };

{ Spin, Spins, SpinQ, SpinNumberQ };
{ Qubit, Qubits, QubitQ };
{ Qudit, Qudits, QuditQ };
{ Boson, Bosons, BosonQ, AnyBosonQ };
{ Heisenberg, Heisenbergs, HeisenbergQ, AnyHeisenbergQ };
{ Fermion, Fermions, FermionQ, AnyFermionQ };
{ Majorana, Majoranas, MajoranaQ };
(* NOTE: Fermion and the like are here for Matrix. *)

{ QuantumCircuit };

{ KetRegulate };

{ Dyad };

{ SpeciesBox,
  $FormatSpecies,
  $SubscriptDelimiter, $SuperscriptDelimiter };

{ NonCommutative, NonCommutativeSpecies, NonCommutativeQ,
  CommutativeQ, AnticommutativeQ,
  System`Hermitian, HermitianQ,
  System`Antihermitian, AntihermitianQ };

{ Dagger, System`HermitianConjugate = Dagger,
  Topple, DaggerTranspose = Topple,
  Tee, TeeTranspose,
  Peel };

{ PlusDagger, TimesDaggerRight, TimesDaggerLeft };

{ PlusTopple };

{ TransformBy, TransformByFourier, TransformByInverseFourier };

{ Basis, Matrix, MatrixIn, TheMatrix };

{ Observation, ObservationValue, Indefinite };
{ Occupation, OccupationValue };

{ JordanWignerTransform };

{ Garner, FullGarner, AddGarnerPatterns, $GarnerPatterns };

{ Elaborate, AddElaborationPatterns, $ElaborationPatterns };

{ Commutator, Anticommutator };

{ Multiply, MultiplyGenus, MultiplyKind, MultiplyDegree,
  MultiplyExp, MultiplyPower, MultiplyDot };

{ DistributableQ };

{ Matrix, ExpressionFor };

{ Lie, LiePower, LieSeries, LieExp, LieBasis };

{ Ket, Bra, State, ProductState };

{ Operator };

{ Pfaffian };

{ PauliGroup, FullPauliGroup,
  PauliGroupElements, FullPauliGroupElements,
  PauliQ, PauliMatrixQ };

{ CliffordGroup, FullCliffordGroup,
  CliffordGroupElements, FullCliffordGroupElements,
  CliffordQ, CliffordMatrixQ };

(**** <compatibiliy> ****)

(* Now comes as a built-in function with v13.1, but with an additional
   Transpose compared to the old one.
   Kept here for backward compatibility. *)
{ PermutationMatrix };

(* Now an experimental built-in symbol since v13.1.
   Kept here for backward compatibility. *)
{ BlockDiagonalMatrix };

(**** </compatibiliy> ****)


Begin["`Private`"]

$symb = Unprotect[
  NonCommutativeMultiply, 
  Conjugate, Inverse,
  KroneckerDelta, DiscreteDelta, UnitStep
]


Base::usage = "Base[c[j,\[Ellipsis],s]] returns the generator c[j,\[Ellipsis]] with the Flavor indices sans the final if c is a Species and the final Flavor index is special at all; otherwise just c[j,\[Ellipsis],s]."

SetAttributes[Base, Listable]

Base[z_] := z


Flavors::usage = "Flavors[c[j]] returns the list of Flavor indices {j} of the generator c[j]."

Flavors::bad = "Invalid Flavor index `` for the operator `` with Spin `` and Vacuum ``. Regarded as Spin 0."

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


(**** <FlavorNone> ****)

FlavorNone::usage = "FlavorNone[S[i, j, \[Ellipsis]]] for some Species S gives S[i, j, \[Ellipsis], $]. Notable examples are Qubit in Quisso package and Spin in Wigner package. Note that FlavorNone is Listable."
  
SetAttributes[FlavorNone, Listable]

FlavorNone[a_] := a (* Does nothing unless specified explicitly *)

FlavorNone[S_?SpeciesQ -> v_] := FlavorNone[S] -> v

FlavorNone[ss:{__?SpeciesQ} -> vv:{__}] := FlavorNone[ss] -> vv


FlavorNoneQ::usage = "FlavorNoneQ[{s$1,s$2,\[Ellipsis]}] returns True if the flavor index ends properly with None for every species s$j. Note that for some species, the flavor index is not required to end with None."

SyntaxInformation[FlavorNoneQ] = {"ArgumentsPattern" -> {_}}

FlavorNoneQ[a_, b__] := (
  CheckArguments[FlavorNoneQ[a, b], 1];
  FlavorNoneQ @ {a, b}
 )

FlavorNoneQ[s_?SpeciesQ] := FlavorNone[s] === s

FlavorNoneQ[ss_List] := AllTrue[Flatten @ ss, FlavorNoneQ]

FlavorNoneQ[_] = True

(**** </FlavorNone> ****)


FlavorMute::usage = "FlavorMute[S[i, j, \[Ellipsis], k]] for some Species S gives S[i, j, \[Ellipsis], $], i.e., with the last Flavor replaced with None. Notable examples are Qubit in Quisso package and Spin in Wigner package. Note that FlavorMute is Listable."
  
SetAttributes[FlavorMute, Listable]

FlavorMute[a_] := a (* Does nothing unless specified explicitly *)


(**** <FlavorThread> ****)

FlavorThread::usage = "FlavorThread[{s1, s2, \[Ellipsis]}, m] returns {s1[m], s2[m], \[Ellipsis]}.\nFlavorThread[{s1, s2, \[Ellipsis]}, {m1, m2, \[Ellipsis]}] returns {s1[m1], s2[m2], s3[m3]}.\nFlavorThread[{s1, s2, \[Ellipsis]}, {list1, list2, \[Ellipsis]}] maps over the lists."

FlavorThread[ss:{__?SpeciesQ}][any_] := FlavorThread[ss, any]

FlavorThread[ss:{__?SpeciesQ}, flv_?AtomQ] :=
  Through @ Construct[ss, flv]

FlavorThread[ss:{__?SpeciesQ}, flv:{__List}] :=
  Map[FlavorThread[ss], flv] /;
  ArrayQ[flv]

FlavorThread[ss:{__?SpeciesQ}, flv:{__}] :=
  MapThread[Construct, {ss, flv}]

(**** </FlavorThread> ****)


Any::usage = "Any represents a dummy Flavor index."

SetAttributes[Any, ReadProtected]

Format[Any] = "\[SpaceIndicator]"


MultiplyKind::usage = "MultiplyKind[op] returns the type of op, which may be a Species or related function.\nMultiplyKind is the lowest category class of Species and functions for Multiply. It affects how Multiply rearranges the non-commutative elements.\nIt is intended for internal use.\nSee also MultiplyGenus."

SetAttributes[MultiplyKind, Listable]

(* NOTE: HoldPattern is necessary here to prevent $IterationLimit::itlim error
   when the package is loaded again. *)

HoldPattern @ MultiplyKind[ Inverse[x_] ] := MultiplyKind[x]

HoldPattern @ MultiplyKind[ Conjugate[x_] ] := MultiplyKind[x]

HoldPattern @ MultiplyKind[ Dagger[x_] ] := MultiplyKind[x]

HoldPattern @ MultiplyKind[ Tee[x_] ] := MultiplyKind[x]


Dimension::usage = "Dimension[A] gives the Hilbert space dimension associated with the system A."

SetAttributes[Dimension, Listable]


LogicalValues::usage = "LogicalValues[spc] gives the list of logical values labeling the logical basis states of the system spc."

SetAttributes[LogicalValues, Listable]


(***** <Let> ****)

Let::usage = "Let[Symbol, a, b, \[Ellipsis]] defines the symbols a, b, \[Ellipsis] to be Symbol, which can be Species, Complex, Real, Integer, etc."

Let::unknown = "Unknown species ``."

SetAttributes[Let, {HoldAll, ReadProtected}]

SyntaxInformation[Let] = {
  "ArgumentsPattern" -> {_, __}
 }

Let[name_Symbol, ls__Symbol, opts___?OptionQ] := Let[name, {ls}, opts]

Let[name_Symbol, ___] := (Message[Let::unknown, name]; $Failed)

(***** </Let> ****)


(**** <Species> ****)

Species::usage = "Species represents a tensor-like quantity, which is regarded as a multi-dimensional regular array of numbers.\nLet[Species, a, b, \[Ellipsis]] declares the symbols a, b, \[Ellipsis] to be Species.\nIn the Wolfram Language, a tensor is represented by a multi-dimenional regular List. A tensor declared by Let[Species, \[Ellipsis]] does not take a specific structure, but only regarded seemingly so."

Let[Species, ss:{__Symbol}] := (
  Clear[ss]; (* NOTE: This must come before Scan. *)
  Scan[setSpecies, ss]
)

setSpecies[x_Symbol] := (
  ClearAttributes[x, Attributes[x]];
  (* NOTE: One could replace the above line and Clear with single ClearAll,
     but then Let[...] cannot be used for local variables such as in Block. *)
  (* NOTE: The messages and defaults associated with x are not affected. *)
  
  SetAttributes[x, {NHoldAll, ReadProtected}];

  SpeciesQ[x] ^= True;
  SpeciesQ[x[___]] ^= True;

  MultiplyKind[x] ^= Species;
  MultiplyKind[x[___]] ^= Species;
  
  Dimension[x] ^= 1;
  Dimension[x[___]] ^= 1;

  LogicalValues[x] ^= {0};
  LogicalValues[x[___]] ^= {0};

  x[i___, None] = x[i, $];
  x[i___, Null] = x[i, $];
  x[i___][j___] = x[i, j];
  x[i___, $, j__] = x[i, j];
  (* In particular, x[j,$,$] = x[j,$]. *)

  x[k__] := x @@ ReplaceAll[{k}, s_?SpeciesQ :> ToString[s, InputForm]] /;
    AnyTrue[{k}, SpeciesQ];
  (* NOTE: If a Flavor index itself is a species, many tests fail to work
     properly. A common example is CommutativeQ. To prevent nasty errors, such
     Flavor indices are converted to String. *)

  x[k___] := Flatten @ ReleaseHold @ Distribute[Hold[x][k], List] /; 
    AnyTrue[{k}, MatchQ[_List]];
  (* NOTE: Flavor indices in {k} cannot have Hold or HoldForm; for the, use the Inactive-Activate pair, instead. Hold-ReleaseHold pair is faster than Inactive-Activate pair. *)
  (* NOTE: Flatten is required for c[{1,2,...}, All] for spinful boson or
     fermion c and for S[{1,2,...}, All] for qubit S, etc. *)
  (* NOTE: Distribute[x[j], List] will hit the recursion limit. *)

  Format @ x[k___] := Interpretation[SpeciesBox[x, {k}, {}], x[k]];
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

(**** </Species> ****)


(**** <Agents> ****)

Agents::usage = "Agents[expr] returns the list of all Agents appearing in EXPR."

Agents[expr_] := Select[
  Union @ FlavorMute @ Cases[{expr}, _?SpeciesQ, Infinity],
  AgentQ
 ] /; FreeQ[expr, _Association|_Dyad]

Agents[expr_] :=
  Agents @ Normal[expr /. Dyad -> Hold[Dyad]]
(* NOTE: This recursion is necessary since Association inside Association is
   not expanded by a single Normal. *)


AgentQ::usage = "AgentQ[a] returns True if a is an Agent.\nAngents include Qubit, Qudit, Fermioin, Boson, Heisenberg, and Spin."

AgentQ[_] = False


AnyAgentQ::usaage = "AnyAgentQ[z] returns True if z itself is an Agent or a modified form Conjugate[x], Dagger[x], or Tee[x] of another Agent x."

AnyAgentQ[ _?AgentQ ] = True

AnyAgentQ[ Inverse[_?AgentQ] ] = True

AnyAgentQ[ Conjugate[_?AgentQ] ] = True

AnyAgentQ[ Dagger[_?AgentQ] ] = True

AnyAgentQ[ Tee[_?AgentQ] ] = True

AnyAgentQ[ _ ] = False

(**** </Agents> ****)


(**** <NonCommutative> ****)

NonCommutative::usage = "NonCommutative represents a non-commutative element.\nLet[NonCommutative, a, b, \[Ellipsis]] declares a[\[Ellipsis]], b[\[Ellipsis]], \[Ellipsis] to be NonCommutative."

Let[NonCommutative, {ls__Symbol}] := (
  Let[Species, {ls}];
  Scan[setNonCommutative, {ls}]
 )

setNonCommutative[x_Symbol] := (
  NonCommutativeQ[x] ^= True;
  NonCommutativeQ[x[___]] ^= True;

  MultiplyKind[x] ^= NonCommutative;
  MultiplyKind[x[___]] ^= NonCommutative;
  MultiplyGenus[x] ^= "Singleton";
  MultiplyGenus[x[___]] ^= "Singleton";
)


Format @ Inverse[op_?NonCommutativeQ] :=
  Interpretation[SpeciesBox[op, { }, {"-1"}], Inverse @ op]
 
Format @ Inverse[op_Symbol?NonCommutativeQ[j___]] :=
  Interpretation[SpeciesBox[op, {j}, {"-1"}], Inverse @ op[j]]

Inverse @ Inverse[op_?NonCommutativeQ] := op

Inverse @ Power[E, expr_] :=
  MultiplyExp[-expr] /; Not[CommutativeQ @ expr]
(* NOTE: Recall that Not[CommutativeQ[expr]] is not the same as
   NonCommutativeQ[expr]. *)


NonCommutativeQ::usage = "NonCommutativeQ[op] or NonCommutativeQ[op[\[Ellipsis]]] returns True if op or op[\[Ellipsis]] is a non-commutative element."

SetAttributes[NonCommutativeQ, Listable]

(* NOTE: HoldPattern is required here to prevent infinite recursion when the
   package is loaded again. *)

HoldPattern @ NonCommutativeQ[ Inverse[_?NonCommutativeQ] ] = True

HoldPattern @ NonCommutativeQ[ Conjugate[_?NonCommutativeQ] ] = True

HoldPattern @ NonCommutativeQ[ Dagger[_?NonCommutativeQ] ] = True

HoldPattern @ NonCommutativeQ[ Tee[_?NonCommutativeQ] ] = True

NonCommutativeQ[_] = False


CommutativeQ::usage = "CommutativeQ[expr] returns True if the expression expr is free of any non-commutative element.\nCommutativeQ[expr] is equivalent to FreeQ[expr, _?NonCommutativeQ]."

SetAttributes[CommutativeQ, Listable]

CommutativeQ[z_] := FreeQ[z, _?NonCommutativeQ]


AnticommutativeQ::usage = "AnticommutativeQ[c] returns True if c is an anticommutative Species such as Fermion, Majorana, and Grassmann, and False otherwise.\nIt is a low-level function intended to be used in Multiply and Matrix.\nIt affects how Multiply and Matrix manipulate expressions involving Fermion, Majorana, and Grassmann Species, which brings about a factor of -1 when exchanged."

SetAttributes[AnticommutativeQ, Listable]


NonCommutativeSpecies::usage = "NonCommutativeSpecies[expr] returns the list of all NonCommutative Species appearing in EXPR."

NonCommutativeSpecies[expr_] := Select[
  Union @ FlavorMute @ Cases[List @ expr, _?SpeciesQ, Infinity],
  NonCommutativeQ
 ] /; FreeQ[expr, _Association|_Dyad]

NonCommutativeSpecies[expr_] :=
  NonCommutativeSpecies @ Normal[expr /. Dyad -> Hold[Dyad]]
(* NOTE: This recursion is necessary since Association inside Association is
   not expanded by a single Normal. *)

(**** </NonCommutative> ****)


(**** <SpeciesBox> ****)

$FormatSpecies::usage = "$FormatSpecies controls the formatting of Species. If True, the ouputs of Species are formatted."

$FormatSpecies = True;

$SuperscriptDelimiter::usage = "$SuperscriptDelimiter stores the character delimiting superscripts in SpeciesBox."

$SubscriptDelimiter::usage = "$SubscriptDelimiter gives the character delimiting subscripts in SpeciesBox."

$SuperscriptDelimiter = ",";
$SubscriptDelimiter = ",";

SpeciesBox::usage = "SpeciesBox[c,sub,sup] formats a tensor-like quantity."

(* SpeciesBox[c_?AtomQ] = c *)

SpeciesBox[c_Symbol] = c

SpeciesBox[c_Symbol?SpeciesQ[a___]] = c[a]

SpeciesBox[c_Symbol[a___]] := DisplayForm @ RowBox @ {"(", c[a], ")"}

SpeciesBox[c_?Negative] := DisplayForm @ RowBox @ {"(", c, ")"}

SpeciesBox[c_?AtomQ] = c


SpeciesBox[c_, {}, {}] := c

SpeciesBox[c_, {}, sup:{__}, delimiter_String:"\[ThinSpace]"] :=
  Superscript[SpeciesBox @ c, Row[sup, delimiter]]

SpeciesBox[c_, sub:{__}, {}] :=
  Subscript[SpeciesBox @ c, Row[FlavorForm @ sub, $SubscriptDelimiter]]

SpeciesBox[c_, sub:{__}, sup:{__}] :=
  Subsuperscript[
    SpeciesBox @ c,
    Row[FlavorForm @ sub, $SubscriptDelimiter],
    Row[sup, $SuperscriptDelimiter]
  ]
(* NOTE(2020-10-14): Superscript[] instead of SuperscriptBox[], etc.
   This is for Complex Species with NonCommutative elements as index
   (see Let[Complex, \[Ellipsis]]), but I am not sure if this is a right choice.
   So far, there seems to be no problem. *)
(* NOTE(2020-08-04): The innner-most RowBox[] have been replaced by Row[]. The
   former produces a spurious multiplication sign ("x") between subscripts
   when $SubscriptDelimiter=Nothing (or similar). *)
(* NOTE: ToBoxes have been removed; with it, TeXForm generates spurious
   \text{\[Ellipsis]} *)

(**** </SpeciesBox> ****)


FlavorForm::usage = "FlavorForm[j] converts the flavor index j into a more intuitively appealing form."

SetAttributes[FlavorForm, Listable]

FlavorForm[Up] := "\[UpArrow]"

FlavorForm[Down] := "\[DownArrow]"

FlavorForm[j_] := j


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

HoldPattern @ Tee[ expr_Plus ] := Tee /@ expr

HoldPattern @ Tee[ expr_Times ] := Tee /@ expr

HoldPattern @ Tee[ expr_Dot ] := Dot @@ Reverse @ Tee[List @@ expr]

HoldPattern @ Tee[ expr_Multiply ] := Multiply @@ Reverse @ Tee[List @@ expr]

Tee /: HoldPattern[ Power[a_, Tee] ] := Tee[a]

Format @ HoldPattern @ Tee[ c_Symbol?SpeciesQ[j___] ] := 
  Interpretation[SpeciesBox[c, {j}, {"T"}], Tee @ c[j]]

Format @ HoldPattern @ Tee[ c_Symbol?SpeciesQ ] := 
  Interpretation[SpeciesBox[c, {}, {"T"}], Tee @ c]


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


DaggerTranspose::usage = "DaggerTranspose is an alias for Topple."

Topple::usage = "Topple \[Congruent] Dagger @* Transpose; i.e., applies Transpose and then Dagger.\nNot to be confused with Dagger or ConjugateTranspose.\nIt is similar to ConjugateTranspose, but applies Dagger instead of Conjugate. Therefore it acts also on a tensor of operators (not just numbers)."

Topple[v_?VectorQ] := Dagger[v]

Topple[m_?TensorQ, spec___] := Dagger @ Transpose[m, spec]

Topple[a_] := Dagger[a]


HermitianConjugate::usage = "HermitianConjugate is an alias for Dagger."

Dagger::usage = "Dagger[expr] returns the Hermitian conjugate the expression expr.\nWARNING: Dagger has the attribute Listable, meaning that the common expectation Dagger[m] == Tranpose[Conjugate[m]] for a matrix m of c-numbers does NOT hold any longer. For such purposes use Topple[] instead.\nSee also Conjugate[], Topple[], and TeeTranspose[]."

SetAttributes[Dagger, {Listable, ReadProtected}]
(* Enabling Dagger[\[Ellipsis]] Listable makes many things much simpler. One
   notable drawback is that it is not applicable to matrices. This is why a
   separate function Topple[m] has been defined for matrix or vector m. *)

Dagger[ Dagger[a_] ] := a

Dagger[ z_?CommutativeQ ] := Conjugate[z]

HoldPattern @ Dagger[ Conjugate[z_?CommutativeQ] ] := z

HoldPattern @ Dagger[ expr_Plus ] := Dagger /@ expr

HoldPattern @ Dagger[ expr_Times ] := Dagger /@ expr

HoldPattern @ Dagger[ expr_Dot ] :=
  Dot @@ Reverse @ Dagger[ List @@ expr ]

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


Format @ HoldPattern @ Dagger[ c_Symbol?SpeciesQ[j___] ] :=
  Interpretation[SpeciesBox[c, {j}, {"\[Dagger]"}], Dagger @ c[j]]

Format @ HoldPattern @ Dagger[ c_Symbol?SpeciesQ ] :=
  Interpretation[SpeciesBox[c, {}, {"\[Dagger]"}], Dagger @ c]

Format @ HoldPattern @ Dagger[a_] :=
  Interpretation[Superscript[a, "\[Dagger]"], Dagger @ a]
(* for the undefined *)


PlusDagger::usage = "PlusDagger[expr] returns expr + Dagger[expr]."

TimesDaggerRight::usage = "TimesDaggerRight[expr] returns expr**Dagger[expr]."

TimesDaggerLeft::usage = "TimesDaggerLeft[expr] returns Dagger[expr]**expr."

PlusDagger[expr_] := expr + Dagger[expr]

TimesDaggerRight[expr_] := Multiply[expr, Dagger @ expr]

TimesDaggerLeft[expr_]  := Multiply[Dagger @ expr, expr]


PlusTopple::usage = "PlusTopple[expr] returns mat + Topple[mat]."

PlusTopple[mat_] := mat + Topple[mat]


System`Hermitian::usage = "In Q3, Hermitian represents Hermitian operators.\nLet[Hermitian, a, b, \[Ellipsis]] declares a, b, \[Ellipsis] as Hermitian operators.\nSince Mathematica v12.1, Hermitian is a built-in symbol, and is extended in Q3.\nSee \!\(\*TemplateBox[{\"Q3/ref/Hermitian\", \"paclet:Q3/ref/Hermitian\"}, \"RefLink\", BaseStyle->\"InlineFunctionSans\"]\) for more details."
(* NOTE: Since Mathematica 12.2, System`Hermitian is a built-in symbol. *)

Let[System`Hermitian, {ls__Symbol}] := (
  Let[NonCommutative, {ls}];
  Scan[setHermitian, {ls}];
 )

setHermitian[a_Symbol] := (
  HermitianQ[a] ^= True;
  HermitianQ[a[___]] ^= True;
  
  Dagger[a] ^= a;
  Dagger[a[j___]] ^:= a[j];
 )

HermitianQ::usage = "HermitianQ[s] returns True if species s represents an Hermitian operator and False otherwise."

HermitianQ[ HoldPattern @ Tee[a_?HermitianQ] ] = True;

HermitianQ[ Conjugate[a_?HermitianQ] ] = True;


System`Antihermitian::usage = "In Q3, Antihermitian represents Antihermitian operators.\nLet[Antihermitian, a, b, \[Ellipsis]] declares a, b, \[Ellipsis] as Antihermitian operators.\nSee \!\(\*TemplateBox[{\"Q3/ref/Antihermitian\", \"paclet:Q3/ref/Antihermitian\"}, \"RefLink\", BaseStyle->\"InlineFunctionSans\"]\) for more details."

(* NOTE: Since Mathematica 12.2, System`Antihermitian is a built-in symbol. *)

Let[System`Antihermitian, {ls__Symbol}] := (
  Let[NonCommutative, {ls}];
  Scan[setAntihermitian, {ls}];
 )

setAntihermitian[a_Symbol] := (
  AntihermitianQ[a] ^= True;
  AntihermitianQ[a[___]] ^= True;
  
  Dagger[a] ^= -a;
  Dagger[a[j___]] ^:= -a[j];
 )

AntihermitianQ::usage = "AntihermitianQ[s] returns True if species s represents an anti-Hermitian operator and False otehrwise."

AntihermitianQ[ HoldPattern @ Tee[a_?AntihermitianQ] ] = True;

AntihermitianQ[ Conjugate[a_?AntihermitianQ] ] = True;


(*** Commutation and Anticommutation Relations ***)

Commutator::usage = "Commutator[a,b] = Multiply[a,b] - Multiply[b,a].\nCommutator[a, b, n] = [a, [a, \[Ellipsis] [a, b]]],
this is order-n nested commutator."

Anticommutator::usage = "Anticommutator[a,b] = Multiply[a,b] + Multiply[b,a].\nAnticommutator[a, b, n] = {a, {a, \[Ellipsis] {a, b}}}, this is order-n nested anti-commutator."

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


(**** <CoefficientTensor> ****)

CoefficientTensor::usage = "CoefficientTensor[expr, opList1, opList2, \[Ellipsis]] returns the tensor of coefficients of Multiply[opList1[i], opList2[j], \[Ellipsis]] in expr. Note that when calculating the coefficients, lower-order terms are ignored.\nCoefficientTensor[expr, list1, list2, \[Ellipsis], func] returns the tensor of coefficients of func[list1[i], list2[j], \[Ellipsis]]."

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

(* Times[\[Ellipsis]] is special *)
CoefficientTensor[expr_, ops:{__?AnySpeciesQ}.., Times] := Module[
  { pp = Times @@@ Tuples @ {ops},
    cc, mm },
  cc = pp /. Counts[pp];
  mm = Coefficient[expr, pp] / cc;
  ArrayReshape[mm, Length /@ {ops}]
]

(**** <CoefficientTensor> ****)


(**** <MultiplyPower> ****)

MultiplyPower::usage = "MultiplyPower[expr, i] raises an expression to the i-th
power using the non-commutative multiplication Multiply."

SetAttributes[MultiplyPower, {Listable, ReadProtected}];

(* Put these definitions earlier than the general rule. *)

MultiplyPower[Sqrt[op_], n_Integer?EvenQ] := MultiplyPower[op, n / 2]

MultiplyPower[S_Symbol?QubitQ[j___, C[n_Integer]], M_Integer] := With[
  { m = Log[2, M] },
  S[j, C[n-m]] /; IntegerQ[m]
]


(* general rule *)

MultiplyPower[op_, 0] = 1

MultiplyPower[op_, 1] = op

MultiplyPower[op_, n_Integer] := 
  Multiply[MultiplyPower[op, n-1], op] /; n > 1
(* NOTE 1: Recursive calculation makes better use of Mathematica's caching
   capabilities! *)
(* NOTE 2: For n > 1, this shadows a similar definition in Pauli because of the additional condition n > 1. *)

(* Put this definition at the last. *)
MultiplyPower[z_?CommutativeQ, n_] := Power[z, n]

(**** </MultiplyPower> ****)


MultiplyDot::usage = "MultiplyDot[a, b, \[Ellipsis]] returns the products of vectors, matrices, and tensors of Species.\nMultiplyDot is a non-commutative equivalent to the native Dot with Times replaced with Multiply"

(* Makes MultiplyDot associative for the case
   MultiplyDot[vector, matrix, matrix, \[Ellipsis]] *)
SetAttributes[MultiplyDot, {Flat, OneIdentity, ReadProtected}]

MultiplyDot[a_?ArrayQ, b_?ArrayQ] := Inner[Multiply, a, b]
(* TODO: Special algorithm is required for SparseArray *)


(**** <Garner> ****)

FullGarner::usage = "FullGarner[expr] collects together terms involving the same species objects (operators, Kets, Bras, etc.) and simplifies the coefficients by using FullSimplify."

SetAttributes[FullGarner, Listable]

FullGarner[expr_] := Garner[expr, FullSimplify]


Garner::usage = "Garner[expr] collects together terms involving the same species objects (operators, Kets, Bras, etc.) and simplifies the coefficients by using Simplify.\nGarner[expr, function] uses function instead of Simplify."

SetAttributes[Garner, Listable]

Garner[expr_, post_:Simplify] := Module[
  { new, var, pat },
  new = KetRegulate @ Expand[expr, Except[_ControlledGate|_QuantumCircuit]];
  pat = Flatten[Alternatives @@ $GarnerPatterns];
  var = theGarner[ new /. {op:$GarnerPatterns["Heads"] -> Hold[op]} ];
  var = Union @ Cases[ReleaseHold @ var, pat];
  Collect[new, var, post]
]
(* NOTE: Cases[{expr}, ..., Infinity] may pick up spurious variables. *)


theGarner::usage = "Breaks into elementary parts."

theGarner[expr_Plus] := Flatten @ Map[theGarner, List @@ expr]

theGarner[expr_Times] := List @@ expr

theGarner[any_] := {any}


AddGarnerPatterns::usage = "AddGarnerPatterns[pattern$1,pattern$2,\[Ellipsis]] adds patterns to be handled by Garner."

AddGarnerPatterns[spec:(_Blank|_PatternTest)..] := Module[
  { heads = Cases[{spec}, _Blank],
    tests = Cases[{spec}, _PatternTest] },
  $GarnerPatterns["Heads"] =
    Union[$GarnerPatterns["Heads"], Alternatives @@ heads];
  $GarnerPatterns["Tests"] =
    Union[$GarnerPatterns["Tests"], Alternatives @@ tests];
  $GarnerPatterns
]


$GarnerPatterns::usage = "$GarnerPatterns gives the list of patterns to be handled by Garner."

$GarnerPatterns = Association[
  "Heads" -> Alternatives[],
  "Tests" -> Alternatives[]
]

(**** </Garner> ****)


(**** <Elaborate> ****)

Elaborate::usage = "Elaborate[expr] transforms expr into a more explicit form."

Elaborate[expr_] := Module[
  { pttn = $ElaborationPatterns["Heads"],
    mint },
  mint = expr /. { v:pttn :> Elaborate[v] };
  Garner[ mint //. $ElaborationPatterns["Rules"] ]
] /; Not @ MemberQ[Identity @@@ $ElaborationPatterns["Heads"], Head[expr]]


AddElaborationPatterns::usage = "AddElaborationPatterns[spec$1,spec$2,\[Ellipsis]] adds patterns to be handled by Elaborate.\nThe spec$j may be _head or replacement rules."

AddElaborationPatterns[spec:(_Blank|_Rule|_RuleDelayed)..] := Module[
  { heads = Cases[{spec}, _Blank],
    rules = Cases[{spec}, _Rule|_RuleDelayed] },
  $ElaborationPatterns["Heads"] =
    Union[$ElaborationPatterns["Heads"], Alternatives @@ heads];
  $ElaborationPatterns["Rules"] =
    Union[$ElaborationPatterns["Rules"], rules];
  $ElaborationPatterns
]


$ElaborationPatterns::usage = "$ElaborationPatterns gives the list of patterns or replacement rules to be handled by Elaborate."

$ElaborationPatterns = Association[
  "Heads" -> Alternatives[],
  "Rules" -> {}
]

(**** </Elaborate> ****)


(**** <MultiplyGenus> ****)

MultiplyGenus::usage = "MultiplyGenus[op] returns the Genus of op, which may be a Species or related function.\nMultiplyGenus is a category class of Species and functions for Multiply that ranks above MultiplyKind. It affects how Multiply rearranges the non-commutative elements.\nMultiplyGenus is intended for internal use."

SetAttributes[MultiplyGenus, Listable]

(* NOTE: HoldPattern is necessary here to prevent $IterationLimit::itlim error
   when the package is loaded again. *)

HoldPattern @ MultiplyGenus[ Inverse[x_?SpeciesQ] ] = "Singleton"

HoldPattern @ MultiplyGenus[ Conjugate[x_?SpeciesQ] ] = "Singleton"

HoldPattern @ MultiplyGenus[ Tee[x_?SpeciesQ] ] = "Singleton"


HoldPattern @ MultiplyGenus[ Dagger[x_?SpeciesQ] ] = "Singleton"

HoldPattern @ MultiplyGenus[ Dagger[any_] ] := "Bra" /;
  MultiplyGenus[any] == "Ket"
  
HoldPattern @ MultiplyGenus[ Dagger[any_] ] := "Ket" /;
  MultiplyGenus[any] == "Bra"

(**** </MultiplyGenus> ****)


(**** <DistributableQ> ****)

DistributableQ::usage = "DistributableQ[{expr1, expr2, \[Ellipsis]}] returns True if any of the expressions expr1, expr2, \[Ellipsis] has Head Plus."

DistributableQ[ops_List] := Not @ MissingQ @ FirstCase[ops, _Plus]

(**** </DistributableQ> ****)


(**** <Multiply> ****)

Multiply::usage = "Multiply[a, b, \[Ellipsis]] represents non-commutative multiplication of a, b, etc. Unlike the native NonCommutativeMultiply[\[Ellipsis]], it does not have the attributes Flat and OneIdentity."

SetAttributes[Multiply, {Listable, ReadProtected}]

AddGarnerPatterns[_Multiply]


Format @ HoldPattern @ Multiply[a__] := Interpretation[
  Row @ List @ Row[{a}, "\[VeryThinSpace]"],
  Multiply[a]
 ]
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

Multiply[c_] = c


(* Associativity *)

HoldPattern @
  Multiply[pre___, Multiply[op__], post___] := Multiply[pre, op, post]
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

HoldPattern @ Multiply[args__] := Garner[
  ReleaseHold @ Distribute[ Hold[Multiply][args] ]
] /; DistributableQ[{args}]
(*  NOTE: If some operators in {args} such as Observation (previous version) themselves involve Hold or HoldForm, ReleaseHold disturb these operators. However, I keep this method because this is faaster than, e.g., the Inactive-Activate pair method or manual wrapper method. *)

(*
HoldPattern @ Multiply[args__] := Garner[
  Activate @ Distribute[ Inactive[Multiply][args] ]
] /; DistributableQ[{args}]
 *)
(*  NOTE: This method is slower than the Hold and RealseHold pair mehtod. *)

HoldPattern @ Multiply[pre___, z_?CommutativeQ, post___] :=
  Garner[ z * Multiply[pre, post] ];

HoldPattern @ Multiply[pre___, z_?CommutativeQ op_, post___] :=
  Garner[ z * Multiply[pre, op, post] ]

HoldPattern @ Multiply[pre___, Power[E, op_], post___] :=
  Multiply[pre, MultiplyExp[op], post]


(* General rules *)

(* No operator is moved across Ket or Bra. *)
(* Operators of different kinds (see MultiplyKind) are regarded either mutually
   commutative or mutually anticommuative. *)
(* Unless specified explicitly, any symbol or function is regarded commutative
   (i.e., commutes with any other symbol or function). *)

HoldPattern @ Multiply[ops__?NonCommutativeQ] := Module[
  { aa = SplitBy[{ops}, MultiplyGenus],
    bb },
  bb = Multiply @@@ aa;
  Multiply @@ bb
] /;
  Not @ KindsOrderedQ @ {ops} /;
  Length[Union @ MultiplyGenus @ {ops}] > 1

HoldPattern @ Multiply[ops__?NonCommutativeQ] := Module[
  { aa = Values @ KeySort @ GroupBy[{ops}, MultiplyKind],
    bb },
  bb = Multiply @@@ aa;
  bb = Multiply @@ bb;
  bb * SignatureTo[
    Cases[ {ops}, _?AnticommutativeQ ],
    Cases[ Flatten @ aa, _?AnticommutativeQ ]
  ]  
] /; Not @ KindsOrderedQ @ {ops}


KindsOrderedQ::usage = "KindsOrderedQ[list] returns True if all iterms in list are ordered within each section, where items are split into sections by MultiplyGenus."

KindsOrderedQ[ops_List] := Module[
  { qq = MultiplyKind @ SplitBy[ops, MultiplyGenus] },
  AllTrue[qq, OrderedQ]
]

(**** </Multiply> ****)


(**** <MultiplyExp> ****)

MultiplyExp::usage = "MultiplyExp[expr] evaluates the Exp function of operator expression expr.\nIt has been introduced to facilitate some special rules in Exp[]."

SetAttributes[MultiplyExp, Listable]

AddElaborationPatterns[_MultiplyExp];

AddElaborationPatterns[
  Exp[a_] :> MultiplyExp[a] /; Not[FreeQ[a, _?NonCommutativeQ]]
]


Format @ HoldPattern @ MultiplyExp[expr_] :=
  Interpretation[Power[E, expr], MultiplyExp @ expr]


MultiplyExp[] = 1

MultiplyExp[0] = 1


MultiplyExp /:
HoldPattern @ Dagger[ MultiplyExp[expr_] ] := MultiplyExp[ Dagger[expr] ]

MultiplyExp /:
HoldPattern @ Inverse[ MultiplyExp[op_] ] := MultiplyExp[-op]

MultiplyExp /:
HoldPattern @ Power[ MultiplyExp[op_], z_?CommutativeQ ] :=
  MultiplyExp[z * op]

MultiplyExp /:
MultiplyPower[ MultiplyExp[op_], z_?CommutativeQ ] :=
  MultiplyExp[z * op]

MultiplyExp /:
Multiply[pre___, MultiplyExp[op_], MultiplyExp[op_], post___] :=
  Multiply[pre, MultiplyExp[2 * op], post]


MultiplyExp /:
HoldPattern @ Matrix[ MultiplyExp[op_], rest___ ] := 
  MatrixExp @ Matrix[op, rest]


MultiplyExp /:
HoldPattern @ Elaborate[ MultiplyExp[expr_] ] :=
  Elaborate @ ExpressionFor @ MatrixExp @ Matrix @ expr /;
  Agents[expr] == {} /;
  Not @ FreeQ[expr, _Pauli]

MultiplyExp /:
HoldPattern @ Elaborate[ MultiplyExp[expr_] ] := Module[
  { ss = Agents[expr],
    mm },
  mm = Matrix[expr, ss];
  Elaborate @ ExpressionFor[MatrixExp[mm], ss] /;
    ContainsOnly[MultiplyKind @ ss, {Qubit, Qudit, Spin}]
]
(* NOTE: In principle, it can handle fermions as well. But fermions have been
   excluded here because the method of converting first to matrix and back to
   operator expression is slow for fermions due to the requirement of the
   Jordan-Wigner transformation. MultiplyExp usually appears in the
   Baker-Hausdorff form, and the latter can be treated more efficiently using
   LieExp or related methods. *)

(**** </MultiplyExp> ****)


(**** <Baker-Hausdorff Lemma: Simple Cases> ****)

HoldPattern @
  Multiply[ pre___, MultiplyExp[a_], MultiplyExp[b_], post___ ] :=
    Multiply[ Multiply[pre], MultiplyExp[a+b], Multiply[post] ] /;
      Garner[ Commutator[a, b] ] === 0

HoldPattern @
  Multiply[pre___, MultiplyExp[a_], MultiplyExp[b_], post___] :=
    Multiply[
      Multiply[pre],
      MultiplyExp[ a + b + Commutator[a, b]/2 ],
      Multiply[post]
    ] /;
      Garner[ Commutator[a, b, 2] ] === 0 /;
      Garner[ Commutator[b, a, 2] ] === 0

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
(* NOTE: Here, notice the PatternTest AnySpeciesQ is put in order to skip
   Exp[op] or MultiplyExp[op]. Commutators involving Exp[op] or
   MultiplyExp[op] usually takes long in vain. *)

(**** </Baker-Hausdorff Lemma: Simple Cases> ****)


(**** <Lie> ****)

Lie::usage = "Lie[a, b] returns the commutator [a, b]."

Lie[a_, b_] := Commutator[a, b]


LiePower::usage = "LiePower[a, b, n] returns the nth order commutator [a, [a, \[Ellipsis], [a, b]\[Ellipsis]]]."

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

LieExp[a_, expr_List] := Map[LieExp[a, #]&, expr]

LieExp[a_, expr_Plus] := Garner @ Map[LieExp[a, #]&, expr]

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

(**** </Lie> ****)


(**** <LieBasis> ****)

LieBasis::usage = "LieBasis[n] returns a basis of the vector space \[ScriptCapitalM](n) of n\[Times]n matrices; equivalently, the standard generating set of Lie algebra u(n).\nThe basis is orthonormal with respect to the Hilbert-Schmidt product, and all but one elements are traceless."

LieBasis[op_?SpeciesQ] := LieBasis @ {op}

LieBasis[qq:{__?SpeciesQ}] := Module[
  { lbs = LieBasis[Times @@ Dimension[qq]] },
  ExpressionFor[#, qq]& /@ lbs
 ]


LieBasis[n_Integer?Positive] := Module[
  { bs },
  bs = Catenate @ Table[{j, k}, {k, 1, n}, {j, 1, k}];
  Catenate[theLieGenerators[n] /@ bs]
 ]

theLieGenerators[n_Integer][{1, 1}] :=
  { SparseArray @ IdentityMatrix[n] / Sqrt[n] }

theLieGenerators[n_Integer][{k_Integer, k_Integer}] :=
  List @ SparseArray @ DiagonalMatrix @
  PadRight[Append[Table[1, k-1], 1-k]/Sqrt[k*(k-1)], n]

theLieGenerators[n_Integer][{j_Integer, k_Integer}] := {
  SparseArray[{{j, k} ->  1, {k, j} -> 1}, {n, n}] / Sqrt[2],
  SparseArray[{{j, k} -> -I, {k, j} -> I}, {n, n}] / Sqrt[2]
 } /; j < k

(**** </LieBasis> ****)


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


(**** <TransformBy> ****)

TransformBy::usage = "TransformBy[old \[RightArrow] new, mat] construct a list of Rules to be used in ReplaceAll by applying the linear transformation associated with matrix mat on new. That is, the Rules old$i \[RightArrow] \[CapitalSigma]$j mat$ij new$j. If new is a higher dimensional tensor, the transform acts on its first index.\nTransformBy[expr, old \[RightArrow] new] applies ReplaceAll on expr with the resulting Rules."

TransformBy[old_List -> new_List, mat_?MatrixQ] :=
  Thread[ Flatten @ old -> Flatten[mat . new] ]

TransformBy[a:Rule[_List, _List], bb:Rule[_List, _List].., mat_?MatrixQ] :=
  TransformBy[ Transpose /@ Thread[{a, bb}, Rule], mat ]

TransformBy[expr_, rr:Rule[_List, _List].., M_?MatrixQ] :=
  Garner[ expr /. TransformBy[rr, M] ]

(**** </TransformBy> ****)


(**** <TransformByFourier> ****)

TransformByFourier::usage = "TransformByFourier[v] is formally equivalent to Fourier[v] but v can be a list of non-numeric symbols. If v is a higher dimensional tensor the transform is on the last index.\nTransformByFourier[old \[RightArrow] new] returns a list of Rules that make the discrete Fourier transform.\nTransformByFourier[expr, old \[RightArrow] new] applies the discrete Fourier transformation on expr, which is expressed originally in the operators in the list old, to the expression in terms of operators in the list new."

TransformByFourier[vv_List, opts___?OptionQ] :=
  vv . FourierMatrix[Last @ Dimensions @ vv, opts]

TransformByFourier[old_List -> new_List, opts___?OptionQ] :=
  Thread[ Flatten @ old -> Flatten @ TransformByFourier[new, opts] ]

TransformByFourier[a:Rule[_List, _List], b:Rule[_List, _List]..,
  opts___?OptionQ] :=
  TransformByFourier @ Thread[{a, b}, Rule]

TransformByFourier[expr_, rr:Rule[_List, _List].., opts___?OptionQ1] :=
  Garner[ expr /. TransformByFourier[rr, opts] ]


TransformByInverseFourier::usage = "TransformByInverseFourier[old -> new] \[Congruent] Fourier[old -> new, -1].\nTransformByInverseFourier[expr, old -> new] \[Congruent] Fourier[expr, old -> new, -1]"

TransformByInverseFourier[args__, opts___?OptionQ] :=
  TransformByFourier[args, opts, FourierParameters -> {0,-1}]

(**** </TransformByFourier> ****)


(**** <Observation> ****)

Observation::usage = "Observation[spec] represents an operator that has the spectrum specified by spec."

(* Observation /: Peel[ Observation[a_] ] := a *)
(* for Matrix[] *)

(* Observation /: MultiplyKind[ Observation[a_] ] := MultiplyKind[a] *)
(* for Multiply[] *)

(* Observation /: MultiplyGenus[ Observation[_] ] := "Singleton" *)
(* for Multiply *)

(* Observation /: AnySpeciesQ[ Observation[a_] ] := AnySpeciesQ[a] *)
(* for Multiply[] *)

Observation /:
NonCommutativeQ[ Observation[spec_] ] := Positive @ Length @
  Cases[{spec}, _Symbol?SpeciesQ[___] | _Symbol?SpeciesQ, Infinity]

Observation /:
Dagger[op_Observation] := op

Observation /:
Multiply[pre___, op_Observation, v_Ket, post___] :=
  Multiply[pre, op[v], post]

Observation /:
Matrix[Observation[spec_], ss:{__?SpeciesQ}] := Module[
  { bs = Basis[ss],
    vv },
  vv = ObservationValue[spec][bs];
  SparseArray @ DiagonalMatrix[vv]
]

Observation /:
Agents[Observation[spec_]] := Select[
  Union @ FlavorNone @ Flatten @
    Cases[{spec}, _Symbol?SpeciesQ | _?SpeciesQ[___], Infinity],
  AgentQ
]
(* NOTE: Since spec may include Hold[...] or HoldForm[...], usual
   Agents would not work. *)

Observation /:
HoldPattern @ NonCommutativeSpecies[Observation[spec_]] :=
  Union @ FlavorNone @ Flatten @
  Cases[{spec}, _Symbol?SpeciesQ | _?SpeciesQ[___], Infinity]
(* NOTE: Since spec may include Hold[...] or HoldForm[...], usual
   NonCommutativeSpecies would not work. *)

Observation[spec_][vec_Ket] := ObservationValue[vec, spec] * vec

Observation[spec_][expr_Association] := Observation[spec] /@ expr

Observation[spec_][expr_List] := Observation[spec] /@ expr

Observation[spec_][expr_Plus] := Observation[spec] /@ expr

Observation[spec_][z_?CommutativeQ expr_] := z * Observation[spec][expr]


ObservationValue::usage = "ObservationValue[state, spec] returns the eigenvalue of operator Observation[spec] that state belongs to if state is an eigenstate of the operator. Otherwise, it returns Indefinite[value1, value2, \[Ellipsis]]."

ObservationValue[spec_][expr_] :=
  ObservationValue[expr, spec]

ObservationValue[expr_Association, spec_] :=
  Map[ObservationValue[#, spec]&, expr]

ObservationValue[expr_List, spec_] :=
  Map[ObservationValue[#, spec]&, expr] /;
  Not @ FreeQ[expr, _Ket]

ObservationValue[z_?CommutativeQ expr_, spec_] :=
  ObservationValue[expr, spec] /;
  Not @ FreeQ[expr, _Ket]

ObservationValue[expr_Plus, spec_] := With[
  { vv = ObservationValue[Cases[expr, _Ket, Infinity], spec] },
  If[Equal @@ vv, First @ vv, Indefinite @@ Union[vv]]
] /; Not @ FreeQ[expr, _Ket]

ObservationValue[Ket[a_Association], spec_] := Activate[
  spec /. {
    S_?SpeciesQ[j___] :> Lookup[a, S[j,$]],
    S_Symbol?SpeciesQ :> Lookup[a, S[$]]
  }
]
(* NOTE: Remember that the spec may involve Hold or HoldForm. *)


Indefinite::usage = "Indefinite[val$1,val$2,\[Ellipsis]] represents an indefinite value among the possible values {val$1,val$2,\[Ellipsis]}."

(**** </Observation> ****)


(**** <Occupation> ****)
(* It is a simple application of Observation. *)

Occupation::usage = "Occupation[{s1,s2,\[Ellipsis]},k] represents the occupation operator of species {s1,s2,\[Ellipsis]} in the computational basis state \[LeftBracketingBar]k\[RightAngleBracket].\nOccupation is a simple application of Observation."

SyntaxInformation[Occupation] = {
  "ArgumentsPattern" -> {_, _}
 }

Occupation[{}, _] = 0

Occupation[ss:{__?SpeciesQ}, k_] :=
  Occupation[FlavorNone @ ss, k] /;
  Not[FlavorNoneQ @ ss]

Occupation[ss:{__?SpeciesQ}, k_] :=
  Observation[Inactive[Count][ss, k]] /;
  And[Equal @@ MultiplyKind[ss], Equal @@ Dimension[ss]]

Occupation /:
HoldPattern @ Dagger[ op_Occupation ] := op

Occupation /:
HoldPattern @ Agents[Occupation[ss:{__?SpeciesQ}, _]] := Agents[ss]

Occupation /:
HoldPattern @ NonCommutativeSpecies[Occupation[ss:{__?SpeciesQ}, _]] :=
  NonCommutativeSpecies[ss]


OccupationValue::usage = "OccupationValue[{s1,s2,\[Ellipsis]},k] returns the occupation number of species {s1,s2,\[Ellipsis]} in the level k (logical state Ket[k]).\nOccupationValue is a simple application of ObservationValue."

OccupationValue[ss:{__?SpeciesQ}, val_][expr_] :=
  OccupationValue[expr, ss, val] /;
  And[Equal @@ MultiplyKind[ss], Equal @@ Dimension[ss]]

OccupationValue[expr_, ss:{__?SpeciesQ}, val_] :=
  ObservationValue[expr, Inactive[Count][ss, val]] /;
  And[Equal @@ MultiplyKind[ss], Equal @@ Dimension[ss]]

(**** </Occupation> ****)


(**** <KroneckerDelta> ****)
(**** <UnitStep> ****)

SetAttributes[{KroneckerDelta, UnitStep}, NumericFunction]

KroneckerDelta /:
HoldPattern[ Power[KroneckerDelta[x__], _?Positive] ] :=
  KroneckerDelta[x]

Format[ KroneckerDelta[x__List], StandardForm ] := Interpretation[
  Times @@ Thread[KroneckerDelta[x]],
  KroneckerDelta[x]
 ]

Format[ KroneckerDelta[x__List], TraditionalForm ] := Interpretation[
  Times @@ Thread[KroneckerDelta[x]],
  KroneckerDelta[x]
 ]
(* NOTE: This is also for TeXForm[ ] *)


DiscreteDelta /:
HoldPattern[ Power[DiscreteDelta[x__], _?Positive] ] :=
  DiscreteDelta[x]

(*
Format @ DiscreteDelta[j__] := Interpretation[
  KroneckerDelta[{j}, ConstantArray[0, Length @ {j}]],
  DiscreteDelta[j]
 ]
 *)

Format[ UnitStep[x_], StandardForm ] := Interpretation[
  Row @ {"\[Theta]", "(", x, ")"},
  UnitStep[x]
 ]

SetAttributes[{DiscreteDelta, UnitStep}, {ReadProtected}]

(**** </UnitStep> ****)
(**** </KroneckerDelta> ****)


Protect[ Evaluate @ $symb ]

End[]

EndPackage[]
