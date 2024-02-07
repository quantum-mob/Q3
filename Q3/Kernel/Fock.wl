(* -*- mode: math; -*- *)
BeginPackage["Q3`"]

{ Heisenberg, Boson, Fermion, Majorana };
{ Bosons, Heisenbergs, Fermions, Majoranas };
{ HeisenbergQ, BosonQ, FermionQ, MajoranaQ, ParticleQ, FockOperatorQ };
{ AnyHeisenbergQ, AnyBosonQ, AnyFermionQ, AnyParticleQ, AnyFockOperatorQ };
{ AnnihilatorQ, CreatorQ };

{ Spin, SpinZ, TrueSpin, Vacuum };

(*** Tools for operator expressions ***)

{ CanonicalConjugate = Canon };

{ NormalOrder, FockColon };

{ FockDegree, CoefficientTensor };

{ FockBilinearQ, FockBilinearSystem,
  FockBilinearOperators, FockBilinearMatrix };

{ DiracToMajorana, MajoranaToDirac,
  HeisenbergToBoson, BosonToHeisenberg };

(* Common bilinear combinations *)

{ FockNumber, Q, FockHopping, Hop, FockPairing, Pair };

{ FockSpin, FockSpinSpin, FockSpinor };

{ FockIsospin, FockIsospinor };

(*** Tools for many-particle states ***)

{ VacuumState[] = Ket[Vacuum],
  NullState[] = Ket[Null] };
{ VacuumExpectation, SurviveVacuum,
  Displacement, CoherentState, SqueezedState };

{ FockKet, FockCat, FockPad };
{ FockNorm, FockAvg };
{ BosonBasis, FermionBasis, PrintFermionBasis };
{ FockMatrix, FockMatrixForm };

{ FockDecompose, FockOrthogonalize };

{ FockAddSpin, FockAddSpinZ };


{ FockCoefficientTensor }; (* Obsolete *)

{ FockFourier, FockInverseFourier }; (* Obsolete *)


Begin["`Private`"]

$symbs = Unprotect[Missing]


FlavorNone[a_?AnyParticleQ] = a


Heisenberg::usage = "Heisenberg represents the operators obeying the canonical commutation relations.\nLet[Heisenberg, a, b, ...] or Let[Heisenberg, {a,b,...}] declares a, b, ... to be Heisenberg canonical operators. Heisenberg cannonical variables are essentially Bosonic. Indeed, a complex Weyl algebra is generated either by Bosonic creators and annihilators or by Heisenberg caonical operators."

Boson::usage = "Boson represents Bosonic annihilation operators.\nLet[Boson, a, b, ...] or Let[Boson, {a,b,...}] declares a, b, ... to be bosonic operators. They obey canonical commutation relations."

Fermion::usage = "Fermion represents Fermionic annihilation operators.\nLet[Fermion, a, b, ...] or Let[Fermion, {a,b,...}] declares a, b, ... to be Dirac fermion operators. They obey canonical anti-commutation relations."

Fermion::error = "Something wrong has happened when declaring a fermion operator ``."

Majorana::usage = "Majorana represents Majorana Fermion operators.\nLet[Majorana, a, b, ...] or Let[Majorana, {a,b,...}] declares a, b, ... to be real (Majorana) fermionic operators."

Spin::badS = "Bad spin value ``. Spin should be non-negative integer (half-integer) for bosons (fermions)."

Flavors::badSz = "Bad spin index in `` for the operator `` with Spin `` and Vacuum ``. Regarded as Spin 0."

Flavors::bad = "Invalid Flavor index `` for the operator `` with Spin `` and Vacuum ``. Regarded as Spin 0."

Vacuum::usage = "Vacuum is an option to Let[Fermion, ...]. Its value should be either \"Void\" or \"Sea\". \"Void\" (\"Sea\") declares that the vacuum state for the fermion operator is the completely empty state (Fermi sea with all levels below the Fermi level filled up). The vacuum state determines how the fermionic operators are reordered. Vacuum is alos a function: Vacuum[c] gives the vacuum state for the fermion operator c."

Vacuum::unknown = "Unknown vacuum type ``. \"Void\" is used instead."

Vacuum::flavor = "Invalid Flavor index `` for the operator `` with Spin `` and Vacuum ``. Regarded as \"Void\"."

Options[Heisenberg] = {Spin -> 0, Bottom -> 0, Top -> 5}

Options[Boson] = {Spin -> 0, Bottom -> 0, Top -> 5}

Options[Fermion] = {Spin -> 1/2, Vacuum -> "Void"}


Spin[ HoldPattern @ Dagger[c_?ParticleQ] ] := Spin[c]

Spin[_] = 0 (* by default every thing is spinless *)


Vacuum[ HoldPattern @ Dagger[c_?ParticleQ] ] := Vacuum[c]

Vacuum[_] = "Void" (* by default every thing has Void vacuum. *)


Boson /:
Let[Boson, {ls__Symbol}, opts___?OptionQ] := Module[
  { spin, bottom, top },
  { spin, bottom, top } = { Spin, Bottom, Top } /. {opts} /. Options[Boson];

  Let[NonCommutative, {ls}];
  
  If[ !And[IntegerQ[spin], NonNegative[spin]],
    Message[Spin::badS, spin];
    (* spin = 0 *)
    (* NOTE that in NON-RELATIVISTIC theory, there is no constraint between
       spin and statistics. It is useful to allow bosons to have half-integer
       spins, for example, in Schwinger boson representation of the spin. Of
       course, in such caes, the "spin" does not refer to real spins but to
       pseudo-spins. *)
   ];
  Scan[ setBoson[#, spin, bottom, top]&, {ls} ];
 ]

setBoson[x_Symbol] := setBoson[x, 0, 5]
(* By default, Spin 0 bosons. *)

setBoson[x_Symbol, spin_?SpinNumberQ, bottom_Integer, top_Integer] := (
  BosonQ[x] ^= True;
  BosonQ[x[___]] ^= True;

  AgentQ[x] ^= True;
  AgentQ[x[___]] ^= True;

  MultiplyKind[x] ^= Boson;
  MultiplyKind[x[___]] ^= Boson;
  
  Bottom[x] ^= bottom;
  Bottom[x[___]] ^= bottom;
  
  Top[x] ^= top;
  Top[x[___]] ^= top;

  Dimension[x] ^= 1 + top - bottom;
  Dimension[x[___]] ^= 1 + top - bottom;
  
  LogicalValues[x] ^= Range[bottom, top];
  LogicalValues[x[___]] ^= Range[bottom, top];

  x /: Power[x, n_Integer] := MultiplyPower[x, n];
  x /: Power[x[j___], n_Integer] := MultiplyPower[x[j], n];

  x /: Conjugate[x] := x;
  x /: Conjugate[x[j___]] := x[j];

  x[j___, $, k___] := x[j,k];
  x[] := x;

  x[j___, a_ -> b_] := Dyad[<|x[j] -> b|>, <|x[j] -> a|>];
  (* NOTE: Required for DyadForm. *)
  
  Spin[x] ^= spin;
  If[ spin == 0,
    Spin[x[___]] ^= spin;
    x[j___,All] := x[j],
    (* the last index indicates the spin component *)
    Spin[x[___,_]] ^= spin;
    (* The value of spin index s is assumed to be consistent with Spin.
       Stricter checking is complicated and may cause slow performance.
       See also spinfulQ[]. *)
    x[j___,All] := Flatten @ x[j, Range[spin,-spin,-1]];
   ];
  (* Special formatting for Spin 1/2 Boson operators. *)
  If[ spin == 1/2,
    x[j___, Up] := x[j, 1/2];
    x[j___, Down] := x[j, -1/2];
    Format @ x[j___, +1/2] := Interpretation[
      SpeciesBox[x , {j,"\[UpArrow]"}, {}],
      x[j, +1/2]
     ];
    Format @ x[j___, -1/2] := Interpretation[
      SpeciesBox[x , {j,"\[DownArrow]"}, {}],
      x[j, -1/2]
     ];
   ];
 )


Heisenberg /:
Let[Heisenberg, {ls__Symbol}, opts___?OptionQ] := Module[
  { spin, top },
  { spin, top } = {Spin, Top} /. {opts} /. Options[Heisenberg];
  
  Let[NonCommutative, {ls}];
    
  If[ !And[IntegerQ[spin], NonNegative[spin]],
    Message[Spin::badS, spin];
    (* spin = 0 *)
    (* NOTE that in NON-RELATIVISTIC theory, there is no constraint between
       spin and statistics. It is useful to allow Bosons to have half-integer
       spins, for example, in Schwinger heisenberg representation of the
       spin. Of course, in such caes, the "spin" does not refer to real spins
       but to pseudo-spins. *)
   ];
  Scan[setHeisenberg[#, spin, top]&, {ls}];
 ]

setHeisenberg[x_Symbol] := setHeisenberg[x, 0]
(* By default, Spin 0 Heisenberg. *)

setHeisenberg[x_Symbol, spin_?SpinNumberQ, top_Integer] := (
  HeisenbergQ[x] ^= True;
  HeisenbergQ[x[___]] ^= True;

  AgentQ[x] ^= True;
  AgentQ[x[___]] ^= True;

  MultiplyKind[x] ^= Heisenberg;
  MultiplyKind[x[___]] ^= Heisenberg;
  
  Top[x] ^= top;
  Top[x[___]] ^= top;

  Dimension[x] ^= 1 + top;
  Dimension[x[___]] ^= 1 + top;
  
  LogicalValues[x] ^= Range[0, top];
  LogicalValues[x[___]] ^= Range[0, top];

  Dagger[x] ^= x;
  Dagger[x[j___]] ^:= x[j];

  x[j___, $] := x[j];
  x[] := x;
  
  x /: Conjugate[x] := x;
  x /: Conjugate[x[j___]] := x[j];
    
  x /: Power[x, n_Integer] := MultiplyPower[x, n];
  x /: Power[x[j___], n_Integer] := MultiplyPower[x[j], n];

  Spin[x] ^= spin;
  If[ spin == 0,
    Spin[x[___]] ^= spin,
    (* s indicates the spin component *)
    Spin[x[___,_]] ^= spin;
    (* The value of spin index s is assumed to be consistent with Spin.
       Stricter checking is complicated and may cause slow performance.
       See also spinfulQ[]. *)
    x[j___,All] := Flatten @ x[j, Range[spin,-spin,-1]];
   ];
 )


Fermion /:
Let[Fermion, {ls__Symbol}, opts___?OptionQ] := Module[
  {spin, vac},
  {spin, vac} = {Spin, Vacuum} /. {opts} /. Options[Fermion];
  
  Let[NonCommutative, {ls}];
    
  If[ vac != "Void" && vac!= "Sea",
    Message[Vacuum::unknown, vac];
    vac = "Void"
   ];

  If[ spin != 0 && !And[OddQ[2*spin], Positive[spin]],
    Message[Spin::badS, spin];
    (* NOTE that in NON-RELATIVISTIC theory, there is no constraint between
       spin and statistics. It is useful to allow fermions to have integer
       spins, for example, in Schwinger fermion representation of the spin. Of
       course, in such caes, the "spin" does not refer to real spins but to
       pseudo-spins. *)
   ];
  
  Scan[setFermion[#, spin, vac]&, {ls}];
 ]

setFermion[x_Symbol] := setFermion[x, 1/2];
(* By default, Spin 1/2 for fermions. *)

setFermion[x_Symbol, spin_?SpinNumberQ, vac:("Void"|"Sea")] := (
  FermionQ[x] ^= True;
  FermionQ[x[___]] ^= True;

  AgentQ[x] ^= True;
  AgentQ[x[___]] ^= True;

  MultiplyKind[x] ^= Fermion;
  MultiplyKind[x[___]] ^= Fermion;
  
  Dimension[x] ^= 2;
  Dimension[x[___]] ^= 2;
  
  LogicalValues[x] ^= {0, 1};
  LogicalValues[x[___]] ^= {0, 1};

  x /: Conjugate[x] := x;
  x /: Conjugate[x[j___]] := x[j];

  x /: Power[x, n_Integer] := MultiplyPower[x, n];
  x /: Power[x[j___], n_Integer] := MultiplyPower[x[j], n];

  x[j___, $, k___] := x[j, k];
  x[] := x; (* NOTE: This affects Vacuum[f[]]. *)
  
  Spin[x] ^= spin;
  Vacuum[x] ^= vac;
  Which[
    spin == 0 && vac == "Void", (
      Spin[x[___]] ^= spin;
      Vacuum[x[___]] ^= vac;
      x[j___,All] := x[j];
     ),
    spin == 0 && vac == "Sea", (
      Spin[x[__]] ^= spin;
      Vacuum[x[__]] ^= vac;
      x[j___,All] := x[j];
     ),
    spin > 0 && vac == "Void", (
      Spin[x[__]] ^= spin;
      Vacuum[x[__]] ^= vac;
      x[j___,All] := Flatten @ x[j, Range[spin,-spin,-1]];
     ),
    spin > 0 && vac == "Sea", (
      (* the first index indicates above or below the Fermi sea *)
      (* the final index indicates the spin component *)
      Spin[x[__,_]] ^= spin;
      Vacuum[x[__,_]] ^= vac;
      x[k_,j___,All] := Flatten @ x[k, j, Range[spin,-spin,-1]];
     ),
    True, Message[Fermion::error, x]
   ];
  (* The value of spin index s is assumed to be consistent with Spin. Stricter
     checking is complicated and may cause slow performance.
     See also spinfulQ[]. *)

  (* Special formatting for Spin 1/2 fermion operators. *)
  If[ spin == 1/2,
    x[j___, Up] := x[j, 1/2];
    x[j___, Down] := x[j, -1/2];
    Format @ x[j___, +1/2] := Interpretation[
      SpeciesBox[x , {j,"\[UpArrow]"}, {}],
      x[j, +1/2]
     ];
    Format @ x[j___, -1/2] := Interpretation[
      SpeciesBox[x , {j,"\[DownArrow]"}, {}],
      x[j, -1/2]
     ];
   ];
 )

(* Override the default definition of Format[Dagger[...]] *)

Format[
  HoldPattern @ Dagger[c_Symbol?SpeciesQ[j___, Rational[1,2]]] /;
    Spin[c] == 1/2 ] := Interpretation[
      SpeciesBox[c , {j,"\[UpArrow]"}, {"\[Dagger]"}],
      Dagger @ c[j, 1/2]
     ]

Format[
  HoldPattern @ Dagger[c_Symbol?SpeciesQ[j___, Rational[-1,2]]] /;
    Spin[c] == 1/2 ] := Interpretation[
      SpeciesBox[c , {j,"\[DownArrow]"}, {"\[Dagger]"}],
      Dagger @ c[j, -1/2]
     ]


Majorana /:
Let[Majorana, {ls__Symbol}] := (
  Let[NonCommutative, {ls}];
  Scan[setMajorana, {ls}]
 )

setMajorana[x_Symbol] := (
  MultiplyKind[x] ^= Majorana;
  MultiplyKind[x[___]] ^= Majorana;
  
  MajoranaQ[x] ^= True;
  MajoranaQ[x[___]] ^= True;
  
  Dagger[x] ^= x;
  Dagger[x[j___]] ^:= x[j];
  
  x[j___, $] := x[j];
  x[] := x;
  
  x /: Conjugate[x] := x;
  x /: Conjugate[x[j___]] := x[j];

  x /: Power[x, n_Integer] := MultiplyPower[x, n];
  x /: Power[x[j___], n_Integer] := MultiplyPower[x[j], n];
 )


TrueSpin::usage = "TrueSpin[c[i,j,\[Ellipsis]]] returns Spin[c] if the Flavor indices i, j, \[Ellipsis] are consistent with Spin[c]; otherwise returns 0 with a warning message. TrueSpin[c] always returns zero, wheather with or without warning message."

HoldPattern @ 
  TrueSpin[ Dagger[c_?ParticleQ] ] := TrueSpin[c]

TrueSpin[ c_Symbol?ParticleQ ] :=
  If[ Spin[c] == 0,
    Spin[c],
    Message[Flavors::bad, {}, c, Spin[c], Vacuum[c]];
    0
   ]

TrueSpin[ op:c_Symbol?ParticleQ[j__] ] :=
  If[ Spin[op] === Spin[c],
    Spin[c],
    Message[Flavors::bad, {j}, c, Spin[c], Vacuum[c]];
    0
   ]


spinlessQ::usage = "spinlessQ[c[j,...]] returns True if the operator itself is spinless or if the Flavor indices are inconsistent although the operator itself is spinful."

spinfulQ::usage = "spinfulQ[c[j...]] returns True if the operator c has finite spin and the Flavor indices are consistent."

(* NOTE: Not[spinlessQ] != spinfulQ.  There are undetermined cases, which
   result in False for both. *)

spinlessQ[op_?AnyParticleQ] := If[TrueSpin[op] == 0, True, False, True]

spinfulQ[op_?AnyParticleQ] := TrueQ[TrueSpin[op] > 0]


seaQ::usage = "seaQ[c[i,j,...]] returns True if Vacuum[c] is \"Sea\" and the Flavor indices i, j, ... are consistent.\nNote that seaQ[c] always returns False wheather with or withour warning message."

(* For a spinless (Spin = 0) Fermion to have the Sea vacuum, at least one
   Flavor index is required for the expected answer. Otherwise, in effect the
   vacuum of the operator is regarded to be Void.
   See also: CreatorQ[], AnnihilatorQ[] *)

(* For a spinful (Spin > 0) Fermion to have the Sea vacuum, at least two
   Flavor indices are required as the last index is expected to represent the
   spin component. Otherwise, in effect the vacuum of the operators is
   regarded to be Void.
   See also: CreatorQ[], AnnihilatorQ[] *)

seaQ[ HoldPattern @ Dagger[op_?FermionQ] ] := seaQ[op]

seaQ[ c_Symbol?FermionQ ] := (
  Message[Vacuum::flavor, {}, c, Spin[c], Vacuum[c]];
  Return[False]
)
(* NOTE: For any species c, c[] is automatically converted to c. *)

seaQ[ op:c_Symbol?FermionQ[j___] ] := (
  If[ Vacuum[op] =!= Vacuum[c],
    Message[Vacuum::flavor, {j}, c, Spin[c], Vacuum[c]]
  ];
  Vacuum[op] == Vacuum[c] == "Sea"
 )

seaQ[_] = False


Missing["KeyAbsent", _?BosonQ] := 0
Missing["KeyAbsent", _?HeisenbergQ] := 0
Missing["KeyAbsent", _?FermionQ] := 0
Missing["KeyAbsent", _?MajoranaQ] := 0


FockOperatorQ::usage = "FockOperatorQ[c] returns True if c is any Fock-space operator (Boson, Fermion, Heisenberg, or Majorana) without Dagger on it.\nGrassmann is not regarded as a Fock-space operator."

AnyFockOperatorQ::usage = "AnyFockOperatorQ[c] returns True if c is any Fock-space operator (Boson, Fermion, Heisenberg, or Majorana) with or without Dagger on it."

AddGarnerPatterns[_?AnyFockOperatorQ]

ParticleQ::usage = "ParticleQ[c] returns True if c is either a Bosonic or Fermionic operator (without Dagger on it); i.e., a normal particle distinguished from a Majorana Fermion, which is both particle and atni-particle."

AnyParticleQ::usage = "AnyParticleQ[c] returns True if c is either a bosonic or fermionic operaor with or without Dagger on it."

BosonQ::usage = "BosonQ[c] returns True if c is a bosonic operator (without Dagger on it)."

AnyBosonQ::usage = "AnyBosonQ[c] returns True if c is a bosonic operaor with or without Dagger on it."

HeisenbergQ::usage = "HeisenbergQ[c] returns True if c is a Heisenberg operator (without Canon on it)."

AnyHeisenbergQ::usage = "AnyHeisenbergQ[c] returns True if c is a Heisenberg operator with or without Canon on it."

FermionQ::usage = "FermionQ[c] returns True if c is a fermionic operator. FermionQ[c[i, j, ...]] returns True if c[i, j, ...] is a fermionic operator (without Dagger on it)."

AnyFermionQ::usage = "AnyFermionQ[c] returns True if c is a fermionic operaor with or without Dagger on it."

MajoranaQ::usage = "MajoranaQ[z] returns True if z is a Majorana fermionic operator."

BosonQ[_] = False

HeisenbergQ[_] = False

FermionQ[_] = False

MajoranaQ[_] = False


AnticommutativeQ[_?AnyFermionQ | _?MajoranaQ | _?GrassmannQ] = True

AnticommutativeQ[_] = False


FockOperatorQ[ _?HeisenbergQ | _?BosonQ | _?FermionQ | _?MajoranaQ ] = True

FockOperatorQ[_] = False


ParticleQ[ _?BosonQ | _?FermionQ ] = True

ParticleQ[_] = False


(* AnyBosonQ, AnyFermionQ, etc. *)
Scan[
  With[
    { anyQ = Symbol["Any" <> ToString[#]] },
    anyQ[Canon[_?#]] = True;
    anyQ[HoldPattern @ Dagger[_?#]] = True;
    anyQ[_?#] = True;
    anyQ[_] = False;
   ] &,
  {FockOperatorQ, ParticleQ, HeisenbergQ, BosonQ, FermionQ}
 ]

AnySpeciesQ[ Canon[_?HeisenbergQ] ] = True
(* Heisenberg's canonical conjugate is not very common, and was not defined in
   the Q3 package. *)


Base[ op:c_Symbol?ParticleQ[j___,s_] ] := c[j] /; spinfulQ[op]

Base[ op_?FockOperatorQ ] := op


SpinZ::usage = "SpinZ[c[j,s]] returns the Spin Z quantum number s (i.e., the final spin index) of the operator c[j,s]."

SetAttributes[SpinZ, Listable]

SpinZ[ HoldPattern @ Dagger[c_?ParticleQ] ] := SpinZ[c]

SpinZ[ op:_Symbol?ParticleQ[___,s_] ] /; spinfulQ[op] = s 

SpinZ[ op_ ] = 0


(*** Canonical Conjugate ***)

CanonicalConjugate::usage = "CanonicalConjugate[op] or Canon[op] denotes the canonical conjugate of a Heisenberg operator op.\nSee also Heisenberg."

Canon::usage = "Canon[x] denotes the canonical conjugate of a Heisenberg canonical operator x.\nSee also Heisenberg."

SetAttributes[Canon, Listable]

Canon[ Canon[q_?HeisenbergQ] ] := q

Canon /:
MultiplyKind[ Canon[q_] ] := MultiplyKind[q]

Canon /:
MultiplyGenus[ Canon[q_] ] := MultiplyGenus[q]

Canon /:
Dagger[ Canon[q_?HeisenbergQ] ] := Canon[q]

Canon /: 
Format @ Canon[c_Symbol?SpeciesQ[j___]] :=
  Interpretation[SpeciesBox[c, {j}, {"c"}], c[j]]

Canon /:
Format @ Canon[c_Symbol?SpeciesQ] :=
  Interpretation[SpeciesBox[c, {}, {"c"}], c]

(* Allows op^Canon as a equivalent to Canon[op] *)
Canon /:
HoldPattern[ Power[expr_, Canon] ] := Canon[expr]


(**** <CreatorQ> <AnnihilatorQ> ****)

AnnihilatorQ::usage = "AnnihilatorQ[op[j]] returns 1 if op[j] is an annihilation operator and 0 otherwise."

CreatorQ::usage = "CreatorQ[op[j]] returns 1 if op[j] is a cration operator and 0 otherwise."

(* Bosons *)
AnnihilatorQ[HoldPattern @ Dagger[_?BosonQ]] = False

AnnihilatorQ[_?BosonQ] = True

CreatorQ[HoldPattern @ Dagger[_?BosonQ]] = True

CreatorQ[_?BosonQ] = False

(* Fermions with Void vacuum *)
AnnihilatorQ[HoldPattern @ Dagger[op_?FermionQ]] /; !seaQ[op] = False

AnnihilatorQ[op_?FermionQ] /; !seaQ[op]  = True

CreatorQ[HoldPattern @ Dagger[op_?FermionQ]] /; !seaQ[op] = True

CreatorQ[op_?FermionQ] /; !seaQ[op] = False

(* Fermions with Sea vacuum.
   In this case, the Flavor indices should also be consistent with its Spin as
   well as its Vacuum.
   See also Spin[], Vacuum[]. *)

(* NOTE: Returns True only when definite. False does not necessarily mean
   'No'; still potentially afirmative. *)

HoldPattern @
  AnnihilatorQ[ Dagger[op:_Symbol?FermionQ[k_?Negative, ___]] ] :=
  True /; seaQ[op]

HoldPattern @
  AnnihilatorQ[ Dagger[op:_Symbol?FermionQ[k_?NonNegative, ___]] ] :=
  False /; seaQ[op]

AnnihilatorQ[ op:_Symbol?FermionQ[k_?NonNegative, ___] ] := True /; seaQ[op]

AnnihilatorQ[ op:_Symbol?FermionQ[k_?Negative, ___] ] := False /; seaQ[op]

AnnihilatorQ[_?AnyFermionQ] := False


HoldPattern @
  CreatorQ[ Dagger[op:_Symbol?FermionQ[k_?NonNegative, ___]] ] :=
  True /; seaQ[op]

HoldPattern @
  CreatorQ[ Dagger[op:_Symbol?FermionQ[k_?Negative, ___]] ] :=
  False /; seaQ[op]

HoldPattern @
  CreatorQ[ op:_Symbol?FermionQ[k_?Negative, ___] ] := True /; seaQ[op]

HoldPattern @
  CreatorQ[ op:_Symbol?FermionQ[k_?NonNegative, ___] ] := False /; seaQ[op]

CreatorQ[_?AnyFermionQ] := False

(**** </CreatorQ> </AnnihilatorQ> ****)


Bosons::usage = "Bosons[expr] gives the list of all Bosons appearing in expr."

Bosons[expr_] := Select[Agents @ expr, BosonQ]


Fermions::usage = "Fermions[expr] gives the list of all Fermions appearing in expr."

Fermions[expr_] := Select[Agents @ expr, FermionQ]

Heisenbergs::usage = "Heisenbergs[expr] gives the list of all Heisenbergs appearing in expr."

Heisenbergs[expr_] := Select[Agents @ expr, HeisenbergQ]

Majoranas::usage = "Majoranas[expr] gives the list of all Majoranas appearing in expr."

Majoranas[expr_] := Select[NonCommutativeSpecies @ expr, MajoranaQ]


FockFourier::usage = "FockFourier is now obsolete. Use TransformByFourier instead."

FockInverseFourier::usage = "FockInverseFourier is now obsolete. Use TransformByFourierInverse instead."

FockFourier[args__] := (
  Message[Q3General::obsolete, "FockFourier", "TransformByFourier"];
  FourierMap[args]
 )

FockInverseFourier[args__] := (
  Message[Q3General::obsolete, "FockInverseFourier", "TransformByFourierInvere"];
  InverseFourierMap[args]
 )


(*** Transformations between Dirac and Majorana Fermions ***)

DiracToMajorana::usage = "DiracToMajorana[expr, {c1,c2,...} -> {h1,h2,h3,h4,...}] converts expr writtten in Dirac fermion operators c1, c2, ... into an equivalent form in terms of the Majorana fermion operators h1, h2, h3, h4, ... via a suitable transformation between them. DiracToMajorana[expr, c1 -> {h1,h2}, c2->{h3,h4}, ...] is the same."

DiracToMajorana::incnst = "Inconsistent Dirac and Majorana fermion operators, `` and ``. There should be twice more Majorana fermion operators than Dirac fermion operators."

DiracToMajorana[expr_,
  rr:HoldPattern[
    {__?FermionQ} -> {PatternSequence[_?MajoranaQ, _?MajoranaQ]..}
   ]
 ] := Simplify[ expr //. rulesDiracToMajorana[rr] ]

DiracToMajorana[expr_,
  rr:HoldPattern[
    _?FermionQ -> {_?MajoranaQ, _?MajoranaQ}]..
   ] := Simplify[ expr //. rulesDiracToMajorana[rr] ]

rulesDiracToMajorana[HoldPattern[
    c_?FermionQ -> {h1_?MajoranaQ, h2_?MajoranaQ}
   ]] :=  {
     HoldPattern @ Dagger[c] -> (h1 - I*h2)/Sqrt[2],
     c -> (h1 + I*h2)/Sqrt[2] }

rulesDiracToMajorana[
  rr:HoldPattern[_?FermionQ -> {_?MajoranaQ, _?MajoranaQ}].. (* *)
 ] := Flatten[rulesDiracToMajorana /@ {rr}, 1]

rulesDiracToMajorana[HoldPattern[
    cc:{__?FermionQ} -> hh:{PatternSequence[_?MajoranaQ, _?MajoranaQ]..}
   ]] /; 2 Length[cc] == Length[hh] :=
  Apply[rulesDiracToMajorana, Thread[Rule[cc, Partition[hh,2]]]]

rulesDiracToMajorana[ HoldPattern[cc:{__} -> hh:{__}] ] := (
  Message[DiracToMajorana::incnst, cc, hh];
  Return[{}]
 )


MajoranaToDirac::usage = "MajoranaToDirac[expr, {h1,h2,h3,h4,...} -> {c1,c2,...}] converts expr writtten in Dirac fermion operators c1, c2, ... into an equivalent form in terms of the Majorana fermion operators h1, h2, h3, h4, ... via a suitable transformation between them. MajoranaToDirac[expr, {h1,h2} -> c1, {h3,h4} -> c2, ...] is the same."

MajoranaToDirac::incnst = "Inconsistent Dirac and Majorana fermion operators, `` and ``. There should be twice more Majorana fermion operators than Dirac fermion operators."

MajoranaToDirac[expr_,
  rr:HoldPattern[
    {PatternSequence[_?MajoranaQ, _?MajoranaQ]..} -> {__?FermionQ}
   ]
 ] := Simplify[ expr //. rulesMajoranaToDirac[rr] ]

MajoranaToDirac[expr_,
  rr:HoldPattern[{_?MajoranaQ, _?MajoranaQ} -> _?FermionQ].. (* *)
 ] := Simplify[ expr //. rulesMajoranaToDirac[rr] ]

rulesMajoranaToDirac[HoldPattern[
    {h1_?MajoranaQ, h2_?MajoranaQ} -> c_?FermionQ
   ]] := Module[
     { d = c /. { Dagger -> Identity } },
     { h1 -> (d + Dagger[d])/Sqrt[2],
       h2 -> (d - Dagger[d])/Sqrt[2]/I }
    ]

rulesMajoranaToDirac[
  rr:HoldPattern[{_?MajoranaQ, _?MajoranaQ} -> _?FermionQ].. (* *)
 ] := Flatten[rulesMajoranaToDirac /@ {rr}, 1]

rulesMajoranaToDirac[HoldPattern[
    hh:{PatternSequence[_?MajoranaQ, _?MajoranaQ]..} -> cc:{__?FermionQ}
   ]] := Apply[rulesMajoranaToDirac, Thread[Rule[Partition[hh,2], cc]]] /;
  2 Length[cc] == Length[hh]

rulesMajoranaToDirac[ HoldPattern[hh:{__} -> cc:{__}] ] := (
  Message[MajoranaToDirac::incnst, cc, hh];
  Return[{}]
 )


HeisenbergToBoson::usage = "HeisenbergToBoson[expr, {x1, x2, ...} -> {a1, a2, ...}] converts expr writtten in canonical Heisenberg operators x1, x2, ... into an equivalent form in terms of the Boson operators a1, a2, ... via a suitable transformation between them. HeisenbergToBoson[expr, x1 -> a1, x2 -> a2, ...] is the same."

HeisenbergToBoson[expr_, rr:(_?HeisenbergQ -> _?BosonQ)..] :=
  Simplify[ expr //. rulesHeisenbergToBoson[rr] ]

HeisenbergToBoson[expr_, rr:({__?HeisenbergQ} -> {__?BosonQ})..] :=
  Simplify[ expr //. rulesHeisenbergToBoson[rr] ]

rulesHeisenbergToBoson[x_?HeisenbergQ -> a_?BosonQ] :=
  { Canon[x] -> (a - Dagger[a]) / (I Sqrt[2]),
    x -> (a + Dagger[a]) / Sqrt[2] }

rulesHeisenbergToBoson[rr:(_?HeisenbergQ -> _?BosonQ)..] :=
  Flatten[ rulesHeisenbergToBoson /@ {rr}, 1 ]

rulesHeisenbergToBoson[rr:({__?HeisenbergQ} -> {__?BosonQ})] :=
  Apply[ rulesHeisenbergToBoson, Thread[rr] ]


BosonToHeisenberg::usage = "BosonToHeisenberg[expr, {x1, x2, ...} -> {a1, a2, ...}] converts expr writtten in canonical Heisenberg operators x1, x2, ... into an equivalent form in terms of the Boson operators a1, a2, ... via a suitable transformation between them. BosonToHeisenberg[expr, x1 -> a1, x2 -> a2, ...] is the same."

BosonToHeisenberg[expr_, rr:(_?BosonQ -> _?HeisenbergQ)..] :=
  Simplify[ expr //. rulesBosonToHeisenberg[rr] ]

BosonToHeisenberg[expr_, rr:({__?BosonQ} -> {__?HeisenbergQ})..] :=
  Simplify[ expr //. rulesBosonToHeisenberg[rr] ]

rulesBosonToHeisenberg[a_?BosonQ -> x_?HeisenbergQ] :=
  { a -> (x + I Canon[x]) / Sqrt[2] }

rulesBosonToHeisenberg[rr:(_?BosonQ -> _?HeisenbergQ)..] :=
  Flatten[ rulesBosonToHeisenberg /@ {rr}, 1 ]

rulesBosonToHeisenberg[rr:({__?BosonQ} -> {__?HeisenbergQ})] :=
  Apply[ rulesBosonToHeisenberg, Thread[rr] ]


(* **************************************************************** *)
(*   <Conjugate>                                                    *)
(* **************************************************************** *)

Dagger /:
HoldPattern @ Conjugate @ Dagger[q_?FockOperatorQ] := Dagger[q]

Multiply /:
HoldPattern @
  Conjugate[ Multiply[a_?AnyFockOperatorQ, b__?AnyFockOperatorQ] ] :=
  Multiply[ a, b ]
(* NOTE: Do not generalize it too much. For example, <a|op|b> is a complex
   number and under Dagger switches to complex conjugation. If the above is
   generalized too much, then it may results in, i.e., Conjugate[Ket[]]
   instead of <b|Dagger[op]|a>. *)

(* **************************************************************** *)
(*   </Conjugate>                                                    *)
(* **************************************************************** *)


(*** DECLARE canonical commutation and anti-commutation relations ***)
(*** IMPORTANT: DO NOT replace CMT[] with Commutator[]! ***)

(* For Heisenberg canonical operators *)

CMT[op_, Canon[op_]] := +I /; HeisenbergQ[op]

CMT[Canon[op_], op_] := -I /; HeisenbergQ[op]

CMT[op_[j1___], Canon[op_[j2___]]] := +I * KroneckerDelta[{j1},{j2}] /;
  HeisenbergQ[op]

CMT[Canon[op_[j2___]], op_[j1___]] := -I * KroneckerDelta[{j1},{j2}] /;
  HeisenbergQ[op]

CMT[_?AnyHeisenbergQ, _?AnyHeisenbergQ] = 0
(* NOTE: Operators with different Heads are regarded different regardless of
   their Flavor indices. This is conventional. If you want to change this
   behavior, Multiply[] should also be modified accordingly. *)

(* For Bosonic operators *)

HoldPattern @ CMT[ op_, Dagger[op_] ] := +1 /; BosonQ[op]

HoldPattern @ CMT[ Dagger[op_], op_ ] := -1 /; BosonQ[op]

HoldPattern @ CMT[ op_[j1___], Dagger[op_[j2___]] ] :=
  +KroneckerDelta[{j1},{j2}] /; BosonQ[op]

HoldPattern @ CMT[ Dagger[op_[j2___]], op_[j1___] ] :=
  -KroneckerDelta[{j1},{j2}] /; BosonQ[op]

CMT[_?AnyBosonQ, _?AnyBosonQ] = 0
(* NOTE: Operators with different Heads are regarded different regardless of
   their Flavor indices. This is conventional. If you want to change this
   behavior, Multiply[] should also be modified accordingly. *)

(* For Fermionic operators *)

SetAttributes[ACMT, Orderless]

HoldPattern @ ACMT[ op_?FermionQ, Dagger[op_?FermionQ] ] = 1

HoldPattern @ ACMT[ Dagger[op_?FermionQ], op_?FermionQ ] = 1

HoldPattern @ ACMT[ op_?FermionQ[i___], Dagger[op_?FermionQ[j___]] ] :=
  KroneckerDelta[{i}, {j}]

ACMT[_?AnyFermionQ, _?AnyFermionQ] = 0
(* NOTE: Operators with different Heads are regarded different regardless of
   their Flavor indices. This is conventional. If you want to change this
   behavior, Multiply[] should also be modified accordingly. *)


(**** <Multiply> ****)

(** Heisenbergs **)

HoldPattern @
  Multiply[pre___, a:_?HeisenbergQ, b:Canon[_?HeisenbergQ], post___] :=
  Multiply[pre, CMT[a, b], post] + Multiply[pre, b, a, post]

HoldPattern @
  Multiply[pre___, a:Canon[_?HeisenbergQ], b:Canon[_?HeisenbergQ], post___] :=
  Multiply[pre, b, a, post] /; Not @ OrderedQ[{a, b}]

HoldPattern @
  Multiply[pre___, a:_?HeisenbergQ, b:_?HeisenbergQ, post___] :=
  Multiply[pre, b, a, post] /; Not @ OrderedQ[{b, a}]
(* NOTE: Operators without Canon are ordered in REVERSE canonical order. *)


(** Bosons **)

HoldPattern @
  Multiply[pre___, a:_?BosonQ, b:Dagger[_?BosonQ], post___] :=
  Multiply[pre, CMT[a, b], post] + Multiply[pre, b, a, post]

HoldPattern @
  Multiply[pre___, a:Dagger[_?BosonQ], b:Dagger[_?BosonQ], post___] :=
  Multiply[pre, b, a, post] /; Not @ OrderedQ[{a, b}]

HoldPattern @
  Multiply[pre___, a:_?BosonQ, b:_?BosonQ, post___] :=
  Multiply[pre, b, a, post] /; Not @ OrderedQ[{b, a}]
(* NOTE: Operators without Dagger are ordered in REVERSE canonical order. *)


(** Fermions **)

(* Pauli exclusion principle *)

HoldPattern @ Multiply[___, op_?FermionQ, op_?FermionQ, ___] = 0

HoldPattern @ Multiply[___, Dagger[op_?FermionQ], Dagger[op_?FermionQ], ___] = 0

(* Dagger[f] of a fermion operator is not necessarily a creation
   operator. Nevertheless, daggered operators (seemingly creation operators)
   are pushed through to the left for fast performance. *)

HoldPattern @
  Multiply[pre___, a:_?FermionQ, b:Dagger[_?FermionQ], post___] :=
  Multiply[pre, ACMT[a,b], post] - Multiply[pre, b, a, post]

HoldPattern @
  Multiply[pre___, a:Dagger[_?FermionQ], b:Dagger[_?FermionQ], post___] :=
  -Multiply[pre, b, a, post] /; Not @ OrderedQ[{a, b}]

HoldPattern @
  Multiply[pre___, a:_?FermionQ, b:_?FermionQ, post___] :=
  -Multiply[pre, b, a, post] /; Not @ OrderedQ[{b, a}]
(* NOTE: Operators without Dagger are ordered in REVERSE canonical order. *)


(** Majoranas **)

HoldPattern @
  Multiply[pre___, op_, op_, post___] := 1/2 Multiply[pre, post] /;
  MajoranaQ[op]

HoldPattern @ Multiply[pre___, op_?MajoranaQ[i___], op_?MajoranaQ[j___], post___] :=
  Multiply[pre, post] KroneckerDelta[{i},{j}] -
  Multiply[pre, op[j], op[i], post] /;
  Not @ OrderedQ @ {op[i], op[j]}
(* NOTE: Operators with different Heads are regarded different regardless of
   their Flavor indices. This is conventional. If you want to change this
   behavior, Multiply[] should also be modified accordingly. *)

HoldPattern @ Multiply[pre___, op__?MajoranaQ, post___] :=
  Multiply[pre, Sequence @@ Sort @ {op}, post] Signature @ {op} /;
  Not @ OrderedQ @ {op}

(**** </Multiply> ****)


Q::usage = "Q is an alias for " <> ToString[
  Hyperlink["FockNumber", "paclet:Q3/ref/FockNumber"],
  StandardForm ] <>
  ", which is one of the most frequently used operator. Because the symbol N is reserved by the Mathematica system, we instead use Q."

Q = FockNumber

FockNumber::usage = "FockNumber[c] returns the number operator corresponding to the operator c. FockNumber[c1, c2, ...] returns the sumb of all FockNumber operators corresponding to operators c1, c2, ...."

FockNumber[ op_?ParticleQ ] := Multiply[ Dagger[op], op ]

FockNumber[x:({__?ParticleQ}|_?ParticleQ)..] := Total @ Map[FockNumber] @ Flatten @ {x}


Hop::usage = "Hop is an alias for " <> ToString[
  Hyperlink["FockHopping", "paclet:Q3/ref/FockHopping"],
  StandardForm ]

Hop = FockHopping


FockHopping::usage = "FockHopping[a, b, c, ...] returns Dagger[a]**b + Dagger[b]**c + ..., describing the hopping process from b to a, c to b, and so on. One or more arguments can be a vector or matrix."

FockHopping[a_?ParticleQ, b_?ParticleQ] := Multiply[ Dagger[a], b ]
(* NOTE: Only for hopping from b to a. *)

FockHopping[a_?MajoranaQ, b_?MajoranaQ] := I Multiply[a, b]
(* NOTE: It corresponds to the FULL hopping Dagger[a]**b + Dagger[b]**a for
   Dirac fermions. *)

(* NOTE: One could use Cauchy`Chain. *)

FockHopping[a:Except[_List]] = 0

FockHopping[a:Except[_List], b:Except[_List]] := Multiply[ Dagger[a], b ]

FockHopping[x_?VectorQ, b_?FockOperatorQ] := Sum[ FockHopping[a,b], {a, x} ]

FockHopping[a_?FockOperatorQ, y_?VectorQ] := Sum[ FockHopping[a,b], {b, y} ]

FockHopping[x_?VectorQ, y_?VectorQ] :=
  Total @ Apply[ FockHopping, Tuples @ {x, y}, {1} ]

(* Conserved over all sites *)
FockHopping[x_?MatrixQ] := Total @ Map[FockHopping] @ Transpose @ x

(* Conserved at the left end *)
FockHopping[x_?MatrixQ, y__] := FockHopping[x] + FockHopping[Last @ x, y]

(* Conserved at the right end *)
FockHopping[x__, y_?MatrixQ] := FockHopping[x, First @ y] + FockHopping[y]

(* Conserved in the middle *)
FockHopping[x__, y_?MatrixQ, z__] :=
  FockHopping[x, First @ y] + FockHopping[y] + FockHopping[Last @ y, z]

FockHopping[a_, b_, c__] := FockHopping[a,b] + FockHopping[b,c]

FockHopping[x_List] := FockHopping[ Sequence @@ x ]


Pair::usage = "Pair is an alias for FockPairing."

Pair = FockPairing

FockPairing::usage = "FockPairing[a, b, c, ...] returns a**b + b**c + ..., describing the pair-annihilation process of a and b, b and c, and so on. One or more arguments can be a vector or matrix."

FockPairing[x__] := FockHopping[x] /. {Dagger -> Identity}


FockSpin::usage = "FockSpin[c] returns the list of the spin operators in all three directions. FockSpin[c,dir] returns the spin operator in the dir direction (dir = 1 for X, 2 for Y, 3 for Z). The spin raising and lowering operator is returned by dir = 4 and 5, respectively. FockSpin[c1, c2, ...] returns the total spin associated with the operators c1, c2, .... FockSpin[c1, c2, ..., dir] returns the total spin in the particular direction dir."

FockSpin[ c_?ParticleQ ] := FockSpin[c, {1,2,3}]

FockSpin[ c_?ParticleQ, dd:{ Repeated[1|2|3,3] } ] :=
  Map[ FockSpin[c,#]&, dd ]

FockSpin[ c_?ParticleQ, dir:(1|2|3|4|5) ] := With[
  { cc = c[All] },
  MultiplyDot[ Dagger @ cc, theWigner[{Spin[c[Any]], dir}], cc]
 ] /; spinfulQ[ c[Any] ]
(* dir = 4 for Raising,
   dir = 5 for Lowering *)

FockSpin[ c_?ParticleQ, dir_ ] /; spinlessQ[ c[Any] ] = 0

FockSpin[ ops:{__?ParticleQ},
  dir:(PatternSequence[]|1|2|3|4|5|{Repeated[1|2|3,3]}) ] :=
  Sum[ FockSpin[a,dir], {a, ops} ]

FockSpin[ ops:(_?ParticleQ|{__?ParticleQ})..,
  dir:(PatternSequence[]|1|2|3|4|5|{Repeated[1|2|3,3]}) ] :=
  FockSpin[ Flatten @ {ops}, dir ]

FockSpin[ ops:{(_?ParticleQ|{__?ParticleQ})..},
  dir:(PatternSequence[]|1|2|3|4|5|{Repeated[1|2|3,3]}) ] :=
  FockSpin[ Flatten @ ops, dir ]

(* Operator form *)

FockSpin[dir:(PatternSequence[]|1|2|3|4|5|{Repeated[1|2|3,3]})][op__] := FockSpin[op, dir]

FockSpin[dir:Repeated[1|2|3,3]][op__] := FockSpin[op, {dir}]


theWigner::usage = "theWigner[{J,k}] returns the matrix representation of the angular momentum operator of magnitude J in the k'th direction."

theWigner[{J_?SpinNumberQ, 0}] := IdentityMatrix[2J+1]

theWigner[{J_?SpinNumberQ, 1}] := (theWigner[{J,4}]+theWigner[{J,5}])/2

theWigner[{J_?SpinNumberQ, 2}] := (theWigner[{J,4}]-theWigner[{J,5}])/(2I)

theWigner[{J_?SpinNumberQ, 3}] := DiagonalMatrix @ Range[J,-J,-1]

theWigner[{J_?SpinNumberQ, 4}] := With[
  { v = Table[Sqrt[J(J+1)-M(M+1)], {M, J, -J, -1}] },
  RotateLeft[ DiagonalMatrix[v] ]
 ]

theWigner[{J_?SpinNumberQ, 5}] := With[
  { v = Table[Sqrt[J(J+1)-M(M-1)], {M, J, -J, -1}] },
  RotateRight[ DiagonalMatrix[v] ]
 ]



(* SS::usage = "SS[dir][a,b,...] is an alias for FockSpinSpin[a,b,..., dir]." *)

FockSpinSpin::usage = "FockSpinSpin[a, b] gives the operator expression for the spin-spin coupling between two spins associated with a and b. FockSpinSpin[a, b, dir] describes the coupling in the particular direction dir."

(* NOTE (2020-11-01): At the moment, the connectivity way of FockSpinSpin is
   different from FockHpping, FockPairing, and Chain. Better to follow the
   same rule. See also WignerSpinSpin, which is implemented by means of
   Chain. *)

FockSpinSpin[a_?ParticleQ, b_?ParticleQ, dir:(1|2|3)] := With[
  { s1 = FockSpin[a, dir],
    s2 = FockSpin[b, dir] },
  Simplify @ Multiply[s1,s2]
 ]

FockSpinSpin[a_?ParticleQ, b_?ParticleQ, dd:{(1|2|3)..}] := With[
  { s1 = FockSpin[a, dd],
    s2 = FockSpin[b, dd] },
  Simplify[s1 ~ MultiplyDot ~ s2]
 ]

FockSpinSpin[a_?ParticleQ, b_?ParticleQ] := With[
  { s1 = FockSpin[a],
    s2 = FockSpin[b] },
  Simplify[s1 ~ MultiplyDot ~ s2]
 ]

FockSpinSpin[ ops:{__?ParticleQ},
  dir:(PatternSequence[]|1|2|3|4|5|{Repeated[1|2|3,3]}) ] :=
  Total @ MapThread[
    FockSpinSpin[#1,#2,dir]&,
    {Most @ ops, Rest @ ops}
   ]

FockSpinSpin[ ops:(_?ParticleQ|{__?ParticleQ})..,
  dir:(PatternSequence[]|1|2|3|4|5|{Repeated[1|2|3,3]}) ] :=
  FockSpinSpin[ Flatten @ {ops} ]

FockSpinSpin[ ops:{(_?ParticleQ|{__?ParticleQ})..},
  dir:(PatternSequence[]|1|2|3|4|5|{Repeated[1|2|3,3]}) ] :=
  FockSpinSpin[ Flatten @ ops ]

(* Operator form *)

FockSpinSpin[dir:(PatternSequence[]|1|2|3|4|5|{Repeated[1|2|3,3]})][op__] := FockSpinSpin[op, dir]

FockSpinSpin[dir:Repeated[1|2|3,3]][op__] := FockSpinSpin[op, {dir}]


FockSpinor::usage = "FockSpinor[c] returns a list that is practically equal to c[All]. Dagger[FockSpinor[c]] forms a spherical irreducible tensor, whose order is Spin[c[Any]].\nFockSpinor[{c1, c2, ...}] or FockSpinor[c1, c2, ...] returns the join list of the results from FockSpinor applied to each of c1, c2, ...."

FockSpinor[ cc_List ] := Flatten[FockSpinor /@ cc]

FockSpinor[ a_, b__ ] := FockSpinor @ {a, b}

FockSpinor[ c_?ParticleQ ] := c[All] /; spinfulQ[c[Any]]

FockSpinor[ c_ ] := { c } (* spinless case *)


FockIsospinor::usage = "FockIsospinor[c] returns the (2S+1)-component spinor in the Nambu (i.e., particle-hole) space associate with the fermionic operator c. Unlike FockSpinor, FockIsospinor is defined only for operators with half-integer spins."

SetAttributes[FockIsospinor, Listable]

FockIsospinor[c_?FermionQ] :=
  Garner @ ( c[All] /. { c[j___,s_?Negative] :> Dagger[c[j,s]] } ) /;
  HalfIntegerQ[ TrueSpin[c[Any]] ]
(* Recall that integer spins are allowed for Fermions. *)


FockIsospin::usage = "FockIsospin[c] returns the isospin operator corresponding to the fermionic operator c. The phase factor is either 1 or -1. The default value of factor is 1."

SetAttributes[FockIsospin, Listable]

FockIsospin[op_?FermionQ, dir_] := With[
  { cc = FockIsospinor[op] },
  Garner @ MultiplyDot[Dagger @ cc, theWigner[{Spin[op[Any]], dir}], cc]
 ] /; HalfIntegerQ[ TrueSpin[op[Any]] ]

FockIsospin[op_Symbol, dir_] := FockIsospin[op[], dir]

FockIsospin[op_] := FockIsospin[op, {1,2,3}]


FockDegree::usage = "FockDegree[expr] returns the highest degree of the terms in Fock expression expr. The degree of a term is the sum of the exponents of the Fock operators that appear in the term. The concept is like the degree of a polynomial. FockDegree[expr] is 0, if expr is free of Fock operators. Note that Grassmann variables are regarded as special numbers and do NOT count for the Fock degree. See also GrassmannGrade[expr]."
(* NOTE: For Grassmann variables, which form a graded algebra, 'grade' is
   defined. *)

FockDegree[a_ + b_] := Max[FockDegree[a], FockDegree[b]]

FockDegree[a_ b_] := FockDegree[a] + FockDegree[b]

FockDegree[HoldPattern @ Multiply[a_, b__]] := FockDegree[a] + FockDegree[Multiply[b]]

FockDegree[_?AnyFockOperatorQ] = 1

FockDegree[_?CommutativeQ] = 0

FockDegree[expr_] := 0 /; FreeQ[expr, _?AnyFockOperatorQ]

(* MultiplyDegree for operators *)
MultiplyDegree[_?AnyFockOperatorQ] = 1


FockBilinearQ::usage = "FockBilinearQ[expr, False] retunrs True if expr is a bilinear combination of operators, either normal or anomalous. FockBilinearQ[expr,True] returns True if expr is a bilinear combination AND includes at least one anomalous combination such as creator times creator. FockBilinearQ[expr] is equivalent to FockBilinearQ[expr, False]."

FockBilinarSystem::usage = "FockBilinearSystem[expr] returns a list of {operators, matrix} of the bilinear combination."

FockBilinearMatrix::usage = "FockBilinearMatrix[expr] gives the coefficient matrix of the bilinear form."

FockBilinearOperators::usage = "FockBilinearOperators[expr] returns the list of all operators involved in the bilinear combination."

FockBilinearQ[expr_] := FockBilinearQ[expr, False]

(* Binlinear combinations either normal or anomalous *)
FockBilinearQ[expr_, False] := And[
  FockDegree[expr //. {_Multiply -> 0}] == 0,
  FockDegree[expr] == 2
 ]

(* Bilinear AND at least ONE anomalous combination *)
FockBilinearQ[expr_, True] := Module[
  { anomalous },
  anomalous = Length @ Cases[ expr,
    HoldPattern[
      Multiply[_?ParticleQ, _?ParticleQ] |
      Multiply[Dagger[_?ParticleQ], Dagger[_?ParticleQ]]
     ],
    {0, Infinity}
   ];
  If[ anomalous > 0, True, False, False ]
 ] /; FockBilinearQ[expr, False]

(* Otherwise fails the test *)
FockBilinearQ[expr_, True] = False

FockBilinearSystem[expr_] := Module[
  { ops = FockBilinearOperators[expr] },
  { ops, CoefficientTensor[expr, Dagger @ ops, ops] }
 ] /; FockBilinearQ[expr, False]

FockBilinearMatrix[expr_] := Last @ FockBilinearSystem[expr] /; FockBilinearQ[expr,False]

(* Including the anomalous bilinear terms. *)
FockBilinearOperators[expr_] := With[
  {ops = getOperators[expr]},
  Join[ops, Dagger[ops]]
 ] /; FockBilinearQ[expr, True]

(* Not including the anomalous bilinear terms. *)
FockBilinearOperators[expr_] := getOperators[expr] /; FockBilinearQ[expr, False]

(* Extract the list of all operators appearing in the Fock expression. *)
getOperators[expr_] :=
  Union @ Cases[ expr, _?FockOperatorQ | Canon[_?HeisenbergQ], {0, Infinity} ]


(* LieExp: Baker-Hausdorff theorem *)

LieExp[gen_, expr_] := Module[
  { ops, mat, rules, n },
  { ops, mat } = FockBilinearSystem[gen];
  
  If[ And @@ AnyBosonQ /@ ops,
    n = Length[ops] / 2;
    mat[[1+n;;, All]] *= -1;
   ];

  mat = FunctionExpand @ MatrixExp[-2*mat];
  rules = Thread[ Rule[ops, mat.ops] ];
  
  Garner[ expr /. rules ]
 ] /; FockBilinearQ[gen, True]
(* TODO: To support Heisenbergs *)

LieExp[gen_, expr_] := Module[
  { ops, mat, new, rules },
  { ops, mat } = FockBilinearSystem[gen];

  If[ And @@ MajoranaQ /@ ops, mat *= 2; ];

  new = FunctionExpand @ MatrixExp[+mat];
  rules = Thread[ Dagger[ops] -> Dagger[ops].new ];

  new = FunctionExpand @ MatrixExp[-mat];
  rules = Join[ rules, Thread[ops -> new.ops] ];
  (* NOTE: In general, the rules for Dagger[c[j]] is not equal to Dagger of
     the rules for c[j]. For example, consider the case where mat (i.e., gen)
     is not anti-Hermitian. *)
  (* NOTE: The rules of Dagger[c[j]] should come before the ones for c[j]. *)

  Garner[ expr /. rules ]
 ] /; FockBilinearQ[gen]
(* TODO: To support Heisenbergs *)

(* Baker-Hausdorff Lemma *)
AddElaborationPatterns[
  HoldPattern @ Multiply[
    pre___,
    MultiplyExp[a_], b__, MultiplyExp[c_],
    post___
   ] :> Multiply[pre, LieExp[a, Multiply[b]], post] /;
    Garner[a + c] == 0
 ]

(* ********************************************************************** *)


(* ********************************************************************** *)
(* *** Fock Space ******************************************************* *)
(* ********************************************************************** *)

NullState::usage = "NullState[] refers to an impossible Fock-space vector in the creation-operator representation. It is denoted by Ket[Null]. The arising of NullState[] implies something is going wrong during the evaluation. Any operator on NullState[] simply returns NullState[] again."

HoldPattern @ Multiply[___, Ket[Null], ___] = Ket[Null]

HoldPattern @ Multiply[___, Bra[Null], ___] = Bra[Null]


(*** VacuumState and Vacuum Expectation Values ***)

VacuumState::usage = "VacuumState[] returns Ket[Vacuum] which refers to the vacuum state in the Fock space. It is the state that is annihilated by any annihilation operator."

HoldPattern @
  Multiply[ pre___, Bra[a_Association], Ket[Vacuum], post___ ] :=
  BraKet[a, Association[]] Multiply[pre, post]

HoldPattern @ Multiply[ pre___, Bra[Vacuum], Ket[b_Association], post___ ] :=
  BraKet[Association[], b] Multiply[pre, post]

HoldPattern @
  Multiply[ pre___, Bra[Vacuum], Ket[Vacuum], post___ ] :=
  BraKet[{}, {}] Multiply[pre, post]


HoldPattern @ Multiply[a___, op_?AnnihilatorQ, Ket[Vacuum], b___] = 0 

HoldPattern @ Multiply[a___, Bra[Vacuum], op_?CreatorQ, b___] = 0

HoldPattern @ Multiply[___, op_?BosonQ, more__, Ket[Vacuum], ___] := 0 /;
  FreeQ[{more}, Dagger[_?BosonQ]]
(* Without this, because of the ordering policy, the bosonic annihilator may
   not directly see VacuumState[] when mixed with other types. *)

HoldPattern @ Multiply[___, Bra[Vacuum], more__, op_?AnyFermionQ, ___] := 0 /;
  CreatorQ[op] /; FreeQ[{more}, _?FermionQ]
(* Without this, because of the ordering polity, the fermionic creator may
   not directly see VacuumState[] when mixed with other types. *)


SurviveVacuum::usage = "SurviveVacuum[expr] drops vacuum-annihilating parts of expression expr."

SurviveVacuum[expr_] := Multiply[expr, Ket[Vacuum]] /. {Ket[Vacuum] -> 1}


VacuumExpectation::usage = "VacuumExpectation[expr] returns the vacuum expectation value of an operator expression.
  The option Method specifies the evaluation method: With
\"Algebra\" it uses the standard algebraic method and with \"Occupations\" using the Fock states Ket[<|...|>]."

SetAttributes[VacuumExpectation, Listable]

Options[VacuumExpectation] = { Method -> "Algebra" }

BraKet[{},{}] = 1 (* Bra[].Ket[] = 1 *)

VacuumExpectation[expr_, OptionsPattern[]] :=
  fVacuumExpectation[OptionValue[Method]][expr]

fVacuumExpectation["Algebra"][expr_] :=
  Multiply[ Bra[Vacuum], expr, Ket[Vacuum] ]

fVacuumExpectation["Occupations"][expr_] := Multiply[ Bra[<||>], expr, Ket[<||>] ]


(* Odd number of operators *)

HoldPattern @ Multiply[Bra[Vacuum], x__?AnyParticleQ, Ket[Vacuum]] /; OddQ[Length @ {x}] = 0

(* Special rules for bosons *)

HoldPattern @ Multiply[ Bra[Vacuum], __?BosonQ, Ket[Vacuum] ] = 0

HoldPattern @ Multiply[ Bra[Vacuum], Dagger[_?BosonQ].., Ket[Vacuum] ] = 0

(* Special rules for Vacuum == "Sea" *)

(* (1-n_k) |0> *)
HoldPattern @
  Multiply[Bra[Vacuum], more___,
    op:c_[k_,j___], Dagger[op:c_[k_,j___]], Ket[Vacuum]] := 
  UnitStep[k] VacuumExpectation[Multiply[more]] /;
  FermionQ[c] && seaQ[op]
(* 2016-09-01 Can this case occur with Dagger[c] always pushed to the left? *)

(* <0| (1-n_k) *)
HoldPattern @
  Multiply[Bra[Vacuum], op:c_[k_,j___], Dagger[op:c_[k_,j___]],
    more___, Ket[Vacuum]] :=
  UnitStep[k] VacuumExpectation[Multiply[more]] /;
  FermionQ[c] && seaQ[op]
(* 2016-09-01 Can this case occur with Dagger[c] always pushed to the left? *)

(* n_k |0> *)
HoldPattern @
  Multiply[Bra[Vacuum], more___,
    Dagger[op:c_[k_,j___]], op:c_[k_,j___], Ket[Vacuum]] :=
  UnitStep[-k] VacuumExpectation[Multiply[more]] /;
j  FermionQ[c] && seaQ[op]

(* <0| n_k *)
HoldPattern @
  Multiply[Bra[Vacuum], Dagger[op:c_[k_,j___]], op:c_[k_,j___],
    more___, Ket[Vacuum]] :=
  UnitStep[-k] VacuumExpectation[Multiply[more]]  /;
  FermionQ[c] && seaQ[op]

(* Special rule for Spin = 1/2 and Vacuum == "Sea".
   Assumption: The vacuum has a well-defined particle number and spin
   z-compoenent. Otherwise, this rule gives a wrong result. *)

HoldPattern @ Multiply[Bra[Vacuum], x__?electronQ, Ket[Vacuum]] := Module[
  {isospin, spin},
  {isospin, spin} = Transpose @ Map[getIsospinSpin, {x}];
  isospin = Total @ isospin;
  spin = Total @ spin;
  0 /; Not[isospin == spin == 0]
 ]

electronQ[op_?AnyParticleQ] := TrueSpin[op]==1/2 && seaQ[op]
(* NOTICE TrueSpin[op], not Spin[op].
   Suppose that c be a Spin 1/2 fermion with See vacuum. At least two Flavor
   indices, one for orbital mode and the other for SpinZ, are required;
   otherwise, Spin 0 is assumed. If one passes just c (without even the square
   bracket), then Spin[c] gives 1/2 and regarded as Electron in spite of the
   inconsistent Flavor index. *)

(* Spins of particles and holes are opposite. *)
HoldPattern @ getIsospinSpin[ Dagger[_Symbol?ParticleQ[__, s_]] ] := {1/2, s}

getIsospinSpin[_Symbol?ParticleQ[__, s_]] := {-1/2, -s}


(* Special reule for unpaired operators *)

HoldPattern @ Multiply[Bra[Vacuum], a__?AnyParticleQ, Ket[Vacuum]] /;
  unpairedQ[a] = 0

(* Returns True if the operators sequence is DEFINITELY unpaired. False does
   not necessarily mean the sequene is all paired. Undetermined case is
   regarded potentially paired.  See also TrueQ[]. *)

HoldPattern @ unpairedQ[ Dagger[_?ParticleQ] | _?ParticleQ ] = True

unpairedQ[ a_?AnyParticleQ, b__?AnyParticleQ ] := Module[
  {species, toll},
  species = speciesForm[{a,b}];
  toll = Total /@ Last /@ Transpose /@ Gather[
    species,
    If[ First[#1]===First[#2] && #1[[2]]==#2[[2]], True, False, True ]&
    (* NOTICE the forth argument of If[] for a very conservative test.
       NOT If[expr, True, False, False]
       NOR TrueQ[expr]
       NOR '===' *)
   ];
  toll = DeleteCases[toll, 0];
  toll =!= {}
 ]

speciesForm::usage = "Converts an operator into a list of {{flavors}, isospin}."

SetAttributes[speciesForm, Listable]

HoldPattern @ speciesForm[ Dagger[a_?ParticleQ] ] := speciesForm[a] * {1, 1, -1}

speciesForm[ x:a_Symbol?ParticleQ[j___] ] := {a, {j}, -1}
(* NOTE: {a[j], -1} does not work because, say, a[1] == a[2] is undertmined
   while it is obviously False. *)

speciesForm[ a_Symbol?ParticleQ ] := {a, {}, -1}

(* The most general case for TWO operators with Vacuum == "Sea".
   Note that it allows for variables in the Flavor indices.
   This is required for more general expression, for example, in
   conjunction with Wick's theorem. *)

HoldPattern @ Multiply[
  Bra[Vacuum],
  Dagger[x:a_Symbol?FermionQ[k1_,j1___]], y:a_[k2_,j2___],
  Ket[Vacuum]
 ] := KroneckerDelta[k1,k2] * KroneckerDelta[{j1},{j2}] * UnitStep[-k1] /;
  seaQ[x] && seaQ[y]
(* NOTE: Operators with different Heads are assumed to be different
   operators. *)

(* For operators with NUMERIC Flavor indices, for which CreatorQ[] and
   AnnihilatorQ[] give definite answers. *)

HoldPattern @ Multiply[Bra[Vacuum], ops__?AnyFockOperatorQ, Ket[Vacuum]] := Module[
  { Zz, new },
  (* NOTE: Zz can be replaced by any symbol which can be canonically
     ordered either lastest or earliest. *)
  Let[Fermion, Zz, Spin -> 0];
  new = VacuumExpectation[
    Multiply @@ ({ops} /. rulesParticleHole[Zz])];
  new /. rulesParticleHoleInverse[Zz]
 ] /; And @@ Map[NumericQ] @ Flatten @ Flavors @ {ops}

rulesParticleHole[f_] := {
  HoldPattern @ Dagger[c_Symbol?FermionQ[k_?Negative, j___?NumericQ]] :>
    f[c, k, j] /; seaQ[c],
  c_Symbol?FermionQ[k_?Negative, j___?NumericQ] :>
    Dagger[f[c, k, j]] /; seaQ[c],
  HoldPattern @ Dagger[c_Symbol?FermionQ] :> Dagger[f[c]] /; seaQ[c],
  c_Symbol?FermionQ :> f[c] /; seaQ[c]
 }

rulesParticleHoleInverse[f_] := {
  HoldPattern @ Dagger[f[c_, k__]] :> c[k],
  f[c_, k__] :> Dagger[c[k]],
  HoldPattern @ Dagger[f[c]] :> Dagger[c],
  f[c] :> c
 }

(* By definition, the vacuum expectation value of a normal ordered
   expression is zero! *)

HoldPattern @ Multiply[Bra[Vacuum], FockColon[_], Ket[Vacuum]] = 0


(**** <Displacement> ****)

Displacement::usage = "Displacement[z, a] represents the displacement operator of the Bosonic mode a, where z is a complex number.\nDisplacement[\[Xi], c] for Fermion c, \[Xi] is a Grassmann number."

Displacement /:
Peel[ Displacement[_, a_] ] := a (* for Matrix[] *)

Displacement /:
MultiplyKind[ Displacement[_, a_] ] := MultiplyKind[a] (* for Multiply[] *)

Displacement /:
MultiplyGenus[ Displacement[_, a_] ] := "Singleton" (* for Multiply[] *)

Displacement /:
AnySpeciesQ[ Displacement[_, a_] ] := AnySpeciesQ[a] (* for Multiply[] *)

Displacement /:
Dagger @ Displacement[z_?CommutativeQ, a_?BosonQ] :=
  Displacement[-z, a]

Displacement[0, _?BosonQ] = 1

Displacement[z_, op:{__?BosonQ}] :=
  Displacement @@@ Thread[{z, op}]

Displacement[zz_List, a_?BosonQ] := Displacement @@@ Thread[{zz,a}]


HoldPattern @ Multiply[pre___,
  Displacement[z_?CommutativeQ, a_?BosonQ], a_?BosonQ,
  post___] := (
    Multiply[pre, a, Displacement[z, a], post] -
      z Multiply[pre, Displacement[z, a], post]
   )

HoldPattern @ Multiply[pre___,
  Displacement[z_?CommutativeQ, a_?BosonQ], Dagger[a_?BosonQ],
  post___] := (
    Multiply[pre, Dagger[a], Displacement[z, a], post] -
      Conjugate[z] Multiply[pre, Displacement[z, a], post]
   )

HoldPattern @ Multiply[pre___,
  Displacement[x_?CommutativeQ, a_?BosonQ],
  Displacement[y_?CommutativeQ, a_?BosonQ],
  post___] := Multiply[pre, Displacement[x+y, a], post]

HoldPattern @ Multiply[pre___,
  x:Displacement[_?CommutativeQ, a_?BosonQ],
  y:Displacement[_?CommutativeQ, b_?BosonQ],
  post___] := Multiply[pre, y, x, post] /; Not @ OrderedQ @ {a, b}


HoldPattern @ Multiply[pre___,
  Displacement[z_, a_?BosonQ],
  CoherentState[vv_Association],
  post___] :=
  Multiply[pre, CoherentState[CoherentState @ vv, a -> vv[a]+z], post]


(* For Fermion,
   D(z) := Exp[ -z ** Dagger[c] + c ** Conjugate[z] ] *)

Displacement[z_?GrassmannQ, c_?FermionQ] := Multiply[
  1 - z ** Dagger[c],
  1 + c ** Conjugate[z],
  1 + z ** Conjugate[z] / 2
 ]

(**** </Displacement> ****)


(**** <CoherentState> ****)

CoherentState::usage = "CoherentState[c[k]->z] = Ket[c[k]->z] gives the coherent state of the operator c[k].  CoherentState is normalized to 1.  It is actually a place holder, but using Elaborate, you can represent it explicitly in terms of the creation and annihilation operator."

CoherentState::boson = "The resulting expression may have been truncated. Recall that coherent states of bosons involves infinitely many Fock states."

AddGarnerPatterns[_CoherentState]

AddElaborationPatterns[_CoherentState]


Format @ CoherentState[a_Association] :=
  Interpretation[Ket[a], CoherentState @ a]

Format @ HoldPattern @ Dagger[v_CoherentState] :=
  Interpretation[Bra @@ v, Dagger @ v]


CoherentState /:
NonCommutativeQ[ CoherentState[_Association] ] = True

CoherentState /:
MultiplyKind[ CoherentState[_Association] ] = Ket

CoherentState /:
MultiplyGenus[ CoherentState[_Association] ] = "Ket"


CoherentState /:
HoldPattern @ toCatForm @ CoherentState[aa_Association] := Module[
  { bb = KeySelect[aa, BosonQ],
    ff = KeySelect[aa, FermionQ] },
  bb = Exp @ Total[-Abs[Values @ bb]^2/2] * 
    Apply[Multiply, KeyValueMap[MultiplyExp[#2*Dagger[#1]]&, bb]];
  ff = Multiply @@ KeyValueMap[Displacement[#2, #1]&, ff];
  ff ** bb ** Ket[Vacuum]
 ]


CoherentState /:
HoldPattern @ Elaborate @ CoherentState[aa_Association] := Module[
  { bb = KeySelect[aa, BosonQ],
    ff = KeySelect[aa, FermionQ] },
  If[Length[bb] > 1, Message[CoherentState::boson]];
  bb = Multiply @@ AssociationMap[theCoherentState, bb];
  ff = Multiply @@ KeyValueMap[Displacement[#2, #1]&, ff];
  bb ** ff ** Ket[<||>]
 ]

theCoherentState[a_?BosonQ -> z_] := Exp[-Abs[z]^2 / 2] * With[
  { nn = Range[Bottom @ a, Top @ a] },
  Basis[a] . ( Power[z, nn] / Sqrt[Factorial @ nn] )
 ]


Matrix[CoherentState[a_Association], ss:{__?SpeciesQ}] :=
  CircleTimes @@ Map[theCoherentStateVector, Thread[ss -> Lookup[a, ss]]]

theCoherentStateVector[a_?BosonQ -> z_] := Exp[-Abs[z]^2 / 2] * With[
  { nn = Range[Bottom @ a, Top @ a] },
  Dot[Power[z, nn] / Sqrt[Factorial @ nn], One @ Dimension @ a]
 ]


(*  Constructing CoherentState *)

$coherentSpec = Alternatives[
  _?BosonQ -> _?CommutativeQ,
  _?FermionQ -> _?GrassmannQ,
  {__?BosonQ} -> _?CommutativeQ,
  {__?BosonQ} -> {__?CommutativeQ},
  {__?FermionQ} -> __?GrassmannQ,
  {__?FermionQ} -> {__?GrassmannQ}
 ]

CoherentState[ op:$coherentSpec.. ] :=
  CoherentState[ CoherentState[<||>], op ]

CoherentState[ CoherentState[a_Association], op:$coherentSpec.. ] := Module[
  { rules = Flatten @ KetRule @ {op} },
  CoherentState @ KeySort @ Join[a, Association @ rules]
 ]


(* Hermitian product between CoherentStates *)

CoherentState[ a:_Association, a ] := 1

CoherentState[ a_Association, b_Association ] := Module[
  { op = Union[ Keys @ a, Keys @ b ],
    za, zb },
  za = Lookup[a, op];
  zb = Lookup[b, op];
  Times @@ Exp[-Dagger[za]**za/2-Dagger[zb]**zb/2 + Dagger[za]**zb]
 ]

HoldPattern @ Multiply[ x___,
  Dagger[CoherentState[a_Association]], CoherentState[b_Association],
  y___ ] := CoherentState[ a, b ] * Multiply[x, y]


(* Op ** CoherentState[...] *)

HoldPattern @
  Multiply[pre___, op_?ParticleQ, CoherentState[v_Association], post___] := 
  Multiply[pre, CoherentState[v], v[op], post] /;
  KeyExistsQ[v, op]
(* NOTE: v[op] can be a Grassmann variable; hence still inside Multiply. *)

HoldPattern @
  Multiply[pre___, op_?ParticleQ, CoherentState[v_Association], post___] := 0 /;
  Not @ KeyExistsQ[v, op]
(* NOTE: Default value for unspecified particles is 0. *)

HoldPattern @ Multiply[ pre___,
  Dagger[CoherentState[v_Association]], Dagger[op_?ParticleQ],
  post___ ] := Multiply[pre, Dagger[op ** CoherentState[v]], post]

(**** </CoherentState> ****)


(**** <FockAddSpin> ****)

FockAddSpin::usage = "FockAddSpin[c1, c2, ...] returns the irreducible basis of the total angular momentum S[c1] + S[c2] + ....\nFockAddSpin[] returns the trivial basis including only VacuumState[]."

FockAddSpin[ ls:{(_?ParticleQ|_Association)...} ] :=
  FockAddSpin @@ Map[FockAddSpin] @ ls

FockAddSpin[] := Association[ {0,0} -> {Ket[Vacuum]} ]

FockAddSpin[irb_Association] := irb

FockAddSpin[c_?ParticleQ] := Module[
  { cc = FockSpinor[c],
   irb },
  irb = Multiply[Dagger[#], Ket[Vacuum]]& /@ GroupBy[cc, {TrueSpin[#], SpinZ[#]}&];
  (* NOTICE TrueSpin[#], not Spin[#]. This is a fallback for
     inconsistent Flavor indices, in which case SpinZ vanishes. *)
  Merge[{Association[{0,0} -> {Ket[Vacuum]}], irb}, Catenate]
  (* NOTE: The following code does not work for Spinless case:
     Prepend[ irb, {0,0} -> {Ket[Vacuum]} ]
     *)
 ]

FockAddSpin[a___, b_?ParticleQ, c___] := FockAddSpin[a, FockAddSpin[b], c]

FockAddSpin[irb_Association, irc_Association, ird__Association] :=
  FockAddSpin[ FockAddSpin[irb, irc], ird]

FockAddSpin[irb_Association, irc_Association] := Module[
  { S1 = Union @ Map[First] @ Keys @ irb,
    S2 = Union @ Map[First] @ Keys @ irc,
    SS,
    gb = Union @ Map[Base] @ Cases[irb, _?ParticleQ, Infinity],
    gc = Union @ Map[Base] @ Cases[irc, _?ParticleQ, Infinity],
    new },
  SS = Flatten[
    Outer[Thread[{#1, #2, Range[Abs[#1 - #2], #1 + #2]}] &, S1, S2], 
    2 ];
  SS = Flatten[
    Map[Thread[{Sequence @@ #, Range[-Last@#, Last@#]}] &]@SS, 
    1 ];
  new = doFockAddSpin[irb, irc, #]& /@ SS;
  new = Merge[new, Catenate];
  If[ ContainsAny[gb, gc],
    new = trimIrreducibleBasis @ DeleteCases[ DeleteCases[new, 0, {2}], {} ];
    (* 0 or {} occurs when spins at the same site are added. *)
   ];
  Return[ new ]
 ]

doFockAddSpin[irb_, irc_, {S1_, S2_, S_, Sz_}] := Module[
  { new, min, max },
  min = Max[-S1, Sz - S2, (Sz - (S1 + S2))/2];
  max = Min[S1, Sz + S2, (Sz + (S1 + S2))/2];
  new = Sum[
    Multiply @@@ Tuples[{irb[{S1, m}], irc[{S2, Sz - m}]}] *
      ClebschGordan[{S1, m}, {S2, Sz - m}, {S, Sz}],
    {m, Range[min, max]}
   ];
  new = Garner @ Multiply[(new /. Ket[Vacuum] -> 1), Ket[Vacuum]];
  Association[ {S, Sz} -> new ]
 ]

trimIrreducibleBasis[irb_Association] := Module[
  { irc = Simplify @ Map[(#/FockNorm[#])&] @ irb },
  irc = Map[ DeleteDuplicates[#, Simplify @ Or[#1==#2, #1==-#2]&]& ] @ irc;
  irc
 ]

(**** </FockAddSpin> ****)


FockAddSpinZ::usage = "FockAddSpinZ[c1, c2, ...] returns the irreducible basis of the total directional angular momentum Sz[c1] + Sz[c2] + ....\nFockAddSpinZ[] returns the trivial basis including only VacuumState[]."

FockAddSpinZ[ops__?FermionQ] := FockAddSpinZ @ {ops}

FockAddSpinZ[ops:{__?FermionQ}] := Module[
  { cc = FockSpinor[ops],
    nn, zz },
  zz = SpinZ[cc];
  nn = Tuples[{0, 1}, Length @ cc];
  nn = GroupBy[nn, (zz.#)&];
  FockCat @ KeySort @ Map[Ket[cc->#]&, nn, {2}]
 ]

FockAddSpinZ[] := Association[ 0 -> Ket[Vacuum] ]

(*** Vectors in the Fock Space ***)

(* Ket := The occupation-number representation of a basis vector in the Fock space. *)
(* Cat := The creation-operator represenation of a basis vector in the Fock space.
   Hence, Cat is an multiplication of creators on VacuumState[]. *)

catQ[ Ket[Vacuum] ] = True

catQ[ z_?CommutativeQ Ket[Vacuum] ] = True

catQ[ HoldPattern @ Multiply[__, Ket[Vacuum]] ] = True

catQ[ z_?CommutativeQ HoldPattern @ Multiply[__, Ket[Vacuum]] ] = True

catQ[ z_?CommutativeQ expr_ ] := catQ[expr]

catQ[ a_ + b_ ] := catQ[a] && catQ[b]

catQ[ _ ] = False


FockCat::usage = "FockCat[n1,n2,...] or equivalently FockCat[Ket[n1,n2,...] converts the occupation-number representation into the creation-operator representation, i.e., as a multiplication of a series of generators on VacuumState[]."

FockCat[rr:(_?AnyParticleQ -> _Integer?NonNegative) ...] :=
  toCatForm @ Ket[rr]

FockCat[rr:({__?AnyParticleQ} -> {__Integer?NonNegative})] :=
  toCatForm @ Ket[rr]

FockCat[expr_] := toCatForm[expr] /; Not @ FreeQ[expr, _Ket|_CoherentState]

FockCat[0] = 0


toCatForm::usage = "Returns a multiplication of generators (creation operators generating the Fock space basis) equivalent to the Fock state v in the occupation number representation."

SetAttributes[toCatForm, Listable]

toCatForm[expr_Plus] := Garner @ Map[toCatForm, expr]

toCatForm[z_?CommutativeQ expr_] := z toCatForm[expr]

toCatForm[ Ket[Null] ] = Ket[Null]

toCatForm[ Ket[v_Association] ] := Module[
  { cc = Keys @ v,
    nn = Values @ v },
  cc = MultiplyPower[Dagger @ cc, nn] / Sqrt[nn!];
  Multiply[ Multiply @@ cc, Ket[Vacuum] ]
 ]


(**** <FockKet> ****)

FockKet::usage = "FockKet[expr] converts FockCat[] form to Ket[] form. Recall that FockCat[] gives a Fock state with VacuumState[] is multiplied at the rightmost."

FockKet[expr_] := KetRegulate[expr /. Ket[Vacuum] -> Ket[<||>]]
(* TODO: This does not properly handle Fermion state with the Fermi sea as the
   vacuum. *)

(**** </FockKet> ****)


(**** <Ket for Fock> ****)

(*
KetRule[ r:Rule[_?ParticleQ, _] ] := r

KetRule[ r:Rule[{__?ParticleQ}, _] ] := Thread[r]
 *)

theKetTrim[Rule[_?ParticleQ, 0]] = Nothing

KetVerify::boson = "Invalid value `` for boson ``."

KetVerify[a_?BosonQ, v_?Negative] := (
  Message[KetVerify::boson, v, a];
  $Failed
 )

KetVerify::fermion = "Invalid value `` for fermion ``."

KetVerify[c_?FermionQ, v_] := (
  Message[KetVerify::fermion, v, c];
  $Failed
 ) /; Not[BinaryQ @ v]
(* NOTE: The following definition would not allow to assign a symbolic value:
   KetVerify[ _?FermionQ, Except[0|1] ] = $Failed *)

(**** </Ket for Fock> ****)

(* Operations on Ket[] *)

HoldPattern @
  Multiply[pre___, op_?BosonQ, Ket[v_Association], post___] :=
    If[ v[op] == 0,
      Return[0],
      Sqrt[v[op]] * Multiply[pre, Ket[Ket @ v, op -> v[op]-1], post]
    ]
(* NOTE: The Keys are sorted in the result. *)

HoldPattern @
  Multiply[pre___, Dagger[op_?BosonQ], Ket[v_Association], post___] :=
    Sqrt[v[op]+1] * Multiply[pre, Ket[Ket @ v, op -> v[op]+1], post]
(* NOTE: The Keys are sorted in the result. *)

HoldPattern @
  Multiply[pre___, op_?HeisenbergQ, Ket[v_Association], post___] :=
  Module[
    { vv = v,
      ww = v },
    vv[op] = v[op] - 1;
    ww[op] = v[op] + 1;
    Multiply[
      pre,
      Sqrt[v[op]] * Ket[vv] + Sqrt[v[op]+1] * Ket[ww]
      post
     ] / Sqrt[2] // Garner
   ]

HoldPattern @
  Multiply[pre___, Canon[op_?HeisenbergQ], Ket[v_Association], post___] :=
  Module[
    { vv = v,
      ww = v },
    vv[op] = v[op] - 1;
    ww[op] = v[op] + 1;
    Multiply[
      pre,
      Sqrt[v[op]] * Ket[vv] - Sqrt[v[op]+1] * Ket[ww]
      post
     ] / (I*Sqrt[2]) // Garner
   ]


HoldPattern @
  Multiply[pre___, op_?FermionQ, Ket[v_Association], post___] :=
    If[ v[op] == 0,
      Return[0],
      (* TODO: This doesn't respect fermions with Sea vacuum. *)
      Signature[Prepend[Keys @ KeyDrop[theKetTrim @ v, op], op]] *
        Multiply[pre, Ket[Ket @ v, op -> 0], post]
    ]
(* NOTE: The Keys of v are assumed to be sorted. *)

HoldPattern @
  Multiply[pre___, Dagger[op_?FermionQ], Ket[v_Association], post___] := 
    If[ v[op] == 1,
      Return[0],
      (* TODO: This doesn't respect fermions with Sea vacuum. *)
      Signature[Prepend[Keys @ theKetTrim @ v, op]] *
        Multiply[pre, Ket[Ket @ v, op -> 1], post]
    ]
(* NOTE: The Keys are sorted in the result. *)


HoldPattern @
  Multiply[pre___, Bra[v_Association], op_?AnyParticleQ, post___] :=
  Multiply[pre, Dagger @ Multiply[ Dagger[op], Ket[v] ], post]

HoldPattern @
  Multiply[pre___, Bra[v_Association], op_?AnyHeisenbergQ, post___] :=
  Multiply[pre, Dagger @ Multiply[ Dagger[op], Ket[v] ], post]


theFermiSignature::usage = "Returns the signature for adding to or removing from the Ket a FERMION at the position j."

theFermiSignature[v_Association, c_?FermionQ] := Module[
  { ff = SequenceSplit[Keys[v], {c, ___}] },
  If[Length[ff] == 0, Return[1]];
  1 - 2*Mod[Total @ Lookup[v, First @ ff], 2]
 ]


FockNorm::usage = "FockNorm[v] returns the norm of the state v, which is either in the occupation number representation or in the creation-operator representation."

SetAttributes[FockNorm, Listable]

FockNorm[expr_] := Sqrt @ Multiply[Dagger @ expr, expr]

FockAvg::usage = "FockAvg[op, a] computes the braket <a|op|a>, where op is an operator expression and a is some state."

SetAttributes[FockAvg, Listable]

FockAvg[op_, a_] := Multiply[Dagger @ a, op, a]


FockMatrix::usage = "FockMatrix[op, vlist] computes the matrix elements of the operator op between the vectors in the list vlist. Vecotrs in vlist can be either in the Ket or Cat form (the latter is slightly more efficient. FockMatrix[op, vlist1, vlist2] calculates the matrix elements between two vectors, one from vlist1 and the other from vlist2. FockMatrix[op, basis] calculates the matrix elements between vectors in the basis 'basis'. The basis is a list with particular structure and can be constructed by FermionBasis."

Options[FockMatrix] = {"DiagonalOnly" -> True}

FockMatrix[op_, vv_List?VectorQ] := FockMatrix[op, vv, vv]

FockMatrix[op_, basis_Association, opts___?OptionQ] := Module[
  { only = "DiagonalOnly" /. {opts} /. Options[FockMatrix] },
  If[ only,
    diagonalBlocks[op, basis],
    allBlocks[op, basis]
   ]
 ]

FockMatrix[op_, vv1:{___?catQ}, vv2:{___?catQ}] :=
  Outer[ Multiply[#1, op, #2]&, Dagger @ FockKet @ vv1, FockKet @ vv2 ]
(* FockKet[] is much faster to evalculate *)

FockMatrix[op_, vv1_List?VectorQ, vv2:{___?catQ}] :=
  Outer[ Multiply[#1, op, #2]&, Dagger @ vv1, FockKet @ vv2 ]
(* FockKet[] is much faster to evalculate *)

FockMatrix[op_, vv1_List?VectorQ, vv2:{___?catQ}] :=
  Outer[ Multiply[#1, op, #2]&, Dagger @ vv1, FockKet @ vv2 ]
(* FockKet[] is much faster to evalculate *)

FockMatrix[op_, vv1:{___?catQ}, vv2_List?VectorQ] :=
  Outer[ Multiply[#1, op, #2]&, Dagger @ FockKet @ vv1, vv2 ]
(* FockKet[] is much faster to evalculate *)

FockMatrix[op_, vv1_List?VectorQ, vv2_List?VectorQ] :=
  Outer[ Multiply[#1, op, #2]&, Dagger @ vv1, vv2 ]


diagonalBlocks[op_, basis_Association] :=
  Map[ (Simplify @ FockMatrix[op, #, #])&, basis ]

allBlocks[op_, basis_Association] := Module[
  { qnn, mat },
  qnn = Tuples[Keys @ basis, 2];
  mat = Values @ basis;
  mat = Flatten[ Outer[FockMatrix[op, #1, #2]&, mat, mat, 1], 1 ];
  Association @ Thread[ qnn -> mat ]
 ]


FockMatrixForm::usage = "FockMatrixForm[m] displays in a human-friendly form the 'matrix' m, which is usually produced by FockMatrix and has a special data structure."

Format @ FockMatrixForm[
  mat:Association[({{___},{___}}->_?MatrixQ)..],
  title_String:"",
  opts___?OptionQ
 ] := Module[
   { row, col, bdy, cnt },
   row = DeleteDuplicates[ First /@ Keys @ mat ];
   bdy = Partition[ Values @ mat, Length @ row ];
   cnt = Map[Length] @ Catenate @ First @ bdy;
   {row, col} = matrixHeaders[row, cnt];
   
   bdy = ArrayFlatten @ bdy;
   bdy = ArrayFlatten[{
       { {{title}}, row },
       { col, bdy }
      }];

   (* Dividers *)
   cnt = 2 + Accumulate @ cnt;
   cnt = Thread[Rule[Most@cnt, Dashed]];
   
   Grid[
     bdy,
     opts,
     Frame -> True,
     Alignment -> Center,
     Dividers -> {
       {2 -> True, Sequence @@ cnt},
       {2 -> True, Sequence @@ cnt}
      }
    ]
  ]

Format @ FockMatrixForm[
  mat:Association[({___} -> _?MatrixQ)..],
  title_String:"",
  opts___?OptionQ
 ] := Module[
   { bdy = Values @ mat,
     cnt = Length /@ Values @ mat,
     row, col },
   {row, col} = matrixHeaders[ Keys @ mat, cnt ];

   bdy = CirclePlus @@ bdy;
   bdy = ArrayFlatten @ {{{{title}}, row}, {col, bdy}};
   
   (* Dividers *)
   cnt = 2 + Accumulate @ cnt;
   cnt = Thread[Rule[Most@cnt, Dashed]];

   Grid[
     bdy,
     opts,
     Frame -> True,
     Alignment -> Center,
     Dividers -> {
       {2 -> True, Sequence @@ cnt},
       {2 -> True, Sequence @@ cnt}
      }
    ]
  ]

matrixHeaders[qnn:{{___}..}, cnt:{___Integer}] := Module[
  {row, col},
  row = List @ Catenate @ MapThread[
    PadRight[{#1}, #2, SpanFromLeft]&,
    {qnn, cnt}
   ];
  col = Transpose @ (row /. SpanFromLeft -> SpanFromAbove);
  {row, col}
 ]


(**** <Matrix> ****)

(* Matrix for Fermions *)

TheMatrix[ _?FermionQ ] := SparseArray[{1,2} -> 1, {2, 2}]

TheMatrix[ Parity[a_?FermionQ] ] :=
  SparseArray[{{1,1} -> 1, {2,2} -> -1}, {2, 2}]

TheMatrix[ Ket @ Association[_?FermionQ -> n:(0|1)] ] :=
  SparseArray[n+1 -> 1, 2]


(* Matrix for Bosons *)

TheMatrix[ a_?BosonQ ] := Module[
  { nn, ii, jj, rr },
  nn = Range[Bottom @ a, Top @ a];
  ii = Most @ nn - Bottom[a] + 1;
  jj = Rest @ nn - Bottom[a] + 1;
  rr = MapThread[ Rule, { Transpose @ {ii, jj}, Sqrt @ Rest @ nn } ];
  SparseArray[ rr, {1, 1} (1+Top[a]-Bottom[a]) ]
 ]

TheMatrix[ Parity[a_?BosonQ] ] := Module[
  { jj = Range[Bottom @ a, Top @ a],
    pp },
  pp = Power[-1, jj];
  jj = jj - Bottom[a] + 1;
  SparseArray @ Thread[ Transpose @ {jj, jj} -> pp ]
 ]

TheMatrix[ Ket[ Association[a_?BosonQ -> n_Integer] ] ] := SparseArray[
  If[Bottom[a] <= n <= Top[a], (1+n-Bottom[a])->1, {}, {}],
  Dimension[a]
 ]

(**** </Matrix> ****)


(**** <Parity> ****)

Parity /:
Elaborate[ op:Parity[_?BosonQ] ] = op
(* NOTE: There is no simple way to express the parity for bosons. *)

Parity /:
Elaborate[ Parity[c_?FermionQ] ] :=
  1 - 2 * Multiply[Dagger[c], c]

Parity /:
HoldPattern @
  Multiply[pre___, Parity[a_?ParticleQ], v_Ket, post___] :=
  Power[-1, v[a]] Multiply[pre, v, post]

Parity /:
HoldPattern @
  Multiply[pre___, Parity[a_?ParticleQ], a_?ParticleQ, post___] :=
  - Multiply[pre, a, Parity[a], post]

Parity /:
HoldPattern @
  Multiply[pre___, Parity[a_?ParticleQ], Dagger[a_?ParticleQ], post___] :=
  - Multiply[pre, Dagger[a], Parity[a], post]

Parity /:
HoldPattern @
  Multiply[pre___, Parity[a_?ParticleQ], b_?AnyParticleQ, post___] :=
  Multiply[pre, b, Parity[a], post] /;
  Commutator[a, b] == 0


ParityValue[v_Ket, a_?ParticleQ] := 1 - 2*Mod[v[a], 2]

ParityEvenQ[v_Ket, a_?ParticleQ] := EvenQ @ v @ a

ParityOddQ[v_Ket, a_?ParticleQ] := OddQ @ v @ a

(**** </Parity> ****)


(**** <Basis> ****)

Basis[c_?FermionQ] := Ket /@ Thread[ c->{0, 1} ]

Basis[b_?BosonQ] := Ket /@ Thread[ b->Range[Bottom@b, Top@b] ]

(**** </Basis> ****)


(**** <BosonBasis> ****)

BosonBasis::usage = "BosonBasis[{b1, b2, ...}, n] returns the Fock-state basis for Bosons b1, b2, ... with total number of particles up to n.\nBosonBasis[{b1, b2, ...}, {n}] gives the basis with exactly n particles.\nBosonBasis[{b1, b2, ...}, {m, n}] gives the basis with m to n particles.\nNote that if either m or n or both are specified the corresponding value of Bottom and/or Top of the Bosons are ignore."

BosonBasis[bb__?BosonQ] := BosonBasis @ {bb}

BosonBasis[bb__?BosonQ, n_Integer] := BosonBasis[{bb}, n]

BosonBasis[bb__?BosonQ, {m_Integer, n_Integer}] := BosonBasis[{bb}, {m, n}]

BosonBasis[bb__?BosonQ, {n_Integer}] := BosonBasis[{bb}, {n}]

BosonBasis[bb:{__?BosonQ}] :=
  BosonBasis[ bb, {Min[Bottom /@ bb], Total[Top /@ bb]} ]

BosonBasis[bb:{__?BosonQ}, n_Integer] :=
  BosonBasis[bb, {Min[Bottom /@ bb], n}]

BosonBasis[bb:{__?BosonQ}, {m_Integer, n_Integer}] :=
  Flatten @ Table[ BosonBasis[bb, {k}], {k, m, n}]

BosonBasis[ss:{__?BosonQ}, {n_Integer}] := With[
  { len = Length @ ss },
  Map[
    Ket[ss -> #]&,
    ReverseSort @ Flatten[
      Permutations /@ (PadRight[#, len]&) /@ IntegerPartitions[n, len],
      1 ]
   ]
 ]

(**** </BosonBasis> ****)


(**** <FermionBasis> ****)

FermionBasis::usage = "FermionBasis[c1, c2, ...] or FermionBasis[{c1, c2, ...}] returns the many-particle basis states (in the creation operators representation) for a single site, i.e. for operators c1, c2, .... It accepts two options \"Representation\" and \"Conserved\"."

FermionBasis::bigSpin = "Sorry, but for the moment, it can handle only spin-1/2 Fermion operators. These operators will be ignored: ``."

Options[FermionBasis] = {
  "Representation" -> "Occupations",
  (* "Representation" -> "Generators", *)
  "Conserved" -> {"Number", "Spin"}
 };

(* Basic constructions *)

FermionBasis[cc__?FermionQ, n_Integer] := FermionBasis[{cc}, n]

FermionBasis[cc__?FermionQ, {m_Integer, n_Integer}] :=
  FermionBasis[{cc}, {m, n}]

FermionBasis[cc__?FermionQ, {n_Integer}] := FermionBasis[{cc}, {n}]

FermionBasis[cc:{__?FermionQ}, n_Integer] :=
  KetRegulate[
    Ket @@@ Map[Thread[#->1]&] @ Subsets[cc, n],
    cc ]

FermionBasis[cc:{__?FermionQ}, {m_Integer, n_Integer}] :=
  Flatten @ Table[ FermionBasis[cc, {k}], {k, m, n}]

FermionBasis[cc:{__?FermionQ}, {n_Integer}] :=
  KetRegulate[
    Ket @@@ Map[Thread[#->1]&, Subsets[cc, {n}]],
    cc ]


(* Advanced constructions*)

FermionBasis[cc__?FermionQ, opts___?OptionQ] := FermionBasis[{cc}, opts]

FermionBasis[{cc__?FermionQ}, OptionsPattern[]] := Module[
  { rep = OptionValue["Representation"],
    qn = OptionValue["Conserved"],
    name },
  
  rep = rep /. {
    "Occupations" -> "Ket",
    "Generators" -> "Cat",
    _ -> "Cat" };
  
  qn = StringJoin @ If[ListQ @ qn, Sort @ qn, {qn}];
  
  name = StringJoin[Context @ name, "basis", rep, qn];
  If[NameQ @ name, Symbol[name][cc], {{} -> {}}]
 ]


basisKetNone::usage = "Make basis with no symmetries, i.e. no good quantum numbers.  Similar to FermionBasis[...] for a single site, but conforms to the proper basis format."

basisKetNone[ops__?FermionQ] := Module[
  { cc = FockSpinor[ops] },
  Association[ {} -> Map[ Ket[cc->#]&, Tuples[{0, 1}, Length @ cc] ] ]
 ]

basisCatNone[ops__?FermionQ] := Map[toCatForm] @ basisKetNone[ops];


basisKetNumber::usage = "Make a basis with good quantum number N."

basisKetNumber[ops__?FermionQ] := Module[
  { cc = FockSpinor[ops], nn },
  nn = Tuples[{0, 1}, Length @ cc];
  nn = GroupBy[nn, {Total@#}&];
  KeySort @ Map[Ket[cc->#]&, nn, {2}]
 ]

basisCatNumber[ops__?FermionQ] := Map[toCatForm] @ basisKetNumber[ops]


basisKetNumberSpinZ::usage = "basisKetNumberSpinZ[{ops}] returns the basis with well defined charge and spin projection quantum numbers (Q, Sz) in occupation number representation."

basisKetNumberSpinZ[ops__?FermionQ] := Module[
  { cc = FockSpinor[ops], nn, z },
  z = SpinZ[cc];
  nn = Tuples[{0, 1}, Length @ cc];
  nn = GroupBy[nn, {Total@#, z.#}&];
  KeySort @ Map[Ket[cc->#]&, nn, {2}]
 ]

basisCatNumberSpinZ::usage = "basisCatNumberSpinZ[{ops}] returns the basis with well defined charge and spin projection quantum numbers (Q,S_z) in creation operator representation."

basisCatNumberSpinZ[ops__?FermionQ] := Map[toCatForm] @ basisKetNumberSpinZ[ops];


basisCatSpin::usage = "Generates the irreducible basis in the Generator representation when Spin is conserved, i.e., in the presence of SU(2) symmetry."

basisKetSpin::usage = "Generates the irreducible basis when Spin is conserved, i.e., in the presence of SU(2) symmetry, in the occupation-number representation."

basisCatSpin[cc__?FermionQ] := Module[
  { irb = FockAddSpin @@ Base @ FockSpinor[cc] },
  irb = KeySelect[irb, (Equal @@ #) &];
  KeyMap[Take[#, 1]&, irb]
 ]

basisKetSpin[ops__?FermionQ] := FockKet @ basisCatSpin[ops]


basisCatNumberSpin::usage = "basisCatNumberSpin[{ops}] returns the basis with well defined charge and total spin quantum numbers (Q,S) in creation operator representation."

basisKetNumberSpin::usage = "Returns the basis with well defined charge and total spin quantum numbers (Q,S) in occupation number representation."

basisCatNumberSpin[cc__?FermionQ] := Module[
  { irb = basisCatSpin[cc] },
  irb = Map[GroupBy[#, (List @ FockDegree @ #)&]&, irb];
  irb = KeyValueMap[
    KeyMap[Function[key, Flatten @ {key, #1}], #2]&, 
    irb
   ];
  irb = KeySort @ Merge[irb, Catenate]
 ]

basisKetNumberSpin[cc__?FermionQ] := FockKet @ basisCatNumberSpin[cc]


PrintFermionBasis::usage = "PrintFermionBasis[bs] prints the Fermion basis bs in table form. Note that a Fermion basis is an association of particular structure.\nSee also FermionBasis."

Options[PrintFermionBasis] = {
  Frame -> False,
  Alignment -> {{Center, {Left}}, Center},
  Dividers -> {{}, {True, {Dashed}, True}}
 };

PrintFermionBasis[bs_Association] :=
  Grid[ Normal[bs] /. {Rule -> List}, Options[PrintFermionBasis] ]

(**** </FermionBasis> ****)


(* ******************************************************************** *)

FockDecompose::usage = "FockDecompose[vec, basis] decomposes a vector into components with respect to the given basis in the creation operator representation."

FockDecompose[vec_, basis_Association] := Map[Multiply[Dagger[#],vec]&, basis]

FockDecompose[vec_, basis_?VectorQ] := Map[Multiply[Dagger[#], vec]&, basis]

FockOrthogonalize::usage = "FockOrthogonalize[m] = Orthogonalize[m,Method->\"Householder\"] for matrix m. FockOrthogonalize[vecs, basis] orthogonalizes a list of vectors vecs in the creation operator representation basis 'basis'."

FockOrthogonalize[m_?MatrixQ] := Orthogonalize[m, Method->"Householder"]

(* FockOrthogonalize[{{0}}] = {} *)
(* Workaround for a bug in Mathematica 6 *)

FockOrthogonalize[vecs_?VectorQ, basis_?VectorQ] := Module[
  {m, l},
  m = Map[ FockKetDecompose[#, basis]&, vecs ];
  m = Simplify[m];
  (* Occasionally, when dealing with very complex sets of basis vectors
     in the OCCUPATION NUMBER REPRESENTATION,
     FockDecompose[] returns large non-simplified expressions. We need to
     Simplify them before calling Householder[], otherwise Householder[] never
     returns. *)
  l = FockOrthogonalize[m];
  l = Select[l, Norm[#] != 0 &]; (* Drop zero vectors *)
  Expand @ Map[(# . basis)&, l]
 ]
(* TODO: Any other more efficient way? *)


NormalOrder::usage = "NormalOrder[expr] normal orders an expression by subtracting its vacuum expectation value (VacuumExpectation)."

SetAttributes[NormalOrder, Listable]

NormalOrder[expr_] := expr - VacuumExpectation[expr]


FockColon::usage = "FockColon[expr] denotes the normal ordering of the operators in expr.\nThis is merely a placeholder, although its output is displayed with double dots surrounding expr. To explicitly evaluate the normal ordered expression, use NormalOrder function."

Let[LinearMap, FockColon]

FockColon[] = 1

Format @ HoldPattern @ FockColon[op__] := Interpretation[
  Row @ { Row @ {
      Style["\[Colon]", FontColor -> Red], op, 
      Style["\[Colon]", FontColor -> Red]
     } },
  FockColon[op]
 ]
(* NOTE: The outer RowBox is to avoid spurious parentheses around the Multiply
   expression. For example, without it, -2 :f**f: is formated as
   -2(:f f:). For more details on spurious parentheses, see
   https://goo.gl/MfCwMF *)


(**** JordanWignerTransform ****)

JordanWignerTransform::usage = "JordanWignerTransform[{q1,q2,\[Ellipsis]}->{f1,f2,\[Ellipsis]}] returns a list of rules {q1->op1, q2->op2, \[Ellipsis]} corresponding to the Jordan-Wigner transformation of qubit operators q1, q2, \[Ellipsis] onto operators op1, op2, \[Ellipsis] in terms of fermion operators f1, f2, \[Ellipsis].\nJordanWignerTransform[{f1,f2,\[Ellipsis]}->{q1,q2,\[Ellipsis]}] returns a list of rules {q1->op1, q2->op2, \[Ellipsis]} corresponding to the inverse Jordan-Wigner transformation of fermion operators f1, f2, \[Ellipsis] onto operators op1, op2, \[Ellipsis] in terms of qubit operators q1, q2, \[Ellipsis]."

JordanWignerTransform[expr_, {} -> {}] := expr

JordanWignerTransform[expr_, qq:{__?QubitQ} -> ff:{__?FermionQ}] :=
  Garner @ Elaborate[ expr /. JordanWignerTransform[qq -> ff] ]

JordanWignerTransform[expr_, ff:{__?FermionQ} -> qq:{__?QubitQ}] :=
  Garner @ Elaborate[ expr /. JordanWignerTransform[ff -> qq] ]

JordanWignerTransform[{} -> {}] := {}

JordanWignerTransform[qq:{__?QubitQ} -> ff:{__?FermionQ}] := Module[
  { rr = Through[Construct[qq, 4]],
    xx = Through[Construct[qq, 1]],
    yy = Through[Construct[qq, 2]],
    zz = Through[Construct[qq, 3]],
    cc, pp },
  pp = FoldList[Multiply, 1, Parity /@ Most[ff]];
  cc = pp ** ff;
  Join[
    Thread[Dagger[rr] -> Dagger[cc]],
    Thread[rr -> cc],
    Thread[xx -> Dagger[cc] + cc],
    Thread[yy -> I (Dagger[cc] - cc)],
    Thread[zz -> Map[Parity, ff]]
   ]
 ] /; Length[qq] == Length[ff]

JordanWignerTransform[ff:{__?FermionQ} -> qq:{__?QubitQ}] := Module[
  { rr = Through[Construct[qq, 4]],
    zz = Through[Construct[qq, 3]],
    cc, pp },
  pp = FoldList[Multiply, 1, Most @ zz];
  cc = Multiply @@@ Transpose @ {pp, rr};
  Thread[ff -> cc]
 ] /; Length[qq] == Length[ff]


(**** </JordanWignerTransform> ****)


Protect[ Evaluate @ $symbs ]

End[]

EndPackage[]
