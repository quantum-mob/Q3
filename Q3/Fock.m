(* -*- mode: math; -*- *)
BeginPackage[ "Q3`Fock`",
  { "Q3`Grassmann`", "Q3`Pauli`", "Q3`Cauchy`", "Q3`Abel`" }
 ]

Unprotect[Evaluate[$Context<>"*"]]

Print @ StringJoin[
  $Input, " v",
  StringSplit["$Revision: 2.5 $"][[2]], " (",
  StringSplit["$Date: 2021-01-12 03:29:41+09 $"][[2]], ") ",
  "Mahn-Soo Choi"
 ]

{ Let, Hermitian, Heisenberg, Boson, Fermion, Majorana };
{ Bosons, Heisenbergs, Fermions, Majoranas };
{ HermitianQ, HeisenbergQ, BosonQ, FermionQ, MajoranaQ, ParticleQ, OperatorQ };
{ AnyHeisenbergQ, AnyBosonQ, AnyFermionQ, AnyParticleQ, AnyOperatorQ };
{ AnnihilatorQ, CreatorQ };
{ AnticommutativeQ };

{ Spin, SpinZ, TrueSpin, Vacuum };

(*** Tools for operator expressions ***)

{ CanonicalConjugate = Cannon };

{ NormalOrder, FockColon };

{ FockDegree, FockCoefficientTensor = CoefficientTensor };

{ FockBilinearQ, FockBilinearSystem,
  FockBilinearOperators, FockBilinearMatrix };

{ FockDiracToMajorana, FockMajoranaToDirac,
  FockHeisenbergToBoson, FockBosonToHeisenberg };

(* Common bilinear combinations *)

{ FockNumber, Q, FockHopping, Hop, FockPairing, Pair };

{ FockSpin, FockSpinSpin, FockSpinor };

{ FockIsospin, FockIsospinor };

(*** Tools for many-particle states ***)

{ VacuumState = Ket[{}],
  VacuumExpectation, SurviveVacuum,
  Displacement, CoherentState, SqueezedState,
  NullState = Ket[Null] };

{ FockKet, FockCat, FockPad };
{ FockNorm, FockAvg };
{ BosonBasis,
  FermionBasis, {Representation, Conserved}, BasisForm, $BasisStyle };
{ FockMatrix, {DiagonalOnly}, FockMatrixFast, FockMatrixSparse,
  FockMatrixForm, $FockMatrixStyle };

{ FockDecompose, FockOrthogonalize };

{ FockAddSpin };

{ FockExpand, $FockExpandMethods };

{ FockFourier, FockInverseFourier }; (* Obsolete *)


Begin["`Private`"]

$symbs = Unprotect[
  Base, FlavorNone, AnySpeciesQ,
  Multiply, Dagger, MultiplyDegree, LieExp,
  Missing, KetTrim, KetRule, VerifyKet, Ket, Bra, BraKet,
  Basis, Matrix, BuildMatrix,
  Parity, ParityEvenQ, ParityOddQ,
  LogicalForm,
  $GarnerHeads, $GarnerTests, $RepresentableTests,
  Spin, ComplexQ
 ]


FlavorNone[a_?AnyParticleQ] := a


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

Vacuum::invIdx = "Invalid Flavor index `` for the operator `` with Spin `` and Vacuum ``. Regarded as \"Void\"."

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

  Kind[x] ^= Boson;
  Kind[x[___]] ^= Boson;
  
  Bottom[x] ^= bottom;
  Bottom[x[___]] ^= bottom;
  
  Top[x] ^= top;
  Top[x[___]] ^= top;

  Dimension[x] ^= 1 + top - bottom;
  Dimension[x[___]] ^= 1 + top - bottom;
  
  x /: Power[x, n_Integer] := MultiplyPower[x, n];
  x /: Power[x[j___], n_Integer] := MultiplyPower[x[j], n];

  x /: Conjugate[x] := x;
  x /: Conjugate[x[j___]] := x[j];
    
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
    Format[ x[j___,+1/2] ] :=
      DisplayForm @ SpeciesBox[x , {j,"\[UpArrow]"}, {}] /;
      $FormatSpecies;
    Format[ x[j___,-1/2] ] :=
      DisplayForm @ SpeciesBox[x , {j,"\[DownArrow]"}, {}] /;
      $FormatSpecies;
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

  Kind[x] ^= Heisenberg;
  Kind[x[___]] ^= Heisenberg;
  
  Top[x] ^= top;
  Top[x[___]] ^= top;

  Dimension[x] ^= 1 + top;
  Dimension[x[___]] ^= 1 + top;
  
  Dagger[x] ^= x;
  Dagger[x[j___]] ^:= x[j];

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

  Kind[x] ^= Fermion;
  Kind[x[___]] ^= Fermion;
  
  Dimension[x] ^= 2;
  Dimension[x[___]] ^= 2;
  
  x /: Conjugate[x] := x;
  x /: Conjugate[x[j___]] := x[j];
  
  x /: Power[x, n_Integer] := MultiplyPower[x, n];
  x /: Power[x[j___], n_Integer] := MultiplyPower[x[j], n];

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
      Spin[x[_,___,_]] ^= spin;
      Vacuum[x[_,___,_]] ^= vac;
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
    Format[ x[j___,+1/2] ] :=
      DisplayForm @ SpeciesBox[x , {j,"\[UpArrow]"}, {}] /;
      $FormatSpecies;
    Format[ x[j___,-1/2] ] :=
      DisplayForm @ SpeciesBox[x , {j,"\[DownArrow]"}, {}] /;
      $FormatSpecies;
   ];
 )

(* Override the default definition of Format[Dagger[...]] *)

Format[
  HoldPattern @ Dagger[c_Symbol?SpeciesQ[j___, Rational[1,2]]] /;
    Spin[c] == 1/2 ] :=
  DisplayForm @ SpeciesBox[c , {j,"\[UpArrow]"}, {"\[Dagger]"}] /;
  $FormatSpecies

Format[
  HoldPattern @ Dagger[c_Symbol?SpeciesQ[j___, Rational[-1,2]]] /;
    Spin[c] == 1/2 ] :=
  DisplayForm @ SpeciesBox[c , {j,"\[DownArrow]"}, {"\[Dagger]"}] /;
  $FormatSpecies


Majorana /:
Let[Majorana, {ls__Symbol}] := (
  Let[NonCommutative, {ls}];
  Scan[setMajorana, {ls}]
 )

setMajorana[x_Symbol] := (
  Kind[x] ^= Majorana;
  Kind[x[___]] ^= Majorana;
  
  MajoranaQ[x] ^= True;
  MajoranaQ[x[___]] ^= True;
  
  Dagger[x] ^= x;
  Dagger[x[j___]] ^:= x[j];
  
  x /: Conjugate[x] := x;
  x /: Conjugate[x[j___]] := x[j];

  x /: Power[x, n_Integer] := MultiplyPower[x, n];
  x /: Power[x[j___], n_Integer] := MultiplyPower[x[j], n];
 )


TrueSpin::usage = "TrueSpin[c[i,j,...]] returns Spin[c] if the Flavor indices i, j, ... are consistent with Spin[c]; otherwise returns 0 with a warning message. TrueSpin[c] always returns zero, wheather with or without warning message."

TrueSpin[ HoldPattern @ Dagger[c_?ParticleQ] ] := TrueSpin[c[]]

TrueSpin[ c_Symbol?ParticleQ ] := TrueSpin[c[]]
(* NOTICE the request through the form with extra [], instead of direct
   inspection with the Head itself. *)

TrueSpin[ op:c_Symbol?ParticleQ[j___] ] :=
  If[ Spin[op] === Spin[c],
    Spin[c],
    Message[Flavors::bad, {j}, c, Spin[c], Vacuum[c]];
    0
   ]


spinlessQ::usage = "spinlessQ[c[j,...]] returns True if the operator itself is spinless or if the Flavor indices are inconsistent although the operator itself is spinful."

spinfulQ::usage = "spinfulQ[c[j...]] returns True if the operator c has finite spin and the Flavor indices are consistent."

(* NOTE: Not[spinlessQ] != spinfulQ.  There are undetermined cases, which
   result in False for both. *)

spinlessQ[ op_?AnyParticleQ ] := If[ TrueSpin[op] == 0, True, False, True ]

spinfulQ[ op_?AnyParticleQ ] := TrueQ[ TrueSpin[op] > 0 ]


seaQ::usage = "seaQ[c[i,j,...]] returns True if Vacuum[c] is \"Sea\" and the Flavor indices i, j, ... are consistent. Note that seaQ[c] returns always False wheather with or withour warning message."

(* For a spinless (Spin = 0) Fermion to have the Sea vacuum, at least one
   Flavor index is required for the expected answer. Otherwise, in effect the
   vacuum of the operator is regarded to be Void.
   See also: CreatorQ[], AnnihilatorQ[] *)

(* For a spinful (Spin > 0) Fermion to have the Sea vacuum, at least two
   Flavor indices are required as the last index is expected to represent the
   spin component. Otherwise, in effect the vacuum of the operators is
   regarded to be Void.
   See also: CreatorQ[], AnnihilatorQ[] *)

seaQ[ HoldPattern @ Dagger[op_?FermionQ] ] := seaQ[op[]]

seaQ[ c_Symbol?FermionQ ] := seaQ[c[]]
(* NOTICE the test through the form with extra [], instead of direct test with
   the Head itself. *)

seaQ[ op:c_Symbol?FermionQ[j___] ] := (
  If[ Vacuum[op] =!= Vacuum[c],
    Message[Vacuum::invIdx, {j}, c, Spin[c], Vacuum[c]] ];
  Vacuum[op] == Vacuum[c] == "Sea"
 )

seaQ[_] = False


Missing["KeyAbsent", _?ParticleQ] := 0


OperatorQ::usage = "OperatorQ[c] returns True if c is any operator (Boson, Fermion, Heisenberg, or Majorana)."

AnyOperatorQ::usage = "AnyOperatorQ[c] returns True if c is a Boson, Fermion, Heisenberg, or Majorana operator with or without Dagger on it."

ParticleQ::usage = "ParticleQ[c] returns True if c is either a Bosonic or Fermionic operator (without Dagger on it); i.e., a normal particle distinguished from a Majorana Fermion, which is both particle and atni-particle."

AnyParticleQ::usage = "AnyParticleQ[c] returns True if c is either a bosonic or fermionic operaor with or without Dagger on it."

BosonQ::usage = "BosonQ[c] returns True if c is a bosonic operator (without Dagger on it)."

AnyBosonQ::usage = "AnyBosonQ[c] returns True if c is a bosonic operaor with or without Dagger on it."

HeisenbergQ::usage = "HeisenbergQ[c] returns True if c is a Heisenberg operator (without Canon on it)."

AnyHeisenbergQ::usage = "AnyHeisenbergQ[c] returns True if c is a Heisenberg operator with or without Cannon on it."

FermionQ::usage = "FermionQ[c] returns True if c is a fermionic operator. FermionQ[c[i, j, ...]] returns True if c[i, j, ...] is a fermionic operator (without Dagger on it)."

AnyFermionQ::usage = "AnyFermionQ[c] returns True if c is a fermionic operaor with or without Dagger on it."

MajoranaQ::usage = "MajoranaQ[z] returns True if z is a Majorana fermionic operator."

BosonQ[_] = False

HeisenbergQ[_] = False

FermionQ[_] = False

MajoranaQ[_] = False


OperatorQ[ _?HeisenbergQ | _?BosonQ | _?FermionQ | _?MajoranaQ ] = True

OperatorQ[_] = False


ParticleQ[ _?BosonQ | _?FermionQ ] = True

ParticleQ[_] = False


(* AnyBosonQ, AnyFermionQ, etc. *)
Scan[
  With[
    { anyQ = Symbol["Any" <> ToString[#]] },
    anyQ[Cannon[_?#]] = True;
    anyQ[HoldPattern @ Dagger[_?#]] = True;
    anyQ[_?#] = True;
    anyQ[_] = False;
   ] &,
  {OperatorQ, ParticleQ, HeisenbergQ, BosonQ, FermionQ}
 ]

AnySpeciesQ[ Cannon[_?HeisenbergQ] ] = True
(* Heisenberg's canonical conjugate is not very common, and was not defined in
   the Cauchy package. *)


Base[ op:c_Symbol?ParticleQ[j___,s_] ] := c[j] /; spinfulQ[op]

Base[ op_?OperatorQ ] := op


SpinZ::usage = "SpinZ[c[j,s]] returns the Spin Z quantum number s (i.e., the final spin index) of the operator c[j,s]."

SetAttributes[SpinZ, Listable]

SpinZ[ HoldPattern @ Dagger[c_?ParticleQ] ] := SpinZ[c]

SpinZ[ op:_Symbol?ParticleQ[___,s_] ] /; spinfulQ[op] = s 

SpinZ[ op_ ] = 0


(*** Canonical Conjugate ***)

Cannon::usage = "Cannon[x] denotes the canonical conjugate of a Heisenberg canonical operator x."

SetAttributes[Cannon, Listable]

Cannon[ Cannon[q_?HeisenbergQ] ] := q

Cannon /:
Kind[ Cannon[q_] ] := Kind[q]

Cannon /:
Dagger[ Cannon[q_?HeisenbergQ] ] := Cannon[q]

Cannon /: 
Format[ Cannon[c_Symbol?SpeciesQ[j___]] ] :=
  DisplayForm @ SpeciesBox[c, {j}, {"c"} ] /; $FormatSpecies

Cannon /: 
Format[ Cannon[ c_Symbol?SpeciesQ ] ] := 
    DisplayForm @ SpeciesBox[c, {}, {"c"} ] /; $FormatSpecies

(* Allows op^Cannon as a equivalent to Cannon[op] *)
Cannon /:
HoldPattern[ Power[expr_, Cannon] ] := Cannon[expr]


(*** CreatorQ[], AnnihilatorQ[] ***)

AnnihilatorQ::usage = "AnnihilatorQ[op[j]] returns 1 if op[j] is an annihilation operator and 0 otherwise."

CreatorQ::usage = "CreatorQ[op[j]] returns 1 if op[j] is a cration operator and 0 otherwise."

(* Bosons *)
AnnihilatorQ[HoldPattern @ Dagger[_?BosonQ]] = False

AnnihilatorQ[_?BosonQ] = True

CreatorQ[HoldPattern @ Dagger[_?BosonQ]] = True

CreatorQ[_?BosonQ] = False

(* Fermions with Void vacuum *)
AnnihilatorQ[HoldPattern @ Dagger[op:_?FermionQ]] /; !seaQ[op] = False

AnnihilatorQ[op:_?FermionQ] /; !seaQ[op]  = True

CreatorQ[HoldPattern @ Dagger[op:_?FermionQ]] /; !seaQ[op] = True

CreatorQ[op:_?FermionQ] /; !seaQ[op] = False

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



Bosons::usage = "Bosons[expr] gives the list of all Bosons appearing in expr."

Bosons[ expr_ ] :=
  Union @ Cases[ { Normal[expr, Association] }, _?BosonQ, Infinity ]
(* NOTE 1: The outermost { } is necessary around expr; otherwise,
   Bosons[S[1,2]] does not give the trivial result. *)
(* NOTE 2: Normal[{expr}, Association] is not enough as nested Association[]s
   are not converted properly. This is due to the HoldAllComplete Attribute of
   Association. *)

Fermions::usage = "Fermions[expr] gives the list of all Fermions appearing in expr."

Fermions[ expr_ ] :=
  Union @ Cases[ { Normal[expr, Association] }, _?FermionQ, Infinity ]

Heisenbergs::usage = "Heisenbergs[expr] gives the list of all Heisenbergs appearing in expr."

Heisenbergs[ expr_ ] :=
  Union @ Cases[ { Normal[expr, Association] }, _?HeisenbergQ, Infinity ]

Majoranas::usage = "Majoranas[expr] gives the list of all Majoranas appearing in expr."

Majoranas[ expr_ ] :=
  Union @ Cases[ { Normal[expr, Association] }, _?MajoranaQ, Infinity ]


FockFourier::usage = "FockFourier is OBSOLETE. Use ReplaceByFourier instead."

FockInverseFourier::usage = "FockInverseFourier is now obsolete. Use ReplaceByFourierInverse instead."

FockFourier[args__] := (
  Message[Notice::obsolete, "FockFourier", "ReplaceByFourier"];
  FourierMap[args]
 )

FockInverseFourier[args__] := (
  Message[Notice::obsolete, "FockInverseFourier", "ReplaceByFourierInvere"];
  InverseFourierMap[args]
 )


(*** Transformations between Dirac and Majorana Fermions ***)

FockDiracToMajorana::usage = "FockDiracToMajorana[expr, {c1,c2,...} -> {h1,h2,h3,h4,...}] converts expr writtten in Dirac fermion operators c1, c2, ... into an equivalent form in terms of the Majorana fermion operators h1, h2, h3, h4, ... via a suitable transformation between them. FockDiracToMajorana[expr, c1 -> {h1,h2}, c2->{h3,h4}, ...] is the same."

FockDiracToMajorana::incnst = "Inconsistent Dirac and Majorana fermion operators, `` and ``. There should be twice more Majorana fermion operators than Dirac fermion operators."

FockDiracToMajorana[expr_,
  rr:HoldPattern[
    {__?FermionQ} -> {PatternSequence[_?MajoranaQ, _?MajoranaQ]..}
   ]
 ] := Simplify[ expr //. rulesDiracToMajorana[rr] ]

FockDiracToMajorana[expr_,
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
  Message[FockDiracToMajorana::incnst, cc, hh];
  Return[{}]
 )


FockMajoranaToDirac::usage = "FockMajoranaToDirac[expr, {h1,h2,h3,h4,...} -> {c1,c2,...}] converts expr writtten in Dirac fermion operators c1, c2, ... into an equivalent form in terms of the Majorana fermion operators h1, h2, h3, h4, ... via a suitable transformation between them. FockMajoranaToDirac[expr, {h1,h2} -> c1, {h3,h4} -> c2, ...] is the same."

FockMajoranaToDirac::incnst = "Inconsistent Dirac and Majorana fermion operators, `` and ``. There should be twice more Majorana fermion operators than Dirac fermion operators."

FockMajoranaToDirac[expr_,
  rr:HoldPattern[
    {PatternSequence[_?MajoranaQ, _?MajoranaQ]..} -> {__?FermionQ}
   ]
 ] := Simplify[ expr //. rulesMajoranaToDirac[rr] ]

FockMajoranaToDirac[expr_,
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
  Message[FockMajoranaToDirac::incnst, cc, hh];
  Return[{}]
 )


FockHeisenbergToBoson::usage = "FockHeisenbergToBoson[expr, {x1, x2, ...} -> {a1, a2, ...}] converts expr writtten in canonical Heisenberg operators x1, x2, ... into an equivalent form in terms of the Boson operators a1, a2, ... via a suitable transformation between them. FockHeisenbergToBoson[expr, x1 -> a1, x2 -> a2, ...] is the same."

FockHeisenbergToBoson[expr_, rr:(_?HeisenbergQ -> _?BosonQ)..] :=
  Simplify[ expr //. rulesHeisenbergToBoson[rr] ]

FockHeisenbergToBoson[expr_, rr:({__?HeisenbergQ} -> {__?BosonQ})..] :=
  Simplify[ expr //. rulesHeisenbergToBoson[rr] ]

rulesHeisenbergToBoson[x_?HeisenbergQ -> a_?BosonQ] :=
  { Cannon[x] -> (a - Dagger[a]) / (I Sqrt[2]),
    x -> (a + Dagger[a]) / Sqrt[2] }

rulesHeisenbergToBoson[rr:(_?HeisenbergQ -> _?BosonQ)..] :=
  Flatten[ rulesHeisenbergToBoson /@ {rr}, 1 ]

rulesHeisenbergToBoson[rr:({__?HeisenbergQ} -> {__?BosonQ})] :=
  Apply[ rulesHeisenbergToBoson, Thread[rr] ]


FockBosonToHeisenberg::usage = "FockBosonToHeisenberg[expr, {x1, x2, ...} -> {a1, a2, ...}] converts expr writtten in canonical Heisenberg operators x1, x2, ... into an equivalent form in terms of the Boson operators a1, a2, ... via a suitable transformation between them. FockBosonToHeisenberg[expr, x1 -> a1, x2 -> a2, ...] is the same."

FockBosonToHeisenberg[expr_, rr:(_?BosonQ -> _?HeisenbergQ)..] :=
  Simplify[ expr //. rulesBosonToHeisenberg[rr] ]

FockBosonToHeisenberg[expr_, rr:({__?BosonQ} -> {__?HeisenbergQ})..] :=
  Simplify[ expr //. rulesBosonToHeisenberg[rr] ]

rulesBosonToHeisenberg[a_?BosonQ -> x_?HeisenbergQ] :=
  { a -> (x + I Cannon[x]) / Sqrt[2] }

rulesBosonToHeisenberg[rr:(_?BosonQ -> _?HeisenbergQ)..] :=
  Flatten[ rulesBosonToHeisenberg /@ {rr}, 1 ]

rulesBosonToHeisenberg[rr:({__?BosonQ} -> {__?HeisenbergQ})] :=
  Apply[ rulesBosonToHeisenberg, Thread[rr] ]


(* **************************************************************** *)
(*   <Conjugate>                                                    *)
(* **************************************************************** *)

Dagger /:
HoldPattern @ Conjugate @ Dagger[q_?OperatorQ] := Dagger[q]

Multiply /:
HoldPattern @ Conjugate[ Multiply[a_?AnyOperatorQ, b__?AnyOperatorQ] ] :=
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

CMT[op_, Cannon[op_]] := +I /; HeisenbergQ[op]

CMT[Cannon[op_], op_] := -I /; HeisenbergQ[op]

CMT[op_[j1___], Cannon[op_[j2___]]] := +I * KroneckerDelta[{j1},{j2}] /;
  HeisenbergQ[op]

CMT[Cannon[op_[j2___]], op_[j1___]] := -I * KroneckerDelta[{j1},{j2}] /;
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

HoldPattern @ ACMT[ op_, Dagger[op_] ] := 1 /; FermionQ[op]

HoldPattern @ ACMT[ Dagger[op_], op_ ] := 1 /; FermionQ[op]

HoldPattern @ ACMT[ op_[i___], Dagger[op_[j___]] ] :=
  KroneckerDelta[{i}, {j}] /; FermionQ[op]

ACMT[_?AnyFermionQ, _?AnyFermionQ] = 0
(* NOTE: Operators with different Heads are regarded different regardless of
   their Flavor indices. This is conventional. If you want to change this
   behavior, Multiply[] should also be modified accordingly. *)


(* ******************************************************************** *)
(*     <Multiply>                                                       *)
(* ******************************************************************** *)

(* Originally defined in Cauchy,
   Redefined for Fermion, Majorana, Grassmann *)
(* NOTE: _?AnySpeciesQ NOT _?AnyNonCommutativeQ.
   This is to handle Ket and Bra separately.
   Now __?AnyNonCommutativeQ to hanle Dyad. *)
HoldPattern @ Multiply[ops__?AnyNonCommutativeQ] := Module[
  { aa = Values @ KeySort @ GroupBy[{ops}, Kind],
    bb },
  bb = Multiply @@@ aa;
  bb = Multiply @@ bb;
  bb * fSignature[
    Cases[ {ops}, _?AnticommutativeQ ],
    Cases[ Flatten @ aa, _?AnticommutativeQ ]
   ]
 ] /;
  Not @ OrderedQ[ Kind @ {ops} ] /;
  NoneTrue[{ops}, ObscureQ]


fSignature::usage = "fSignature[a, b] returns the signature of the permutation that converts a to b for two expressions that differ only in the order of their arguments."
fSignature[a_, b_] := 
  Signature @ PermutationList @ FindPermutation[a, b] /;
  Length[a] == Length[b]


(** Heisenbergs **)

HoldPattern @
  Multiply[pre___, a:_?HeisenbergQ, b:Cannon[_?HeisenbergQ], post___] :=
  Multiply[pre, CMT[a, b], post] + Multiply[pre, b, a, post]

HoldPattern @
  Multiply[pre___, a:Cannon[_?HeisenbergQ], b:Cannon[_?HeisenbergQ], post___] :=
  Multiply[pre, b, a, post] /; Not @ OrderedQ[{a, b}]

HoldPattern @
  Multiply[pre___, a:_?HeisenbergQ, b:_?HeisenbergQ, post___] :=
  Multiply[pre, b, a, post] /; Not @ OrderedQ[{b, a}]
(* NOTE: Operators without Cannon are ordered in REVERSE canonical order. *)


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

HoldPattern @ Multiply[___, op_, op_, ___] := 0 /; FermionQ[op]

HoldPattern @ Multiply[___, Dagger[op_], Dagger[op_], ___] := 0 /; FermionQ[op]

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


(* Majoranas *)

HoldPattern @
  Multiply[pre___, op_, op_, post___] := 1/2 Multiply[pre, post] /;
  MajoranaQ[op]

HoldPattern @ Multiply[pre___, op_[i___], op_[j___], post___] :=
  Multiply[pre, post] KroneckerDelta[{i},{j}] -
  Multiply[pre, op[j], op[i], post] /;
  Not @ OrderedQ @ {op[i], op[j]} /;
  MajoranaQ[op]
(* NOTE: Operators with different Heads are regarded different regardless of
   their Flavor indices. This is conventional. If you want to change this
   behavior, Multiply[] should also be modified accordingly. *)

HoldPattern @ Multiply[pre___, op__?MajoranaQ, post___] :=
  Multiply[pre, Sequence @@ Sort @ {op}, post] Signature @ {op} /;
  Not @ OrderedQ @ {op}

(* ******************************************************************** *)
(*     </Multiply>                                                      *)
(* ******************************************************************** *)


Q::usage = "Q[c] is an alias to FockNumber[c], which is one of the most frequently used operator. Because the symbol N is reserved by the Mathematica system, we instead use Q."

Q = FockNumber

FockNumber::usage = "FockNumber[c] returns the number operator corresponding to the operator c. FockNumber[c1, c2, ...] returns the sumb of all FockNumber operators corresponding to operators c1, c2, ...."

FockNumber[ op_?ParticleQ ] := Multiply[ Dagger[op], op ]

FockNumber[x:({__?ParticleQ}|_?ParticleQ)..] := Total @ Map[FockNumber] @ Flatten @ {x}


Hop::usage = "Hop[a,b,...] is an alias to FockHopping[a,b,...]."

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

FockHopping[x_?VectorQ, b_?OperatorQ] := Sum[ FockHopping[a,b], {a, x} ]

FockHopping[a_?OperatorQ, y_?VectorQ] := Sum[ FockHopping[a,b], {b, y} ]

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


Pair::usage = "Pair[a,b,...] is an alias to FockPairing[a,b,...]."

Pair = FockPairing

FockPairing::usage = "FockPairing[a, b, c, ...] returns a**b + b**c + ..., describing the pair-annihilation process of a and b, b and c, and so on. One or more arguments can be a vector or matrix."

FockPairing[x__] := FockHopping[x] /. {Dagger -> Identity}


(*
S::usage = "S[dir][a,b,...] is an alias to FockSpin[a,b,..., dir]."

S[op__?ParticleQ] := FockSpin[op, {1,2,3}]

S[dir_][op__] := FockSpin[op, dir]

S[dir_, ddir__][op__] := FockSpin[op, {dir,ddir}]
*)

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



(* SS::usage = "SS[dir][a,b,...] is an alias to FockSpinSpin[a,b,..., dir]." *)

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


FockSpinor::usage = "FockSpinor[c] returns a list that is practically equal to c[All]. Dagger[FockSpinor[c]] forms a spherical irreducible tensor, whose order is Spin[c[Any]]."

FockSpinor[ cc_List ] := Flatten @ (FockSpinor /@ cc)

FockSpinor[ a_, b__ ] := FockSpinor[{a,b}]

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

FockDegree[_?AnyOperatorQ] = 1

FockDegree[_?CommutativeQ] = 0

FockDegree[expr_] := 0 /; FreeQ[expr, _?AnyOperatorQ]

(* MultiplyDegree for operators *)
MultiplyDegree[_?AnyOperatorQ] = 1


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
  Union @ Cases[ expr, _?OperatorQ | Cannon[_?HeisenbergQ], {0, Infinity} ]


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


(* To be called through FockExpand[expr, Method->"BakerHausdorff"] *)

(* Let[LinearMap, doExpandBakerHausdorff] *)

HoldPattern @ doExpandBakerHausdorff[
  Multiply[pre___, MultiplyExp[a_], b__, MultiplyExp[c_], post___]
 ] := Multiply[pre, LieExp[a, Multiply[b]], post] /;
  Garner[a + c] == 0

doExpandBakerHausdorff[expr_] := expr


(* ********************************************************************** *)

Once[
  $GarnerTests = Join[$GarnerTests, {AnyOperatorQ}];
  $RepresentableTests = Join[$RepresentableTests, {AnyParticleQ}];
 ]

(* ********************************************************************** *)


FockExpand::usage = "FockExpand[expr] expands expr including Fock space operators."

FockExpand::unknown = "Unknown expand method: ``. Basic is used."

$FockExpandMethods::usage = "$FockExpandMethods is an Association for the available FockExpand methods."


Options[FockExpand] = {Method->"Basic"}

$FockExpandMethods = Association[
  "BakerHausdorff" -> doExpandBakerHausdorff
 ]

FockExpand[expr_, opts___?OptionQ] := Module[
  { method },
  method = Method /. {opts} /. Options[FockExpand] /.
    { s_Symbol :> SymbolName[s],
      s_ :> ToString[s] };
  If[ !KeyExistsQ[$FockExpandMethods, method],
    Message[FockExpand::unknown, method];
    method = "Basic";
   ];
  $FockExpandMethods[method][expr]
 ]


(* ********************************************************************** *)
(* *** Fock Space ******************************************************* *)
(* ********************************************************************** *)

NullState::usage = "NullState refers to an impossible Fock-space vector in the creation-operator representation. It is denoted by Ket[Null]. The arising of NullState implies something is going wrong during the evaluation. Any operator on NullState simply returns NullState again."

HoldPattern @ Multiply[___, Ket[Null], ___] = Ket[Null]

HoldPattern @ Multiply[___, Bra[Null], ___] = Bra[Null]


(*** VacuumState and Vacuum Expectation Values ***)

VacuumState::usage = "VacuumState represents the vacuum state in the Fock space. It is denoted by Ket[{}]. It is the state that is annihilated by any annihilation operator."

HoldPattern @ Multiply[a___, op_?AnnihilatorQ, Ket[{}], b___] = 0 

HoldPattern @ Multiply[a___, Bra[{}], op_?CreatorQ, b___] = 0

HoldPattern @
  Multiply[___, op_?BosonQ, __?(FreeQ[#, Dagger[_?BosonQ]]&), Ket[{}], ___] := 0
(* Without this, because of the ordering policy, the bosonic annihilator may
   not directly see VacuumState when mixed with other types. *)

HoldPattern @
  Multiply[___, Bra[{}], __?(FreeQ[#, _?FermionQ]&), op_?AnyFermionQ, ___] :=
  0 /; CreatorQ[op]
(* Without this, because of the ordering polity, the fermionic creator may
   not directly see VacuumState when mixed with other types. *)

SurviveVacuum::usage = "SurviveVacuum[expr] drops vacuum-annihilating parts of expression expr."

SurviveVacuum[expr_] := Block[
  { saved },
  Multiply[ expr /. {Ket[{}] -> saved}, Ket[{}] ] /.
    {Ket[{}] -> 1, saved -> Ket[{}]}
 ]

VacuumExpectation::usage = "VacuumExpectation[expr] returns the vacuum expectation value of an operator expression.
  The option Method specifies the evaluation method: With
\"Algebra\" it uses the standard algebraic method and with \"Occupations\" using the Fock states Ket[<|...|>]."

SetAttributes[VacuumExpectation, Listable]

Options[VacuumExpectation] = { Method -> "Algebra" }

BraKet[{},{}] = 1 (* Bra[].Ket[] = 1 *)

VacuumExpectation[expr_, OptionsPattern[]] :=
  fVacuumExpectation[OptionValue[Method]][expr]

fVacuumExpectation["Algebra"][expr_] := Multiply[ Bra[{}], expr, Ket[{}] ]

fVacuumExpectation["Occupations"][expr_] := Multiply[ Bra[<||>], expr, Ket[<||>] ]


(* Odd number of operators *)

HoldPattern @ Multiply[Bra[{}], x__?AnyParticleQ, Ket[{}]] /; OddQ[Length @ {x}] = 0

(* Special rules for bosons *)

HoldPattern @ Multiply[ Bra[{}], __?BosonQ, Ket[{}] ] = 0

HoldPattern @ Multiply[ Bra[{}], Dagger[_?BosonQ].., Ket[{}] ] = 0

(* Special rules for Vacuum == "Sea" *)

(* (1-n_k) |0> *)
HoldPattern @
  Multiply[Bra[{}], a___, op:c_[k_,j___], Dagger[op:c_[k_,j___]], Ket[{}]] := 
  UnitStep[k] VacuumExpectation[Multiply[a]] /;
  FermionQ[c] && seaQ[op]
(* 2016-09-01 Can this case occur with Dagger[c] always pushed to the left? *)

(* <0| (1-n_k) *)
HoldPattern @
  Multiply[Bra[{}], op:c_[k_,j___], Dagger[op:c_[k_,j___]], b___, Ket[{}]] :=
  UnitStep[k] VacuumExpectation[Multiply[b]] /;
  FermionQ[c] && seaQ[op]
(* 2016-09-01 Can this case occur with Dagger[c] always pushed to the left? *)

(* n_k |0> *)
HoldPattern @
  Multiply[Bra[{}], a___, Dagger[op:c_[k_,j___]], op:c_[k_,j___], Ket[{}]] :=
  UnitStep[-k] VacuumExpectation[Multiply[a]] /;
j  FermionQ[c] && seaQ[op]

(* <0| n_k *)
HoldPattern @
  Multiply[Bra[{}], Dagger[op:c_[k_,j___]], op:c_[k_,j___], b___, Ket[{}]] :=
  UnitStep[-k] VacuumExpectation[Multiply[b]]  /;
  FermionQ[c] && seaQ[op]

(* Special rule for Spin = 1/2 and Vacuum == "Sea".
   Assumption: The vacuum has a well-defined particle number and spin
   z-compoenent. Otherwise, this rule gives a wrong result. *)

HoldPattern @ Multiply[Bra[{}], x__?electronQ, Ket[{}]] := Module[
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

HoldPattern @ Multiply[Bra[{}], a__?AnyParticleQ, Ket[{}]] /;
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
  Bra[{}],
  Dagger[x:a_Symbol?FermionQ[k1_,j1___]], y:a_[k2_,j2___],
  Ket[{}]
 ] := KroneckerDelta[k1,k2] * KroneckerDelta[{j1},{j2}] * UnitStep[-k1] /;
  seaQ[x] && seaQ[y]
(* NOTE: Operators with different Heads are assumed to be different
   operators. *)

(* For operators with NUMERIC Flavor indices, for which CreatorQ[] and
   AnnihilatorQ[] give definite answers. *)

HoldPattern @ Multiply[Bra[{}], ops__?AnyOperatorQ, Ket[{}]] := Module[
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

HoldPattern @ Multiply[Bra[{}], FockColon[_], Ket[{}]] = 0


(* ********************************************************************** *)

Displacement::usage = "Displacement[z, a] represents the displacement operator of the Bosonic mode a, where z is a complex number.\nDisplacement[\[Xi], c] for Fermion c, \[Xi] is a Grassmann number."

Displacement /: Peel[ Displacement[_, a_] ] := a (* for Matrix[] *)

Displacement /: Kind[ Displacement[_, a_] ] := Kind[a] (* for Multiply[] *)

Displacement /: AnySpeciesQ[ Displacement[_, a_] ] := AnySpeciesQ[a] (* for Multiply[] *)

HoldPattern @ Dagger[ Displacement[z_?CommutativeQ, a_?BosonQ] ] :=
  Displacement[-z, a]

Displacement[0, _?BosonQ] = 1

Displacement[z_, op:{__?BosonQ}] :=
  Multiply @@ Displacement @@@ Thread[{z, op}]

Displacement[zz_List, a_?BosonQ] := Displacement[#, a]& /@ zz

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


(* For Fermion,
   D(z) := Exp[ -z ** Dagger[c] + c ** Conjugate[z] ] *)

Displacement[z_?GrassmannQ, c_?FermionQ] := Multiply[
  1 - z ** Dagger[c],
  1 + c ** Conjugate[z],
  1 + z ** Conjugate[z] / 2
 ]

(* ********************************************************************** *)

CoherentState::usage = "CoherentState[c[k]->z] = Ket[c[k]->z] gives the coherent state of the operator c[k].  CoherentState is normalized to 1.  It is actually a place holder, but using FockExpand, you can represent it explicitly in terms of the creation and annihilation operator."

Format[ CoherentState[a_Association] ] := Ket[a]

Format[ HoldPattern @ Dagger[v_CoherentState] ] := Bra @@ v


coherentSpec = Alternatives[_?BosonQ->_?ComplexQ, _?FermionQ->_?GrassmannQ]

CoherentState[ op:coherentSpec.. ] := CoherentState[ CoherentState[<||>], op ]

CoherentState[ CoherentState[a_Association], op:coherentSpec.. ] := Module[
  { rules = Flatten @ KetRule @ {op} },
  (* Print["rules = ", rules]; *)
  CoherentState @ KeySort @ KetTrim @ Join[a, Association @ rules]
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

HoldPattern @
  Multiply[a___, op_?ParticleQ, CoherentState[v_Association], b___] := 
  Multiply[a, CoherentState[v], v[op], b] /; KeyExistsQ[v, op]
(* NOTE: v[op] can be a Grassmann variable *)

HoldPattern @ Multiply[a___, op_?ParticleQ, CoherentState[v_Association], b___] := 
  Multiply[a, CoherentState[v], op, b]

HoldPattern @ Multiply[a___, Dagger[CoherentState[v_Association]], Dagger[op_?ParticleQ], b___] := Multiply[a, Dagger[op ** CoherentState[v]], b]


HoldPattern @ Multiply[a___, Dagger[op_?ParticleQ], CoherentState[v_Association], b___] := 
  Multiply[a, CoherentState[v], Dagger[op], b] /; Not @ KeyExistsQ[v, op]

HoldPattern @ Multiply[a___, Dagger[CoherentState[v_Association]], op_?ParticleQ, b___] := 
  Multiply[a, op, Dagger[CoherentState[v]], b] /; Not @ KeyExistsQ[v, op]


(* To be called through FockExpand[expr, Method->"Basic"] *)
doExpandBasic[expr_] := expr //. {
  CoherentState[a_Association] :>
    ( Multiply @@
        Map[ Exp[-(#[[2]]**#[[2]])/2 + (Dagger[#[[1]]]**#[[2]])]& ] @
        Normal[a] ) ** Ket[{}]
 }
(* TODO: SqueezedState *)

AppendTo[ $FockExpandMethods,
  "Basic" -> Symbol[ Context[doExpandBasic] <> "doExpandBasic" ]
 ]


(* ********************************************************************** *)

FockAddSpin::usage = "FockAddSpin[c1, c2, ...] returns the irreducible basis of the total angular momentum S[c1] + S[c2] + ....
  FockAddSpin[] returns the trivial basis including only the VacuumState."

FockAddSpin[ ls:{(_?ParticleQ|_Association)...} ] :=
  FockAddSpin @@ Map[FockAddSpin] @ ls

FockAddSpin[] := Association[ {0,0} -> {Ket[{}]} ]

FockAddSpin[irb_Association] := irb

FockAddSpin[c_?ParticleQ] := Module[
  { cc = FockSpinor[c], irb },
  irb = Multiply[Dagger[#], Ket[{}]]& /@ GroupBy[cc, {TrueSpin[#], SpinZ[#]}&];
  (* NOTICE TrueSpin[#], not Spin[#]. This is a fallback for
     inconsistent Flavor indices, in which case SpinZ vanishes. *)
  Merge[{Association[{0,0} -> {Ket[{}]}], irb}, Catenate]
  (* NOTE: The following code does not work for Spinless case:
     Prepend[ irb, {0,0} -> {Ket[{}]} ]
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
    2]; SS = 
    Flatten[Map[Thread[{Sequence @@ #, Range[-Last@#, Last@#]}] &]@SS, 
      1];
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
    Multiply @@@ Tuples[{irb[{S1, m}], irc[{S2, Sz - m}]}]*
      ClebschGordan[{S1, m}, {S2, Sz - m}, {S, Sz}],
    {m, Range[min, max]}];
  new = Simplify @ Multiply[(new /. Ket[{}] -> 1), Ket[{}]];
  Association[ {S, Sz} -> new ]
 ]

trimIrreducibleBasis[irb_Association] := Module[
  { irc = Simplify @ Map[(#/FockNorm[#])&] @ irb },
  irc = Map[ DeleteDuplicates[#, Simplify @ Or[#1==#2, #1==-#2]&]& ] @ irc;
  irc
 ]


(*** Vectors in the Fock Space ***)

(* Ket := The occupation-number representation of a basis vector in the Fock space. *)
(* Cat := The creation-operator represenation of a basis vector in the Fock space.
   Hence, Cat is an multiplication of creators on VacuumState. *)

catQ[ Ket[{}] ] = True

catQ[ z_?ComplexQ Ket[{}] ] = True

catQ[ HoldPattern @ Multiply[__, Ket[{}]] ] = True

catQ[ z_?ComplexQ HoldPattern @ Multiply[__, Ket[{}]] ] = True

catQ[ z_?ComplexQ expr_ ] := catQ[expr]

catQ[ a_ + b_ ] := catQ[a] && catQ[b]

catQ[ _ ] = False


FockCat::usage = "FockCat[n1,n2,...] or equivalently FockCat[Ket[n1,n2,...] converts the occupation-number representation into the creation-operator representation, i.e., as a multiplication of a series of generators on the VacuumState."

FockCat[rr:(_?AnyParticleQ -> _Integer?NonNegative) ...] := toCatForm @ Ket[rr]

FockCat[rr:({__?AnyParticleQ} -> {__Integer?NonNegative})] := toCatForm @ Ket[rr]

FockCat[expr_] := toCatForm[expr] /; !FreeQ[expr, Ket]

FockCat[0] = 0


toCatForm::usage = "Returns a multiplication of generators (creation operators generating the Fock space basis) equivalent to the Fock state v in the occupation number representation."

Let[LinearMap, toCatForm]

SetAttributes[toCatForm, Listable]

toCatForm[ Ket[Null] ] = Ket[Null]

toCatForm[ Ket[v_Association] ] := Module[
  { cc = Keys @ v,
    nn = Values @ v },
  cc = MultiplyPower[Dagger @ cc, nn] / Sqrt[nn!];
  Multiply[ Multiply @@ cc, Ket[{}] ]
 ]


FockKet::usage = "FockKet[expr] converts FockCat[] form to Ket[] form. Recall that FockCat[] gives a Fock state with VacuumState is multiplied at the rightmost."

FockKet::badExpr = "`1` does not seem to represent a state vector in the Fock space, which in the creation-operator representation, takes the form of Dagger[c1]**Dagger[c2]**...**VacuumState."

FockKet[expr_] := toKetExpression[ expr ] /;
  !FreeQ[expr, Ket[{}] | Ket[<|___|>]]

FockKet[expr__] := (
  Message[FockKet::badExpr, {expr}];
  expr
 )

toKetExpression::usage = "Returns a Fock state in the occupation representation (Ket[<|c1->n1,c2->n2,...|>]) equivalent to expr, which is a multiplication of generators."

SetAttributes[toKetExpression, Listable]

Let[LinearMap, toKetExpression]

toKetExpression[ Ket[{}] ] := Ket[]

toFockKet[ Ket[Null] ] = Ket[Null]

toKetExpression[ v:Ket[_Association] ] := v

toKetExpression[ HoldPattern @ Multiply[expr__, Ket[{}]] ] := Module[
  {ops, val},
  {ops, val} = Transpose @ Tally @ {expr};
  ops = ops /. {Dagger->Identity};
  (Times @@ Sqrt[val!]) * Ket[ops -> val]
 ]


(* Ket for Fock *)

KetRule[ r:Rule[_?ParticleQ, _] ] := r

KetRule[ r:Rule[{__?ParticleQ}, _] ] := Thread[r]

KetTrim[_?ParticleQ, 0] = Nothing

VerifyKet[_?BosonQ, _?Negative] = 0

VerifyKet[_?FermionQ, b_] := 0 /; Or[ Negative[b], b > 1 ]
(* The following definition would not allow to assign a symbolic value:
   VerifyKet[ _?FermionQ, Except[0|1] ] = 0
 *)


(* Multiply for restricted Ket and Bra *)
HoldPattern @ Multiply[pre___, op_?AnyParticleQ, Ket[a_Association, b_List], post___] := With[
  { new = Restrict[ Multiply[op, Ket[a]], b ] },
  Multiply[pre, new, post]
 ] /; MemberQ[b, Peel @ op]


(* Operations on Ket[] *)

HoldPattern @ Multiply[x___, op_?BosonQ, Ket[v_Association], y___] := Module[
  { vv = v },
  vv[op] = v[op] - 1;
  Multiply[x, Sqrt[v[op]] * Ket[KetTrim @ vv], y]
 ] /; KeyExistsQ[v, op]

HoldPattern @ Multiply[x___, op_?BosonQ, Ket[v_Association], y___] := 0

HoldPattern @ Multiply[x___, Dagger[op_?BosonQ], Ket[v_Association], y___] := Module[
  { vv = v },
  vv[op] = v[op]+1;
  Multiply[x, Sqrt[v[op]+1] * Ket[vv], y]
 ] /; KeyExistsQ[v, op]

HoldPattern @ Multiply[x___, Dagger[op_?BosonQ], Ket[v_Association], y___] := Module[
  { vv = v },
  Multiply[x, Ket[ KeySort @ AssociateTo[vv, op->1] ], y]
 ]

HoldPattern @ Multiply[x___, op_?FermionQ, Ket[v_Association], y___] := Module[
  { sign },
  If[ v[op] == 0, Return[0] ];
  (* TODO: This doesn't respect fermions with Sea vacuum. *)
  sign = keySignature[v, op];
  Multiply[x, sign * Ket @ KeyDrop[v, op], y]
 ] /; KeyExistsQ[v, op]

HoldPattern @ Multiply[x___, op_?FermionQ, Ket[v_Association], y___] := 0

HoldPattern @ Multiply[x___, Dagger[op_?FermionQ], Ket[v_Association], y___] := Module[
  { vv = v, sign },
  If[ v[op] == 1, Return[0] ];
  (* TODO: This doesn't respect fermions with Sea vacuum. *)
  vv[op] = 1;
  sign = keySignature[v, op];
  Multiply[x, sign * Ket[vv], y]
 ] /; KeyExistsQ[v, op]

HoldPattern @ Multiply[x___, Dagger[op_?FermionQ], Ket[v_Association], y___] := Module[
  { vv = v,
    sign = keySignature[v, op] },
  If[ v[op] == 1, Return[0] ];
  (* TODO: This doesn't respect fermions with Sea vacuum. *)
  vv[op] = 1;
  Multiply[x, sign * Ket[vv], y]
 ] /; KeyExistsQ[v, op]

HoldPattern @ Multiply[x___, Dagger[op_?FermionQ], Ket[v_Association], y___] := Module[
  { vv = v, sign },
  vv = KeySort @ AssociateTo[vv, op->1];
  sign = keySignature[vv, op];
  Multiply[x, sign * Ket[vv], y]
 ]

HoldPattern @ Multiply[x___, Bra[v_Association], op_?AnyParticleQ, y___] :=
  Multiply[x, Dagger @ Multiply[ Dagger[op], Ket[v] ], y]

keySignature::usage = "Returns the signature for adding to or removing from the Ket a FERMION at the position j."

keySignature[v_Association, op_] := Module[
  { vv = KetTrim @ KeyDrop[ KeySelect[v, FermionQ], op ] },
  Signature[Join[{op}, Keys @ vv]]
 ]


FockNorm::usage = "FockNorm[v] returns the norm of the state v, which is either in the occupation number representation or in the creation-operator representation."

SetAttributes[FockNorm, Listable]

FockNorm[expr_] := Sqrt @ Multiply[Dagger @ expr, expr]

FockAvg::usage = "FockAvg[op, a] computes the braket <a|op|a>, where op is an operator expression and a is some state."

SetAttributes[FockAvg, Listable]

FockAvg[op_, a_] := Multiply[Dagger @ a, op, a]


FockMatrix::usage = "FockMatrix[op, vlist] computes the matrix elements of the operator op between the vectors in the list vlist. Vecotrs in vlist can be either in the Ket or Cat form (the latter is slightly more efficient. FockMatrix[op, vlist1, vlist2] calculates the matrix elements between two vectors, one from vlist1 and the other from vlist2. FockMatrix[op, basis] calculates the matrix elements between vectors in the basis 'basis'. The basis is a list with particular structure and can be constructed by FermionBasis."

Options[FockMatrix] = {DiagonalOnly -> True}

FockMatrix[op_, vv_List?VectorQ] := FockMatrix[op, vv, vv]

FockMatrix[op_, basis_Association, opts___?OptionQ] := Module[
  { only = DiagonalOnly /. {opts} /. Options[FockMatrix] },
  If[ only,
    diagonalBlocks[op, basis],
    allBlocks[op, basis]
   ]
 ]

FockMatrix[op_, vv1:{___?catQ}, vv2:{___?catQ}] :=
  Outer[ Multiply[#1, op, #2]&, Dagger @ toKetExpression @ vv1, toKetExpression @ vv2 ]
(* FockKet[] is much faster to evalculate *)

FockMatrix[op_, vv1_List?VectorQ, vv2:{___?catQ}] :=
  Outer[ Multiply[#1, op, #2]&, Dagger @ vv1, toKetExpression @ vv2 ]
(* FockKet[] is much faster to evalculate *)

FockMatrix[op_, vv1_List?VectorQ, vv2:{___?catQ}] :=
  Outer[ Multiply[#1, op, #2]&, Dagger @ vv1, toKetExpression @ vv2 ]
(* FockKet[] is much faster to evalculate *)

FockMatrix[op_, vv1:{___?catQ}, vv2_List?VectorQ] :=
  Outer[ Multiply[#1, op, #2]&, Dagger @ toKetExpression @ vv1, vv2 ]
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

$FockMatrixStyle::usage = "$FockMatrixStyle is a list of options of Grid that are used in FockMatrixForm to format the output of FockMatrix."

$FockMatrixStyle = {Frame -> True, Alignment -> Center}

Format[
  FockMatrixForm[mat:Association[({{___},{___}}->_?MatrixQ)..], title_String:""]
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
   
   Grid[bdy, Sequence @@ $FockMatrixStyle,
     Dividers -> {
       {2 -> True, Sequence @@ cnt},
       {2 -> True, Sequence @@ cnt}
      }
    ]
  ]

Format[
  FockMatrixForm[mat:Association[({___} -> _?MatrixQ)..], title_String:""]
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

   Grid[bdy, Sequence @@ $FockMatrixStyle,
     Dividers -> {
       {2 -> True, Sequence @@ cnt},
       {2 -> True, Sequence @@ cnt}
      }
    ]
  ]

matrixHeaders[qnn:{{___}..}, cnt:{___Integer}] := Module[
  {row, col},
  row = { Catenate @ MapThread[ PadRight[{#1}, #2, SpanFromLeft]&, {qnn, cnt} ] };
  col = Transpose @ (row /. SpanFromLeft -> SpanFromAbove);
  {row, col}
 ]

(* ******************************************************************** *)
(*     <Matrix>                                                         *)
(* ******************************************************************** *)

BuildMatrix[op_?AnyFermionQ, qq:{__?SpeciesQ}] := Module[
  { mm = Matrix[op],
    sp = FlavorMute @ Peel @ op,
    id, rr, ss },
  id = First @ FirstPosition[qq, sp];
  rr = qq[[ ;; id - 1]];
  ss = qq[[id + 1 ;; ]];

  rr = fermionOne /@ rr;
  ss = One /@ Dimension[ss];
  CircleTimes @@ Join[rr, {mm}, ss]
 ]

fermionOne[q_?FermionQ] := ThePauli[3]

fermionOne[q_] := One @ Dimension @ q


(*
AnticommutativeQ::usage = "AnticommutativeQ[c] returns True if c is an anticommutative Species such as Fermion, Majorana, and Grassmann, and False otherwise.\nIt is a low-level function intended to be used in Multiply and Matrix.\nIt affects how Multiply and Matrix manipulate expressions involving Fermion, Majorana, and Grassmann Species, which brings about a factor of -1 when exchanged."

SetAttributes[AnticommutativeQ, Listable]

AnticommutativeQ[op_?AnyFermionQ] = True

AnticommutativeQ[op_?MajoranaQ] = True

AnticommutativeQ[op_?GrassmannQ] = True

AnticommutativeQ[_] = False
*)


(* Matrix[] for Fermions *)

Matrix[ _?FermionQ ] := SparseArray[ {1,2}->1, {2, 2} ]

Matrix[ Parity[a_?FermionQ] ] :=
  SparseArray[ { {1,1} -> 1, {2,2} -> -1 }, {2, 2} ]

Matrix[ Ket[ Association[_?FermionQ -> n:(0|1)] ] ] :=
  SparseArray[ n+1 -> 1, 2 ]


(* Matrix[] for Bosons *)

Matrix[ a_?BosonQ ] := Module[
  { nn, ii, jj, rr },
  nn = Range[Bottom @ a, Top @ a];
  ii = Most @ nn - Bottom[a] + 1;
  jj = Rest @ nn - Bottom[a] + 1;
  rr = MapThread[ Rule, { Transpose @ {ii, jj}, Sqrt @ Rest @ nn } ];
  SparseArray[ rr, {1, 1} (1+Top[a]-Bottom[a]) ]
 ]

Matrix[ Parity[a_?BosonQ] ] := Module[
  { jj = Range[Bottom @ a, Top @ a],
    pp },
  pp = Power[-1, jj];
  jj = jj - Bottom[a] + 1;
  SparseArray @ Thread[ Transpose @ {jj, jj} -> pp ]
 ]

Matrix[ Ket[ Association[a_?BosonQ -> n_Integer] ] ] := SparseArray[
  If[ Bottom[a] <= n <= Top[a], (1+n-Bottom[a])->1, {}, {} ],
  Dimension[a]
 ]

(* ******************************************************************** *)
(*     </Matrix>                                                        *)
(* ******************************************************************** *)


(* ************************************************************************** *)

(* Basis[] for fermions *)

(* Simple construction of basis for fermions; see FermionBasis for more
   elaborate constructions. *)

Basis[c_?FermionQ] := Ket /@ Thread[ c->{0, 1} ]

Basis[cc:{__?FermionQ}] := Map[ Ket[cc->#]&, Tuples[{0, 1}, Length@cc] ]

(* Basis[] for bosons *)

Basis[b_?BosonQ] := Ket /@ Thread[ b->Range[Bottom@b, Top@b] ]

Basis[bb:{__?BosonQ}] := Map[
  Ket[bb->#]&,
  Tuples [ Range @@@ Transpose @ {Bottom /@ bb, Top /@ bb} ]
 ]

(* ******************************************************************** *)

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


ParityEvenQ[v_Ket, a_?ParticleQ] := EvenQ @ v @ a

ParityOddQ[v_Ket, a_?ParticleQ] := OddQ @ v @ a

(* ******************************************************************** *)

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

BosonBasis[bb:{__?BosonQ}, {n_Integer}] := 
  Ket /@ Counts /@ Union[ Sort /@ Tuples[bb, n] ]


FermionBasis::usage = "FermionBasis[c1, c2, ...] or FermionBasis[{c1, c2, ...}] returns the many-particle basis states (in the creation operators representation) for a single site, i.e. for operators c1, c2, .... It accepts two options Representation and Conserved."

FermionBasis::bigSpin = "Sorry, but for the moment, it can handle only spin-1/2 Fermion operators. These operators will be ignored: ``."

Representation::usage = "Representation is an option of FermionBasis. It can be either \"Occupations\" (default) or \"Generators\"."

Conserved::usage = "Conserved is an option of FermionBasis, specifying the conserved quantities. It can be either None or any combination of Spin, SpinZ, and Number."

Options[FermionBasis] = {
  Representation -> "Occupations",
  Conserved -> {"Number", "Spin"}
 }

(* Basic constructions *)

FermionBasis[cc__?FermionQ, n_Integer] := FermionBasis[{cc}, n]

FermionBasis[cc__?FermionQ, {m_Integer, n_Integer}] :=
  FermionBasis[{cc}, {m, n}]

FermionBasis[cc__?FermionQ, {n_Integer}] := FermionBasis[{cc}, {n}]

FermionBasis[cc:{__?FermionQ}, n_Integer] :=
  Ket @@@ Map[Thread[#->1]&] @ Subsets[cc, n]

FermionBasis[cc:{__?FermionQ}, {m_Integer, n_Integer}] :=
  Flatten @ Table[ FermionBasis[cc, {k}], {k, m, n}]

FermionBasis[cc:{__?FermionQ}, {n_Integer}] := 
  Ket @@@ Map[Thread[#->1]&] @ Subsets[cc, {n}]


(* Advanced constructions*)

FermionBasis[cc__?FermionQ, opts___?OptionQ] := FermionBasis[{cc}, opts]

FermionBasis[{cc__?FermionQ}, opts___?OptionQ] := Module[
  {rep, qn, name},
  {rep, qn} = {Representation, Conserved} /. {opts} /. Options[FermionBasis];

  rep = rep /.
    { s_Symbol :> SymbolName[s],
      s_ :> ToString[s] } /.
    { "Occupations" -> "Ket",
      "Generators" -> "Cat",
      _ -> "Cat" };
  
  qn = If[ AtomQ[qn], {qn}, Sort[qn] ];
  qn = StringJoin @ Map[
    ( # /. { s_Symbol :> SymbolName[s], s_ :> ToString[s] } )&,
    qn
   ];
  
  name = StringJoin[Context[name], "basis", rep, qn];
  If[ NameQ[name], Symbol[name][cc], {{}->{}} ]
 ]


BasisForm::usage = "BasisForm[bs] prints the basis bs in table form. Note that a basis is a list of particular structure."

$BasisStyle::usage = "$BasisStyle is a list of options of Grid that are used in BasisForm to format bases."

Format[ BasisForm[bs_Association] ] :=
  Grid[ Normal[bs] /. {Rule -> List}, $BasisStyle ]

$BasisStyle = {
  Frame -> False,
  Alignment -> {{Center, {Left}}, Center},
  Dividers -> {{}, {True, {Dashed}, True}}
 }


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


basisKetNumberSpinZ::usage = "basisKetNumberSpinZ[{ops}] returns the basis with well defined charge and spin projection quantum numbers (Q,S_z) in occupation number representation."

basisCatNumberSpinZ::usage = "basisCatNumberSpinZ[{ops}] returns the basis with well defined charge and spin projection quantum numbers (Q,S_z) in creation operator representation."

(* Make a basis of good quantum numbers Q and S_z. This is trivially done in
   the occupation number representation Ket[...]. *) 

basisKetNumberSpinZ[ops__?FermionQ] := Module[
  { cc = FockSpinor[ops], nn, z },
  z = SpinZ[cc];
  nn = Tuples[{0, 1}, Length @ cc];
  nn = GroupBy[nn, {Total@#, z.#}&];
  KeySort @ Map[Ket[cc->#]&, nn, {2}]
 ]

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
  irb = Map[GroupBy[#, (List@FockDegree@#) &] &, irb];
  irb = KeyValueMap[KeyMap[Function[key, Flatten@{key, #1}], #2] &, 
    irb];
  irb = KeySort@Merge[irb, Catenate]
 ]

basisKetNumberSpin[cc__?FermionQ] := FockKet @ basisCatNumberSpin[cc]


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


FockColon::usage = "FockColon[expr] denotes the normal ordering of the operators in expr.
    This is merely a placeholder, although its output is displayed with double dots surrounding expr. To explicitly evaluate the normal ordered expression, use NormalOrder function."

Let[LinearMap, FockColon]

FockColon[] = 1

Format[ FockColon[op__] ] := DisplayForm @ RowBox[{ RowBox[
      { Style["\[Colon]", FontColor -> Red], op, 
        Style["\[Colon]", FontColor -> Red] }
     ]} ]
(* NOTE: The outer RowBox is to avoid spurious parentheses around the Multiply
   expression. For example, without it, -2 :f**f: is formated as
   -2(:f f:). For more details on spurious parentheses, see
   https://goo.gl/MfCwMF *)


Protect[ Evaluate @ $symbs ]

End[]


Q3`Fock`Private`symbs = Protect[Evaluate[$Context<>"*"]]

SetAttributes[Evaluate[Q3`Fock`Private`symbs], ReadProtected]

EndPackage[]
