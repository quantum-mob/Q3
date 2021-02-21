(* -*- mode: math; -*- *)

BeginPackage["Q3`Wigner`", { "Q3`Pauli`", "Q3`Cauchy`", "Q3`" } ]

Unprotect[Evaluate[$Context<>"*"]]

Begin["`Private`"]
`Version = StringJoin[
  $Input, " v",
  StringSplit["$Revision: 1.23 $"][[2]], " (",
  StringSplit["$Date: 2021-02-21 16:23:24+09 $"][[2]], ") ",
  "Mahn-Soo Choi"
 ];
End[]

{ TheWigner, TheWignerKet };

{ Spin, SpinQ, Spins };

{ WignerSpinSpin };

{ WignerKetQ };

{ WignerReduced, WignerFactor };

{ WignerDecompose, WignerCompose,
  WignerCoefficients,
  WignerExpression };

{ WignerAdd, WignerAddZ };

{ WignerCoherent };

{ WignerRotation, WignerEulerRotation };

{ WignerDistributionW,
  WignerDistributionC };

{ ClebschGordanTable, PrintTable };

{ NineJSymbol, WignerEckart };

{ WignerExpand }; (* obsolete *)


Begin["`Private`"]

$symbs = Unprotect[
  Multiply, MultiplyDegree, CircleTimes,
  KetRule, KetTrim, Ket, Bra, Spin, Missing,
  Basis, Matrix,
  Base, FlavorNone, FlavorMute,
  $GarnerHeads, $GarnerTests,
  $ElaborationRules, $ElaborationHeads,
  $RepresentableTests, $RaiseLowerRules,
  TheRotation, TheEulerRotation
 ]


(* TheWigner, like ThePauli in Pauli package *)

TheWigner::usage = "TheWigner[{J,k}] returns the matrix representation of the angular momentum operator of magnitude J in the k'th direction.\nTheWigner[{J,k,theta,phi}] = U.TheWigner[{J,k}].Topple[U] returns the matrix representation in the rotated frame.\nTheWigner[{J1,k1},{J2,k2},...] returns TheWigner[{J1,k1}] \[CircleTimes] TheWigner[{J2,k2}] \[CircleTimes] ...\nTheWigner[{J, {k1,k2,...}, th, ph}] = TheWigner[{J,k1,th,ph}, {J,k2,th,ph}, ...]."

TheWigner[{J_?SpinNumberQ, 0}] := SparseArray @ IdentityMatrix[2J+1]

TheWigner[{J_?SpinNumberQ, 1}] := (TheWigner[{J,4}]+TheWigner[{J,5}])/2

TheWigner[{J_?SpinNumberQ, 2}] := (TheWigner[{J,4}]-TheWigner[{J,5}])/(2I)

TheWigner[{J_?SpinNumberQ, 3}] := SparseArray @ DiagonalMatrix @ Range[J,-J,-1]

TheWigner[{J_?SpinNumberQ, 4}] := SparseArray @ With[
  { v = Table[Sqrt[J(J+1)-M(M+1)], {M, J, -J, -1}] },
  RotateLeft[ DiagonalMatrix[v] ]
 ]

TheWigner[{J_?SpinNumberQ, 5}] := SparseArray @ With[
  { v = Table[Sqrt[J(J+1)-M(M-1)], {M, J, -J, -1}] },
  RotateRight[ DiagonalMatrix[v] ]
 ]

TheWigner[{J_?SpinNumberQ, Raise}] := TheWigner[{J,4}]

TheWigner[{J_?SpinNumberQ, Lower}] := TheWigner[{J,5}]

TheWigner[{J_?SpinNumberQ, s_ -> t_}] := SparseArray[
  {J+1 - t, J+1 - s} -> 1,
  {2*J+1, 2*J+1}
 ]

TheWigner[{J_?SpinNumberQ, 0, theta_, phi_}] := TheWigner[{J,0}]

TheWigner[{J_?SpinNumberQ, n:(1|2|3), theta_, phi_}] := With[
  { R = EulerMatrix[{phi, theta, 0}] },
  TheWigner[{J, 1}]*R[[1, n]] + TheWigner[{J, 2}]*R[[2, n]] + TheWigner[{J, 3}]*R[[3, n]]
 ]

TheWigner[ nn:{_?SpinNumberQ, (0|1|2|3|4|5|6|Raise|Lower)}.. ] :=
  CircleTimes @@ Map[TheWigner] @ {nn}

TheWigner[ { j_?SpinNumberQ, n:{(0|1|2|3|4|5|6|Raise|Lower)..} } ] :=
  CircleTimes @@ Map[TheWigner] @ Tuples[{{j}, n}]

TheWigner[ { j_?SpinNumberQ, n:{(0|1|2|3|4|5|6|Raise|Lower)..},
    th:Except[_List], ph:Except[_List] } ] :=
  CircleTimes @@ Map[TheWigner] @ Tuples[{{j}, n, {th}, {ph}}]


TheWignerKet::usage = "TheWignerKet[{J,M,th,ph}] is the rotated-frame version of TheWignerKet[{J,M}].\nTheWignerKet[{j1,m1,t1,p1}, {j2,m2,t2,p2}, ...] returns CircleTimes of the vectors  indicated by the indices.\nTheWignerKet[{J, {m1,m2,...}, th, ph}] = TheWignerKet[{J,m1,th,ph}, {J,m2,th,ph}, ...]."

TheWignerKet[ {J_,M_} ] := UnitVector[2J+1,J-M+1] /; SpinNumberQ[J,M]

TheWignerKet[ {j_?SpinNumberQ, m:{__?NumericQ}} ] := TheWignerKet @@ Tuples[{{j},m}]

TheWignerKet[ a:{_?SpinNumberQ, _?NumericQ} .. ] := Module[
  { aa = Transpose@{a}, jj,
    pwrs, bits, p},
  jj = 2 First[aa] + 1;
  pwrs = Reverse @ FoldList[ Times, 1, Reverse @ Rest @ jj ];
  bits = Subtract @@ aa;
  p = 1 + bits.pwrs;
  Normal @ SparseArray[ {p -> 1}, Times @@ jj ]
 ]

TheWignerKet[ {J_, M_, theta:Except[_List], phi:Except[_List]} ] :=
  TheEulerRotation[{J,phi,theta,0}] . TheWignerKet[{J,M}] /;
  SpinNumberQ[J,M]

TheWignerKet[ a:{Repeated[Except[_List],{4}]}, b:{Repeated[Except[_List],{4}]}.. ] :=
  CircleTimes @@ Map[TheWignerKet, {a, b}]
(* NOTE: TheWignerKet[a:{Repeated[Except[_List],{4}]..}] is dangerous for bad inputs
   like {1/2,0,Pi/2,Pi/2}. *)
  
TheWignerKet[ {j_?SpinNumberQ, m:{__?NumericQ}, t:Except[_List], p:Except[_List]} ] :=
  CircleTimes @@ Map[TheWignerKet] @ Tuples[{{j}, m, {t}, {p}}]


Once[ TheRotation::usage = TheRotation::usage <> "\nTheRotation[\[Phi], {J, 1}], TheRotation[\[Phi], {J, 2}], TheRotation[\[Phi], {J, 3}] give the rotation matrices by angle \[Phi] around the x, y, and z axis, respective, for Spin = J." ]

TheRotation[_, {_?SpinNumberQ, 0}] := IdentityMatrix[2*J+1]

TheRotation[phi_, {J_?SpinNumberQ, n:(1|2|3)}] :=
  MatrixExp[ -I phi TheWigner[{J, n}] ]

TheRotation[{phi_, {J_?SpinNumberQ, n:(1|2|3)}}] :=
  TheRotation[phi, {J, n}]

TheRotation[
  a:{_, {_?SpinNumberQ, (0|1|2|3)}},
  b:{_, {_?SpinNumberQ, (0|1|2|3)}}.. ] :=
  CircleTimes @@ Map[TheRotation, {a, b}]


Once[ TheEulerRotation::usage = TheEulerRotation::usage <> "\nTheEulerRotation[{a, b, c}, J] gives the Euler rotation matrix in the angular momentum J representation." ]

TheEulerRotation[ {phi_, theta_, chi_}, J_?SpinNumberQ ] :=
  TheRotation[phi, {J, 3}] . TheRotation[theta, {J, 2}] .
  TheRotation[chi, {J, 3}]

TheEulerRotation[{{a_, b_, c_}, J_?SpinNumberQ}] :=
  TheEulerRotation[{a, b, c}, J]

TheEulerRotation[
  a:{{_, _, _}, _?SpinNumberQ},
  b:{{_, _, _}, _?SpinNumberQ}.. ] :=
  CircleTimes @@ Map[TheEulerRotation, {a, b}]


Spin::wrongS = "Wrong spin value ``. Spin should be a non-negative integer or half-integer. Spin 1/2 is assumed."

Options[Spin] = {Spin->1/2}

SetAttributes[Spin, Listable]

Spin /:
Let[Spin, {ls__Symbol}, opts___?OptionQ] := Module[
  { spin },
  spin = Spin /. {opts} /. Options[Spin];
  
  If[ !SpinNumberQ[spin],
    Message[Spin::wrongS, spin];
    spin = 1/2;
   ];
  
  Let[NonCommutative, {ls}];
    
  Scan[setSpin[#,spin]&, {ls}];
 ]

setSpin[x_Symbol, spin_?SpinNumberQ] := (
  Kind[x] ^= Spin;
  Kind[x[___]] ^= Spin;
  
  Dimension[x] ^= 2 spin + 1;
  Dimension[x[___]] ^= 2 spin + 1;

  SpinQ[x] ^= True;
  SpinQ[x[___]] ^= True;

  Spin[x] ^= spin;
  Spin[x[___]] ^= spin;
  x[___,Spin] = spin;

  x/: Dagger[ x[j___,k:(0|1|2|3|6)] ] := x[j,k];
  x/: Dagger[ x[j___,4] ] := x[j,5];
  x/: Dagger[ x[j___,5] ] := x[j,4];

  x /: Power[x, n_Integer] := MultiplyPower[x, n];
  x /: Power[x[j___], n_Integer] := MultiplyPower[x[j], n];

  x[j___,Raise] := x[j,1] + I x[j,2];
  x[j___,Lower] := x[j,1] - I x[j,2];
  
  x[j___,Hadamard] := MultiplyExp[-I (Pi/2) x[j,2]] ** x[j,3] / spin;
  (* NOTE: For Spin-1/2, this is enough to reduce it to (X+Z)/Sqrt[2].
     See Cauchy.m for Exp[ (Clifford- or Grassmann-like elements) ] .*)
  
  x[j___,All] := Flatten @ x[j,{1,2,3}];

  x[j___,Null] := x[j,None];

  x[j___, None, k_] := x[j,k];
  (* In particular, x[j,None,None] = x[j,None]. *)
  
  Format[ x[j___,None] ] := SpeciesBox[x, {j}, {}];

  Format[ x[j___,0] ] := SpeciesBox[x, {j}, {0}];
  Format[ x[j___,1] ] := SpeciesBox[x, {j}, {"x"}];
  Format[ x[j___,2] ] := SpeciesBox[x, {j}, {"y"}];
  Format[ x[j___,3] ] := SpeciesBox[x, {j}, {"z"}];
  Format[ x[j___,4] ] := SpeciesBox[x, {j}, {"+"}];
  Format[ x[j___,5] ] := SpeciesBox[x, {j}, {"-"}];
  Format[ x[j___,6] ] := SpeciesBox[x, {j}, {"H"}];
 )

Missing["KeyAbsent", S_Symbol?SpinQ[___, None]] := Spin[S]


SpinQ::usage = "SpinQ[J] or SpinQ[J[...]] returns True if J is declared as a Spin operator."

SpinHalfQ::usage = "SpinHalfQ[J] or SpinHalfQ[J[...]] returns True if J is a Spin operator and its Spin is 1/2."

SpinQ[_] = False

SpinHalfQ[J_Symbol?SpinQ] := Spin[J]==1/2

SpinHalfQ[J_Symbol?SpinQ[k___]] := Spin[J[k]]==1/2

SpinHalfQ[_] = False


Spins::usage = "Spins[expr] gives the list of all Spins appearing in expr."

Spins[ expr_ ] := FlavorNone @ Union @ Map[Most] @
  Cases[ { expr /. {Association->List} }, _?SpinQ, Infinity ]
(* NOTE 1: The outermost { } are necessary around expr; otherwise, it does not
   give the trivial result. *)
(* NOTE 2: Normal[{expr}, Association] does not convert nested Association[]s;
   i.e., Association[ ... Association[] ...]. This is due to HoldAllComplete
   Attribute of Association. *)


(* Multiply *)

(* Speical Rules: Involving identity *)

HoldPattern @ Multiply[a___, x_?SpinQ[j___,0], x_?SpinQ[j___,n_], b___] := Multiply[a, x[j,n], b]

HoldPattern @ Multiply[a___, x_?SpinQ[j___,n_], x_?SpinQ[j___,0], b___] := Multiply[a, x[j,n], b]
(* Conceptually this one is not required as it can be deduced from the
   commutation relations below. But this makes the evaluation faster when
   Multiply involves many Spin operators. *)


(* Special Rules: Spin = 1/2 *)
 
HoldPattern @ Multiply[
  a___,
  x_Symbol?SpinHalfQ[j___,k:(1|2|3|6)], x_Symbol?SpinHalfQ[j___,k:(1|2|3|6)],
  b___ ] := (1/4) Multiply[a, b]

HoldPattern @ Multiply[
  a___,
  x_Symbol?SpinHalfQ[j___,k:(4|5)], x_Symbol?SpinHalfQ[j___,k:(4|5)],
  b___ ] := 0

HoldPattern @ Multiply[ a___, x_Symbol?SpinHalfQ[j___,1], x_Symbol?SpinHalfQ[j___,2], b___ ] :=
  Multiply[a, I/2 x[j,3], b]

HoldPattern @ Multiply[ a___, x_Symbol?SpinHalfQ[j___,2], x_Symbol?SpinHalfQ[j___,3], b___ ] :=
  Multiply[a, I/2 x[j,1], b]

HoldPattern @ Multiply[ a___, x_Symbol?SpinHalfQ[j___,3], x_Symbol?SpinHalfQ[j___,1], b___ ] :=
  Multiply[a, I/2 x[j,2], b]

HoldPattern @ Multiply[ a___, x_Symbol?SpinHalfQ[j___,2], x_Symbol?SpinHalfQ[j___,1], b___ ] :=
  Multiply[a, -I/2 x[j,3], b]

HoldPattern @ Multiply[ a___, x_Symbol?SpinHalfQ[j___,3], x_Symbol?SpinHalfQ[j___,2], b___ ] :=
  Multiply[a, -I/2 x[j,1], b]

HoldPattern @ Multiply[ a___, x_Symbol?SpinHalfQ[j___,1], x_Symbol?SpinHalfQ[j___,3], b___ ] :=
  Multiply[a, -I/2 x[j,2], b]
(* Again, the last three definitions can be deduced from the commutation
   relations below, but explicit definition makes the evaluation much
   faster. *)

(* fundamental commutation relations for AM *)

CMT[J_?SpinQ[j___,1], J_?SpinQ[j___,2]] := I J[j,3]

CMT[J_?SpinQ[j___,2], J_?SpinQ[j___,3]] := I J[j,1]

CMT[J_?SpinQ[j___,3], J_?SpinQ[j___,1]] := I J[j,2]

CMT[J_?SpinQ[j___,2], J_?SpinQ[j___,1]] := -I J[j,3]

CMT[J_?SpinQ[j___,3], J_?SpinQ[j___,2]] := -I J[j,1]

CMT[J_?SpinQ[j___,1], J_?SpinQ[j___,3]] := -I J[j,2]

(* J[j,4] = Raising; J[j,5] = Lowering *)

CMT[J_?SpinQ[j___,1], J_?SpinQ[j___,4]] := - J[j,3]

CMT[J_?SpinQ[j___,1], J_?SpinQ[j___,5]] := + J[j,3]

CMT[J_?SpinQ[j___,4], J_?SpinQ[j___,1]] := + J[j,3]

CMT[J_?SpinQ[j___,5], J_?SpinQ[j___,1]] := - J[j,3]

CMT[J_?SpinQ[j___,2], J_?SpinQ[j___,4]] := -I * J[j,3]

CMT[J_?SpinQ[j___,2], J_?SpinQ[j___,5]] := -I * J[j,3]

CMT[J_?SpinQ[j___,4], J_?SpinQ[j___,2]] := +I * J[j,3]

CMT[J_?SpinQ[j___,5], J_?SpinQ[j___,2]] := +I * J[j,3]

CMT[J_?SpinQ[j___,3], J_?SpinQ[j___,4]] := + J[j,4]

CMT[J_?SpinQ[j___,3], J_?SpinQ[j___,5]] := - J[j,5]

CMT[J_?SpinQ[j___,4], J_?SpinQ[j___,3]] := - J[j,4]

CMT[J_?SpinQ[j___,5], J_?SpinQ[j___,3]] := + J[j,5]

CMT[J_?SpinQ[j___,4], J_?SpinQ[j___,5]] := +2 J[j,3]

CMT[J_?SpinQ[j___,5], J_?SpinQ[j___,4]] := -2 J[j,3]

(* Hadamard *)

CMT[J_?SpinQ[j___,6], J_?SpinQ[j___,1]] :=
  Exp[-I (Pi/2) J[j,2]] ** ( I J[j,2] + (J[j,1]-J[j,3])**J[j,3] ) / Spin[J]
(* Exp[] is pushed to the left; see Cauchy *)

CMT[J_?SpinQ[j___,6], J_?SpinQ[j___,2]] :=
  -I Exp[-I (Pi/2) J[j,2]] ** J[j,1] / Spin[J]
(* Exp[] is pushed to the left; see Cauchy *)

CMT[J_?SpinQ[j___,6], J_?SpinQ[j___,3]] :=
  Exp[-I (Pi/2) J[j,2]] ** (J[j,1] + J[j,3]) ** J[j,3] / Spin[J]
(* Exp[] is pushed to the left; see Cauchy *)


CMT[_?SpinQ, _?SpinQ] = 0


(* General Rules *)

HoldPattern @ Multiply[a___, x1_?SpinQ, x2_?SpinQ, b___] :=
  Multiply[a, CMT[x1,x2], b] + Multiply[a, x2, x1, b] /;
  Not @ OrderedQ @ {x1, x2}

(* Wigner on Ket *)

(* Multiply for restricted Ket and Bra *)
HoldPattern @ Multiply[ x___, a_?SpinQ, Ket[b_Association, c_List], y___ ] := With[
  { new = Restrict[ Multiply[a, Ket[b]], c ] },
  Multiply[x, new, y]
 ] /; MemberQ[c, FlavorMute @ a]


HoldPattern @ Multiply[ x___, a_?SpinQ[j___,0], Ket[b_Association], y___ ] :=
  Multiply[ x, Ket[b], y ]

HoldPattern @ Multiply[ x___, a_?SpinQ[j___,4], Ket[b_Association], y___ ] := Module[
  { J = Spin[a], M = b[a[j,None]], v },
  v = Sqrt[J(J+1)-M(M+1)] Ket[ KetTrim @ ReplacePart[b, Key[a[j,None]]->M+1] ];
  Multiply[ x, v, y ]
 ] /; KeyExistsQ[b, a[j,None]]

HoldPattern @ Multiply[ x___, a_?SpinQ[j___,4], Ket[b_Association], y___ ] := 0

HoldPattern @ Multiply[ x___, a_?SpinQ[j___,5], Ket[b_Association], y___ ] := Module[
  { J = Spin[a], M = b[a[j,None]], v },
  v = Sqrt[J(J+1)-M(M-1)] Ket[ KetTrim @ ReplacePart[b, Key[a[j,None]]->M-1] ];
  Multiply[ x, v, y ]
 ] /; KeyExistsQ[b, a[j,None]]

HoldPattern @ Multiply[ x___, a_?SpinQ[j___,5], Ket[b_Association], y___ ] := Module[
  { J = Spin[a], v },
  v = Sqrt[J(J+1)-J(J-1)] Ket[ KeySort @ Append[b, a[j,None]->J-1]];
  Multiply[ x, v, y ]
 ]

HoldPattern @ Multiply[ x___, a_?SpinQ[j___,1], Ket[b_Association], y___ ] := Module[
  { J = Spin[a], M = b[a[j,None]], v },
  v = 1/2 Sqrt[J(J+1)-M(M-1)] Ket[ KetTrim @ ReplacePart[b, Key[a[j,None]]->M-1] ] +
      1/2 Sqrt[J(J+1)-M(M+1)] Ket[ KetTrim @ ReplacePart[b, Key[a[j,None]]->M+1] ];
  Multiply[ x, v, y ]
 ] /; KeyExistsQ[b, a[j,None]]

HoldPattern @ Multiply[ x___, a_?SpinQ[j___,1], Ket[b_Association], y___ ] := Module[
  { J = Spin[a], v },
  v = 1/2 Sqrt[J(J+1)-J(J-1)] Ket[ KeySort @ Append[b, a[j,None]->J-1]];
  Multiply[ x, v, y ]
 ]

HoldPattern @ Multiply[ x___, a_?SpinQ[j___,2], Ket[b_Association], y___ ] := Module[
  { J = Spin[a], M = b[a[j,None]], v },
  v = I/2 Sqrt[J(J+1)-M(M-1)] Ket[ KetTrim @ ReplacePart[b, Key[a[j,None]]->M-1] ] -
      I/2 Sqrt[J(J+1)-M(M+1)] Ket[ KetTrim @ ReplacePart[b, Key[a[j,None]]->M+1] ];
  Multiply[ x, v, y ]
 ] /; KeyExistsQ[b, a[j,None]]

HoldPattern @ Multiply[ x___, a_?SpinQ[j___,2], Ket[b_Association], y___ ] := Module[
  { J = Spin[a], v },
  v = I/2 Sqrt[J(J+1)-J(J-1)] Ket[ KeySort @ Append[b, a[j,None]->J-1] ];
  Multiply[ x, v, y ]
 ]

HoldPattern @ Multiply[ x___, a_?SpinQ[j___,3], Ket[b_Association], y___ ] :=
  b[a[j,None]] Multiply[x, KetTrim @ Ket[b], y]


Once[
  $RepresentableTests = Join[$RepresentableTests, {SpinQ}];

  $GarnerTests = Join[$GarnerTests, {SpinQ}];
  
  $ElaborationRules = Join[
    $ElaborationRules,
    { G_?SpinQ[j___,0] -> 1,
      G_?SpinQ[j___,4] -> G[j, Raise],
      G_?SpinQ[j___,5] -> G[j, Lower],
      G_?SpinQ[j___,6] -> G[j, Hadamard]
     }
   ];
 ]


(* MultiplyDegree for operators *)
MultiplyDegree[_?SpinQ] = 1


(* Base: See Cauchy *)

Base[ S_?SpinQ[j___, _] ] := S[j]
(* For Spins, the final Flavor index is special. *)


(* FlavorNone: See Cauchy package *)

FlavorNone[S_?SpinQ] := S[None]

FlavorNone[S_?SpinQ -> m_] := S[None] -> m


(* FlavorMute: See Cauchy *)

FlavorMute[S_Symbol?SpinQ] := S[None]

FlavorMute[S_Symbol?SpinQ[j___, _]] := S[j, None]

FlavorMute[S_Symbol?SpinQ[j___, _] -> m_] := S[j, None] -> m


(* KetTrim / See Pauli *)

KetTrim[S_?SpinQ, m_] := Nothing /; Spin[S] == m


(* KetRule / See Pauli *)

KetRule[ r:Rule[_?SpinQ, _] ] := FlavorNone[r]

KetRule[ r:Rule[{__?SpinQ}, _] ] := FlavorNone @ Thread[r]


WignerKetQ::usage = "WignerKetQ[v] varifies the Ket v."

Ket::badQN = "Bad spin quantum numbers `1`."

WignerKetQ[ Ket[a_Association] ] := Module[
  { tf = KeyValueMap[ SpinNumberQ[Spin[#1],#2]&, a ] },
  If[ And @@ tf,
    Return[True],
    Message[ Ket::badQN, Pick[ Normal @ a, tf, False ] ];
    Return[False]
   ]
 ]

(* ****************************************************************** *)

Basis[ S_?SpinQ ] := Basis @ {S}

Basis[ ss:{__?SpinQ} ] := Module[
  { tt = Union @ FlavorNone[ss],
    dims, bits },
  dims = Map[Spin, tt];
  bits = Map[Range[#, -#, -1]&, dims];
  Map[ Ket[tt->#]&, Tuples @ bits ]
 ]

(* ****************************************************************** *)

WignerFactor::usage = "WignerFactor[expr, S] or WignerFactor[expr, {S1,S2,...}] factors the Ket expression expr."

Let[LinearMap, WignerFactor];

WignerFactor[Ket[a_Association], S_?SpinQ] := WignerFactor[Ket[a], {S}]

WignerFactor[Ket[a_Association], S : {__?SpinQ}] := Module[
  { SS = FlavorNone[S] },
  OSlash[Ket[KeyTake[a, SS]], Ket[KeyDrop[a, SS]]]
 ]


WignerReduced::usage = "WignerReduced[v, {s1, s2, ...}] constructs the reduced density matrix corresponding to the pure state v of Spins s$1, s$2, ... ."

WignerReduced[v_, S_?SpinQ] :=
  wReduced @ WignerFactor[ Expand @ v, {S} ]

WignerReduced[v_, S : {__?SpinQ}] :=
  wReduced @ WignerFactor[ Expand @ v, S ]

wReduced[ OSlash[a_Ket, b_] ] :=
  Multiply[a, Dagger[a]] * Conjugate[ Dagger[b] ** b ]

wReduced[ expr_Plus ] := Module[
  { vv = List @@ expr,
    aa, bb },
  { aa, bb } = Transpose[vv /. {OSlash -> List}];
  aa = Flatten@Outer[Multiply, aa, Dagger[aa]];
  bb = Flatten@Outer[ Multiply, Dagger[bb], bb];
  Conjugate[bb].aa
 ]


(* ****************************************************************** *)

(* Matrix[] for Wigner *)

Matrix[S_?SpinQ[___,j_]] := TheWigner @ {Spin[S], j}

Matrix[ Ket[ Association[S_?SpinQ -> m_] ] ] := TheWignerKet @ {Spin[S], m}

(* ****************************************************************** *)


WignerSpinSpin::usage = "WignerSpinSpin[dir][S1, S2, ...] returns the sum of exchange couplings between Spins S1, S2, ... for components specified by dir."

WignerSpinSpin[All][ss__] := WignerSpinSpin[{1,2,3}][ss]

WignerSpinSpin[dir:(1|2|3|{(1|2|3)..})][ss__] := Module[
  { tt = FlavorNone @ {ss},
    links },
  links = Chain @@ tt;
  Total[ wSpinSpin[dir] /@ links ]
 ] /; And @@ SpinQ /@ Flatten @ {ss}

wSpinSpin[dir:(1|2|3)][a_ -> b_] := a[dir] ** b[dir]

wSpinSpin[dir:{(1|2|3)..}][a_ -> b_] := MultiplyDot[a[dir], b[dir]]


(* ****************************************************************** *)

WignerAddZ::usage = "WignerAddZ[J1, J2, ...] returns in an Association the irreducible basis of the total angular momentum J1 + J2 + ... invariant under the U(1) rotation around spin z-axis."

WignerAddZ::duplicate = "Duplicate angular momentum operators appear."


WignerAddZ[ ls:{(_?SpinQ|_Association)..} ] :=
  WignerAddZ @@ Map[WignerAddZ] @ ls

WignerAddZ[] := Association[ {0} -> {Ket[]} ]

WignerAddZ[irb_Association] := irb

WignerAddZ[a_?SpinQ] := Module[
  { aa = FlavorNone @ a,
    bs = Basis @ a },
  GroupBy[bs, #[aa]&]
 ]

WignerAddZ[a___, b_?SpinQ, c___] := WignerAddZ[a, WignerAddZ[b], c]

WignerAddZ[irb_Association, irc_Association, ird__Association] :=
  WignerAddZ[ WignerAddZ[irb, irc], ird]

WignerAddZ[irb_Association, irc_Association] := Module[
  { kk = Flatten@Outer[Plus, Keys[irb], Keys[irc]],
    vv = Map[Tuples]@Tuples[{Values[irb], Values[irc]}],
    gb = Union @ Cases[Normal @ Values @ irb, _?SpinQ, Infinity],
    gc = Union @ Cases[Normal @ Values @ irc, _?SpinQ, Infinity],
    rr },
  If[ ContainsAny[gb, gc],
    Message[ WignerAddZ::duplicate ];
    Return[ irb ]
   ];

  vv = Apply[CircleTimes, vv, {2}];
  rr = Thread[kk -> vv];
  rr = Merge[rr, Catenate];
  Map[ReverseSort, rr]
 ]

WignerAdd::usage = "WignerAdd[J1, J2, ...] returns in an Association the irreducible basis of the total angular momentum J1 + J2 + ...."

WignerAdd::duplicate = "Duplicate angular momentum operators appear."

WignerAdd[ ls:{(_?SpinQ|_Association)..} ] :=
  WignerAdd @@ Map[WignerAdd] @ ls

WignerAdd[] := Association[ {0,0} -> {Ket[]} ]

WignerAdd[irb_Association] := irb

WignerAdd[a_?SpinQ] := Module[
  { aa = FlavorNone @ a,
    bs = Basis @ a },
  GroupBy[bs, {Spin[aa], #[aa]}&]
 ]

WignerAdd[a___, b_?SpinQ, c___] := WignerAdd[a, WignerAdd[b], c]

WignerAdd[irb_Association, irc_Association, ird__Association] :=
  WignerAdd[ WignerAdd[irb, irc], ird]

WignerAdd[irb_Association, irc_Association] := Module[
  { S1 = Union@Map[First]@Keys[irb],
    S2 = Union@Map[First]@Keys[irc],
    SS,
    gb = Union @ Cases[Normal @ Values @ irb, _?SpinQ, Infinity],
    gc = Union @ Cases[Normal @ Values @ irc, _?SpinQ, Infinity],
    new },
  If[ ContainsAny[gb, gc],
    Message[ WignerAdd::duplicate ];
    Return[ irb ]
   ];
  SS = Flatten[
    Outer[Thread[{#1, #2, Range[Abs[#1 - #2], #1 + #2]}]&, S1, S2], 
    2];
  SS = Flatten[
    Map[Thread[{Sequence @@ #, Range[-Last@#, Last@#]}]&] @ SS,
    1];
  new = doWignerAdd[irb, irc, #] & /@ SS;
  Merge[new, Catenate]
 ]

doWignerAdd[irb_, irc_, {S1_, S2_, S_, Sz_}] := Module[
  { new, min, max },
  min = Max[-S1, Sz - S2, (Sz - (S1 + S2))/2];
  max = Min[S1, Sz + S2, (Sz + (S1 + S2))/2];
  new = Sum[
    CircleTimes @@@ Tuples[{irb[{S1, m}], irc[{S2, Sz - m}]}]*
      ClebschGordan[{S1, m}, {S2, Sz - m}, {S, Sz}],
    {m, Range[min, max]}];
  Association[ {S, Sz} -> new ]
 ]


WignerRotation::usage = "WignerRotation[angle, S[j, ..., k]] operates the rotation by angle around the axis k on the Spin S[j, ..., None].\nWignerRotation[angle, S, {x, y, z}] gives the rotation operator by angle around the axis {x, y, z} on the Spin S."

WignerRotation[phi_, S_?SpinQ[j___,k:(1|2|3)]] := Module[
  { bs = Basis[ S[j, None] ],
    Rn = MatrixExp[ -I phi TheWigner[{Spin[S], k}] ] },
  Inner[Dyad, bs.Rn, bs]
 ]

WignerRotation[phi_, S_?SpinQ[j___, None], v:{_,_,_}] := Module[
  { bs = Basis[ S[j, None] ],
    vn = v / Norm[v],
    Rn },
  Rn = vn . {
    TheWigner[{Spin[S], 1}],
    TheWigner[{Spin[S], 2}],
    TheWigner[{Spin[S], 3}] };
  Rn = MatrixExp[ -I phi Rn ];
  Inner[Dyad, bs.Rn, bs]
 ]

WignerRotation[phi_, S_?SpinQ, v:{_,_,_}] :=
  WignerRotation[ phi, S[None], v] /;
  FlavorLast[S] =!= None


WignerEulerRotation::usage = "WignerEulerRotation[{a, b, c}, S] returns the Euler rotation operator acting on the spin S."

WignerEulerRotation[{a_, b_, c_}, S_?SpinQ] := Multiply[
  WignerRotation[a, S[3]],
  WignerRotation[b, S[2]],
  WignerRotation[c, S[3]]
 ]

(* ***************
   Special Topics
   *************** *)

WignerDecompose::usage = "WignerDecompose[v] gives the Pauli decomposition of the density matrix for the PURE state v for Spin=1/2 particles."

WignerDecompose::badSpin = "WignerDecompose[] supports only Spin-1/2 particles."

WignerDecompose[v_] := With[
  { ss = Union @ Cases[Normal[v, Association], _?SpinQ, Infinity] },
  WignerDecompose[v, Length[ss]]
 ]

WignerDecompose[v_, n_Integer] :=
  Join @@ Table[ WignerDecompose[v,{k}], {k, 0, n} ]

WignerDecompose[v_, {0}] := Module[
  { ss = Union @ Cases[Normal[v, Association], _?SpinQ, Infinity] },
  Association[ {1} -> 1 / Power[2, Length[ss]] ]
 ]

WignerDecompose[v_, {n_Integer}] := Module[
  { ss = Union @ Cases[Normal[v, Association], _?SpinQ, Infinity],
    jj, kk, op, vv, nS },
  nS = Length[ss];
  ss = Subsets[ss, {n}];
  kk = Outer[List, Sequence @@ Table[{1, 2, 3}, {n}]];
  op = Table[
    Map[ ( Multiply @@ MapThread[Construct, {jj, #}] )&, kk, {n} ],
    {jj, ss}
   ];
  vv = Dagger[v]**op**v / Power[2,nS-n];
  Association[ Thread[ss->vv] ]
 ]

WignerCompose::usage = "WignerCompose[a] constructs the operator expression in terms of spin operators. The association a is usually generated by WignerDecompose[]."

WignerCompose::badSpin = "WignerCompose[] supports only Spin-1/2 particles."

WignerCompose[ a_Association ] := Total @ KeyValueMap[ WignerCompose, a ]

WignerCompose[ {1}, m_ ] := m

WignerCompose[ ss:{__?SpinQ}, m_List ] := Module[
  { kk, op, vv, nL },
  nL = Length[ss]; (* the level of Wigner decomposition *)
  kk = Outer[List, Sequence @@ Table[{1, 2, 3}, {nL}]];
  op = Map[ ( Multiply @@ MapThread[Construct, {ss, #}] )&, kk, {nL} ];
  vv = Power[2,nL] * (op * m);
  Total @ Flatten[vv]
 ]


WignerExpression::usage = "WignerExpression[m] gives the operator expression for the matrix representation m.\nWignerExpression[v] gives the Ket expression for the vector representation v."

(* Let[LinearMap, WignerExpression] *)
(* NOTE: Where there are many terms, larger than 512?,
   strange $RecursionLimit::reclim2 error occurs.*)

WignerExpression[ expr_ ] := ReplaceAll[
  LogicalForm @ expr,
  Multiply[ a:Ket[_Association], b:Bra[_Association] ] :> WignerExpression[a,b]
 ]

WignerExpression[ Ket[a_Association], Bra[b_Association] ] :=
  Multiply @@ Thread[ WignerExpression[Normal@a, Normal@b] ]

WignerExpression[S_?SpinQ ->  1/2, S_?SpinQ ->  1/2] := 1/2 + S[3]

WignerExpression[S_?SpinQ -> -1/2, S_?SpinQ -> -1/2] := 1/2 - S[3]

WignerExpression[S_?SpinQ ->  1/2, S_?SpinQ -> -1/2] := S[Raise]

WignerExpression[S_?SpinQ -> -1/2, S_?SpinQ ->  1/2] := S[Lower]

WignerExpression::incon = "Inconsistent matrix and spin-operators list."

(* At the moment, only for Spin 1/2 *)
WignerExpression[ m_?MatrixQ, s:{__?SpinQ} ] := Module[
  { nL = Log[2, Length[m]],
    mm = Tensorize[m],
    ss, op },

  If[ nL != Length[s],
    Message[WignerExpression::incon];
    Return[0]
   ];
  
  ss = Map[
    Function[ {S},
      { {1/2+S[3], S[Raise]},
        {S[Lower], 1/2-S[3]} } ],
    s ];
  op = Outer[ Multiply, Sequence @@ ss ];
  Total @ Flatten[mm * op]
 ]

WignerExpression[m_?MatrixQ, S_?SpinQ] := WignerExpression[m, {S}]

WignerExpression[v_?VectorQ, j:{__?SpinQ}] := Module[
  { jj = Map[Spin] @ j,
    ss = FlavorNone @ j,
    basis },
  If[ Length[v] != Times @@ (2jj+1),
    Message[WignerExpression::incon];
    Return[{0}]
   ];
  basis = Basis[ss];
  Dot[ v, basis ]
 ]

WignerExpression[v_?VectorQ, S_?SpinQ] := WignerExpression[v, {S}]


WignerExpand::usage = "WignerExpand[expr] expands the expression expr revealing the explicit forms of various operator or state-vector expressions."

WignerExpand[expr_] := (
  Message[Q3General::obsolete, WignerExpand, Elaborate];
  Elaborate[expr]
 )


WignerCoefficients::usage = "WignerCoefficients[expr] gives the Pauli decomposition of the density matrix by finding the coefficients to the operators."

WignerCoefficients[op_] := With[
  { ss = Union @ Map[Most] @ Cases[op, _?SpinQ, Infinity] },
  WignerCoefficients[op, Length[ss]]
 ]

WignerCoefficients[op_, n_Integer] :=
  Join @@ Table[ WignerCoefficients[op, {k}], {k, 0, n} ]

WignerCoefficients[op_, {0}] := Module[
  { ss = Union @ Map[Most] @ Cases[op, _?SpinQ, Infinity] },
  Association[ {1} -> 1 / Power[2, Length[ss]] ]
 ]

WignerCoefficients[op_, {n_Integer}] := Module[
  { ss = Union @ Map[Most] @ Cases[op, _?SpinQ, Infinity],
    kk, cc },
  ss = Subsets[ss, {n}];
  kk = Map[ (#[{1,2,3}])&, ss, {2} ];
  ss = Map[ (#[None])&, ss, {2} ];
  cc = Map[ CoefficientTensor[op, Sequence @@ #]&, kk ];
  cc /= Power[2, n];
  Association[ Thread[ss->cc] ]
 ]


WignerCoherent::usage = "WignerCoherent[S, th, ph] gives the spin coherent state."

WignerCoherent[S_?SpinQ, 0, ph_] := Ket[S -> Spin[S]]

WignerCoherent[S_?SpinQ, Pi, ph_] := Ket[S -> -Spin[S]]

WignerCoherent[S_?SpinQ, th_, ph_] := Module[
  { J = Spin[S],
    sin = Sin[th]/2,
    cot = Cot[th/2],
    basis = Basis[{S}] },
  
  cc = Table[
    Sqrt[Binomial[2 J, J + m]] * cot^m * Exp[-I*ph*(J+m)],
    {m, J, -J, -1} ];
  
  Power[sin, J] * Dot[cc, basis]
 ]


(*
 * Wigner distribution function W
 * See Pezze et al (2018a, Section II.D.2).
 *)
WignerDistributionW::usage = "WignerDistributionW[th, ph,v] returns the Wigner distribution function W."

WignerDistributionW[th_, ph_, v_List] := Module[
  { J = (Length[v]-1)/2,
    YY, CG, rho },
  Off[ClebschGordan::phy];
  YY = Table[ SphericalHarmonicY[K, l, th, ph], {K, 0, 2*J}, {l, K, -K, -1}];
  YY = Flatten @ YY;
  CG = Table[
    (-1)^(J - n)*ClebschGordan[{J, m}, {J, -n}, {K, l}],
    {m, J, -J, -1},
    {n, J, -J, -1},
    {K, 0, 2 J},
    {l, K, -K, -1} ];
  CG = Flatten[CG, {{1}, {2}, {3, 4}}];
  rho = TensorContract[ TensorProduct[ Conjugate[v], v, CG ], {{1,3}, {2,4}} ];
  On[ClebschGordan::phy];
  Return[ rho . YY ];
 ]

(*
 * Wigner distribution function W
 * See Pezze et al (2018a, Section II.C.3).
 *)
WignerDistributionC::usage = "WignerDistributionC[th, ph] gives the distribution function C(\[Theta],\[Phi]) = \[LeftAngleBracket]\[Theta],\[Phi]|\[Psi]\[RightAngleBracket], where \[VerticalSeparator]\[Theta],\[Phi]\[RightAngleBracket] is the coherent spin state."

WignerDistributionC[th_, ph_, v_List] := Module[
  { J = (Length[v]-1)/2,
    cos = Cos[th/2],
    sin = Sin[th/2],
    YY },
  YY = Table[ Exp[I m ph] *
    Sqrt[(2J)!/((J+m)!(J-m)!)] *
    Power[cos, J+m] Power[sin, J-m],
    {m, J, -J, -1} ];
  Abs[ YY . v ]^2
 ]


(* ********************************************************************** *)

ClebschGordanTable::usage = "ClebschGordanTable[j1,j2] returns the matrix of the Clebsch-Gordan coefficients."

PrintTable::usage = "PrintTable is an option of ClebschGordanTable. If True, the table is printed."

Options[ClebschGordanTable] = { PrintTable -> True }

ClebschGordanTable[ j1_?SpinNumberQ, j2_?SpinNumberQ,
  opts___?OptionQ
 ] := Module[
   { JJ = Range[j1+j2, Abs[j1-j2], -1],
     JM, printQ },

   printQ = PrintTable /. {opts} /. Options[ClebschGordanTable];

   JM = Catenate @ Map[momentumStates] @ JJ;
   cg = Quiet[
     Outer[ ClebschGordan,
       momentumStates[j1], momentumStates[j2], JM,
       1 ],
     ClebschGordan::phy
    ];
   cg = Flatten[cg, 1];
   
   If[ printQ, printCG[j1, j2, cg] ];
   
   Return[ cg ]
  ]

printCG[j1_, j2_, cg_] := Module[
  { JJ = Range[j1+j2, Abs[j1-j2], -1], JM,
    m1 = Range[j1, -j1, -1],
    m2 = Range[j2, -j2, -1], m1m2,
    jj, mm, table },

  (* Header row *)
  JM = Catenate @ Map[momentumStates] @ JJ;
  JM = { Apply[Ket, JM, {1}] }; (* 1 x N matrix *)
  
  (* Header column *)
  m1m2 = Tuples @ {m1, m2};
  m1m2 = Transpose @ { Apply[Bra, m1m2, {1}] }; (* N x 1 matrix *)
  
  (* The whole table *)
  table = ArrayFlatten[{
      { {{""}}, JM },
      { m1m2, cg }
     }];
  
  (* Dividers *)
  jj = 2 + Accumulate @ Map[2*#+1&] @ Most @ JJ;
  jj = Thread[ Rule[jj, Dashed] ];
  mm = 2 + Accumulate @ ConstantArray[2*j2+1, 2*j1];
  mm = Thread[ Rule[mm, Dashed] ];
  
  Print @ Grid[
    table,
    Frame -> True,
    Dividers -> {
      Catenate @ { {2->True}, jj },
      Catenate @ { {2->True}, mm }
     }
   ];
 ]

momentumStates[J_?SpinNumberQ] := Thread[{J, Range[J,-J,-1]}]


NineJSymbol::usage = "NineJSymbol[{j1,j2,j3}, {j4,j5,j6},{j7,j8,j9}] gives the Wigner 9j-symbol."

(* Special cases with one of J's is zero, in which case the Nine-J symbol is related to the Six-J symbol. *)

NineJSymbol[
  {j1_,  j2_,  j12_},
  {j3_,  j4_,  j34_},
  {j13_, j24_,  0 }
 ] :=
  KroneckerDelta[j12,j34] *
  KroneckerDelta[j13,j24] *
  Power[-1, j2+j3+j12+j13] / Sqrt[(2*j12+1)(2*j13+1)] *
  SixJSymbol[{j1,j2,j12}, {j4,j3,j13}]

NineJSymbol[
  {j1_, j2_, j3_},
  {j4_, j5_,  0 },
  {j7_, j8_, j9_}] :=
  NineJSymbol[
    {j7, j8, j9},
    {j1, j2, j3},
    {j4, j5, 0 }]

NineJSymbol[
  {j1_, j2_,  0 },
  {j4_, j5_, j6_},
  {j7_, j8_, j9_}] :=
  NineJSymbol[
    {j4, j5, j6},
    {j7, j8, j9},
    {j1, j2, 0 }]

NineJSymbol[
  {j1_, j2_, j3_},
  {j4_,  0 , j6_},
  {j7_, j8_, j9_}] :=
  NineJSymbol[
    {j9, j7, j8},
    {j3, j1, j2},
    {j6, j4, 0 }]

NineJSymbol[
  { 0 , j2_, j3_},
  {j4_, j5_, j6_},
  {j7_, j8_, j9_}] := 
  NineJSymbol[
    {j9, j6, j3},
    {j8, j5, j2},
    {j7, j4, 0 }]

NineJSymbol[
  {j1_,  0 , j3_},
  {j4_, j5_, j6_},
  {j7_, j8_, j9_}] := 
  NineJSymbol[
    {0 , j3, j1},
    {j5, j6, j4},
    {j8, j9, j7}]

NineJSymbol[
  {j1_, j2_, j3_},
  {j4_, j5_, j6_},
  {j7_,  0 , j9_}] := 
  NineJSymbol[
    {j3, j1, j2},
    {j6, j4, j5},
    {j9, j7, 0 }]

NineJSymbol[
  {j1_, j2_, j3_},
  {j4_, j5_, j6_},
  { 0 , j8_, j9_}] := 
  NineJSymbol[
    {j2, j3, j1},
    {j5, j6, j4},
    {j8, j9, 0 }]

NineJSymbol[
  {j1_, j2_, j3_},
  { 0 , j5_, j6_},
  {j7_, j8_, j9_}] := 
  NineJSymbol[
    {0 , j5, j6},
    {j7, j8, j9},
    {j1, j2, j3}]

(* General case *)

NineJSymbol[
  {j1_,  j2_,  j12_},
  {j3_,  j4_,  j34_},
  {j13_, j24_, j_} ] := Simplify @ Sum[
    (-1)^(2*g)*(2*g+1) *
      SixJSymbol[{j1,j2,j12}, {j34,j,g}] *
      SixJSymbol[{j3,j4,j34}, {j2,g,j24}] *
      SixJSymbol[{j13,j24,j}, {g,j1,j3}], 
    { g,
      Max[Abs[j1-j], Abs[j2-j34], Abs[j3-j24]], 
      Min[j1+j, j2+j34, j3+j24],
      1-Mod[2*(j1+j),2]/2 }
   ]
(* QUESTION::2016-02-22: Mathematica says that SixJSymbol[] givs the Racah 6-j
   symbol. Is it the same as the Wigner 6-j symbol? Messiah says that they are
   different in sign. *)

WignerEckart::usage = "WignerEckart[{i1,i2,ii}, {k1,k2,kk}, {j1,j2,jj}] returns the Wigner-Eckart coefficient."

WignerEckart[{i1_,i2_,ii_}, {k1_,k2_,kk_}, {j1_,j2_,jj_}] :=
  Sqrt[(2*i1+1)(2*i2+1)(2*kk+1)(2*jj+1)] *
  NineJSymbol[{j1,j2,jj}, {k1,k2,kk}, {i1,i2,ii}]

(*
 * Epiloque
 *)

Protect[Evaluate @ $symbs]

End[]


Q3Protect[]


EndPackage[]
