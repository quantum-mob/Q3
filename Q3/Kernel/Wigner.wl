(* -*- mode: math; -*- *)

BeginPackage["Q3`"]

{ TheWigner, TheWignerKet };

{ Spin, SpinQ, Spins };

{ SpinNumbers, SpinNumberQ };

{ WignerSpinSpin };

{ WignerDecompose, WignerCompose,
  WignerCoefficients };

{ WignerAdd, WignerAddZ };

{ SpinCoherentState };

{ WignerDistributionW,
  WignerDistributionC };

{ ClebschGordanTable };

{ NineJSymbol, WignerEckart };


Begin["`Private`"]

$symb = Unprotect[Missing]


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

TheWigner[{J_?SpinNumberQ, Raising}] := TheWigner[{J,4}]

TheWigner[{J_?SpinNumberQ, Lowering}] := TheWigner[{J,5}]

TheWigner[{J_?SpinNumberQ, s_ -> t_}] := SparseArray[
  {J+1 - t, J+1 - s} -> 1,
  {2*J+1, 2*J+1}
 ]

TheWigner[{J_?SpinNumberQ, 0, theta_, phi_}] := TheWigner[{J,0}]

TheWigner[{J_?SpinNumberQ, n:(1|2|3), theta_, phi_}] := With[
  { R = EulerMatrix[{phi, theta, 0}] },
  TheWigner[{J, 1}]*R[[1, n]] + TheWigner[{J, 2}]*R[[2, n]] + TheWigner[{J, 3}]*R[[3, n]]
 ]

TheWigner[ nn:{_?SpinNumberQ, (0|1|2|3|4|5|6|Raising|Lowering)}.. ] :=
  CircleTimes @@ Map[TheWigner] @ {nn}

TheWigner[ { j_?SpinNumberQ, n:{(0|1|2|3|4|5|6|Raising|Lowering)..} } ] :=
  CircleTimes @@ Map[TheWigner] @ Tuples[{{j}, n}]

TheWigner[ { j_?SpinNumberQ, n:{(0|1|2|3|4|5|6|Raising|Lowering)..},
    th:Except[_List], ph:Except[_List] } ] :=
  CircleTimes @@ Map[TheWigner] @ Tuples[{{j}, n, {th}, {ph}}]


TheWignerKet::usage = "TheWignerKet[{j,m}] or TheWignerKet[j,m] returns column vector representation of the spin angular momentum basis state Ket[j,m].\nTheWignerKet[{j1,m1}, {j2,m2}, ...] returns the direct product of TheWignerKet[{j1,m1}], TheWignerKet[{j2,m2}], ....\nTheWignerKet[j, {m1, m2, ...}] is equivalent to TheWignerKet[{j,m1}, {j,m2}, ...]."

TheWignerKet[{j_, m_}] := SparseArray[(j-m+1)->1, 2*j+1] /; SpinNumberQ[j, m]

TheWignerKet[j:Except[_List], m:Except[_List]] := TheWignerKet @ {j, m}

TheWignerKet[j:Except[_List], mm:{__?NumericQ}] := With[
  { jm = Thread @ {j, mm} },
  TheWignerKet @@ jm /; AllTrue[jm, SpinNumberQ]
 ]

TheWignerKet[jm:{_, _}, more:{_, _}..] :=
  CircleTimes @@ Map[TheWignerKet, {jm, more}] /;
  AllTrue[{jm, more}, SpinNumberQ]


(**** <TheRotation> ****)

TheRotation[_, {_?SpinNumberQ, 0}] := IdentityMatrix[2*J+1]

TheRotation[phi_, {J_?SpinNumberQ, n:(1|2|3)}] :=
  MatrixExp[ -I phi TheWigner[{J, n}] ]

TheRotation[{phi_, {J_?SpinNumberQ, n:(1|2|3)}}] :=
  TheRotation[phi, {J, n}]

TheRotation[
  a:{_, {_?SpinNumberQ, (0|1|2|3)}},
  b:{_, {_?SpinNumberQ, (0|1|2|3)}}.. ] :=
  CircleTimes @@ Map[TheRotation, {a, b}]

(**** <TheRotation> ****)


(**** <TheEulerRotation> ****)

TheEulerRotation[ {phi_, theta_, chi_}, J_?SpinNumberQ ] :=
  TheRotation[phi, {J, 3}] . TheRotation[theta, {J, 2}] .
  TheRotation[chi, {J, 3}]

TheEulerRotation[{{a_, b_, c_}, J_?SpinNumberQ}] :=
  TheEulerRotation[{a, b, c}, J]

TheEulerRotation[
  a:{{_, _, _}, _?SpinNumberQ},
  b:{{_, _, _}, _?SpinNumberQ}.. ] :=
  CircleTimes @@ Map[TheEulerRotation, {a, b}]

(**** </TheEulerRotation> ****)


(**** <SpinQuantumNumberQ> ****)

SpinNumbers::usage = "SpinNumbers[s] returns a list of spin quantum numbers {{s, s}, {s, s-1}, \[Ellipsis], {s, -s}}."

SpinNumbers[j_?SpinNumberQ] := Thread[{j, Range[j,-j,-1]}]


SpinNumberQ::usage = "SpinNumberQ[J] returns True if J is a valid angular momentum quantum number (non-negative integer or half-integer).\nSpinNumberQ[J,M] returns True if J is a valid angular momentum quantum number and M is a valid magnetic quantum number (-j<=m<=j)."
(* To be defined further in other packages; e.g., Wigner. *)

SetAttributes[SpinNumberQ, {NHoldAll, ReadProtected}]

SpinNumberQ[_Integer?NonNegative] = True

SpinNumberQ[Rational[_, 2]?Positive] = True

SpinNumberQ[j_Integer?NonNegative, m_Integer] := And[ -j <= m <= j ]

SpinNumberQ[j:Rational[_, 2]?Positive, m:Rational[_, 2]] := And[ -j <= m <= j ]

SpinNumberQ[{j_, m_}] := SpinNumberQ[j, m]

SpinNumberQ[__] = False

(**** </SpinQuantumNumberQ> ****)


(**** <Spin> ****)

Spin::usage = "Spin refers to either the Spin species or an option for the Boson, Fermion or Spin species.\nSpin[c] returns the Spin quantum number of Species c."

Spin::bad = "Bad spin value ``: Spin should be a non-negative integer or half-integer for Spin species, integer for Fermions, and half-integer for Fermions. Being reset to 1/2 for a Spin species."

SetAttributes[Spin, Listable]

Spin[ HoldPattern @ Dagger[c_?ParticleQ] ] := Spin[c]

Spin[_] = 0 (* by default every thing is spinless *)


Options[Spin] = {Spin->1/2}

Spin /:
Let[Spin, ss:{__Symbol}, OptionsPattern[Spin]] := Module[
  { spin = OptionValue[Spin] },  
  If[ Not[SpinNumberQ @ spin],
    Message[Spin::bad, spin];
    spin = 1/2
  ];
  
  Let[NonCommutative, ss];    
  Scan[setSpin[spin], ss];
]

setSpin[spin_][x_Symbol] := (
  MultiplyKind[x] ^= Spin;
  MultiplyKind[x[___]] ^= Spin;
  
  Dimension[x] ^= 2*spin + 1;
  Dimension[x[___]] ^= 2*spin + 1;

  LogicalValues[x] ^= Range[spin, -spin, -1];
  LogicalValues[x[___]] ^= Range[spin, -spin, -1];

  AgentQ[x] ^= True;
  AgentQ[x[___]] ^= True;

  SpinQ[x] ^= True;
  SpinQ[x[___]] ^= True;

  Spin[x] ^= spin;
  Spin[x[___]] ^= spin;
  x[___, Spin] = spin;

  If[ spin == 1/2,
    x[j___,  1/2 ->  1/2] := 1/2 + x[j,3];
    x[j___, -1/2 -> -1/2] := 1/2 - x[j,3];
    x[j___, -1/2 ->  1/2] := x[j, 4];
    x[j___,  1/2 -> -1/2] := x[j, 5]
  ];

  x /: Dagger[ x[j___, k:(0|1|2|3|6)] ] := x[j, k];
  x /: Dagger[ x[j___, 4] ] := x[j, 5];
  x /: Dagger[ x[j___, 5] ] := x[j, 4];

  x /: Power[x, n_Integer] := MultiplyPower[x, n];
  x /: Power[x[j___], n_Integer] := MultiplyPower[x[j], n];

  x[j___, Raising] := x[j,1] + I x[j,2];
  x[j___, Lowering] := x[j,1] - I x[j,2];
  
  x[j___, Hadamard] := MultiplyExp[-I (Pi/2) x[j,2]] ** x[j,3] / spin;
  (* NOTE: For Spin-1/2, this is enough to reduce it to (X+Z)/Sqrt[2].
     See Cauchy.m for Exp[ (Clifford- or Grassmann-like elements) ] .*)
  
  x[j___, All]  := Flatten @ x[j, {1,2,3}];
  x[j___, Full] := Flatten @ x[j, {0, 1, 2, 3}];

  Format @ x[j___, $] :=
    Interpretation[SpeciesBox[x, {j}, {}], x[j, $]];

  Format @ x[j___,0] := Interpretation[SpeciesBox[x, {j}, {0}], x[j, 0]];
  Format @ x[j___,1] := Interpretation[SpeciesBox[x, {j}, {"X"}], x[j, 1]];
  Format @ x[j___,2] := Interpretation[SpeciesBox[x, {j}, {"Y"}], x[j, 2]];
  Format @ x[j___,3] := Interpretation[SpeciesBox[x, {j}, {"Z"}], x[j, 3]];
  Format @ x[j___,4] := Interpretation[SpeciesBox[x, {j}, {"+"}], x[j, 4]];
  Format @ x[j___,5] := Interpretation[SpeciesBox[x, {j}, {"-"}], x[j, 5]];
  Format @ x[j___,6] := Interpretation[SpeciesBox[x, {j}, {"H"}], x[j, 6]];
  
  Format @ x[j___, a_->b_] := Interpretation[
    SpeciesBox[
      Row @ {"(",Ket[b],Bra[a],")"}, {x[j, $]},
      {}
    ],
    x[j, a -> b]
  ]
)

Missing["KeyAbsent", S_Symbol?SpinQ[___, $]] := Spin[S]

(**** <Spin> ****)


SpinQ::usage = "SpinQ[J] or SpinQ[J[...]] returns True if J is declared as a Spin operator."

AddGarnerPatterns[_?SpinQ];

SpinQ[_] = False


Spins::usage = "Spins[expr] gives the list of all Spins appearing in expr."

Spins[expr_] := Select[Agents @ expr, SpinQ]


SpinHalfQ::usage = "SpinHalfQ[J] or SpinHalfQ[J[...]] returns True if J is a Spin operator and its Spin is 1/2."

SpinHalfQ[J_Symbol?SpinQ] := Spin[J]==1/2

SpinHalfQ[J_Symbol?SpinQ[k___]] := Spin[J[k]]==1/2

SpinHalfQ[_] = False


(* Multiply *)

(* Speical Rules: Involving identity *)

HoldPattern @
  Multiply[pre___, x_?SpinQ[j___,0], x_?SpinQ[j___,n_], post___] :=
  Multiply[pre, x[j,n], post]

HoldPattern @
  Multiply[pre___, x_?SpinQ[j___,n_], x_?SpinQ[j___,0], post___] :=
  Multiply[pre, x[j,n], post]
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

HoldPattern @
  Multiply[ x___, a_?SpinQ[j___,0], Ket[b_Association], y___ ] :=
  Multiply[ x, Ket[b], y ]

HoldPattern @
  Multiply[ x___, a_?SpinQ[j___,4], Ket[b_Association], y___ ] := Module[
    { J = Spin[a],
      M = b[a[j,$]],
      v },
    v = Sqrt[J(J+1)-M(M+1)] * Ket[KeySort @ Append[b, a[j,$]->M+1]];
    Multiply[x, v, y]
   ]

HoldPattern @
  Multiply[ x___, a_?SpinQ[j___,5], Ket[b_Association], y___ ] := Module[
    { J = Spin[a],
      M = b[a[j,$]],
      v },
    v = Sqrt[J(J+1)-M(M-1)] Ket[KeySort @ Append[b, a[j,$]->M-1]];
    Multiply[x, v, y]
   ]

HoldPattern @
  Multiply[pre___, a_?SpinQ[j___,1], b:Ket[_Association], post___] :=
  Multiply[pre, (a[j,4]**b + a[j,5]**b)/2, post]

HoldPattern @
  Multiply[pre___, a_?SpinQ[j___,2], b:Ket[_Association], post___] :=
  Multiply[pre, (a[j,4]**b - a[j,5]**b)/(2*I), post]

HoldPattern @
  Multiply[pre___, a_?SpinQ[j___,3], Ket[b_Association], post___] :=
  b[a[j,$]] * Multiply[pre, Ket[b], post]


AddElaborationPatterns[
  G_?SpinQ[j___,0] -> 1,
  G_?SpinQ[j___,4] -> G[j, Raising],
  G_?SpinQ[j___,5] -> G[j, Lowering],
  G_?SpinQ[j___,6] -> G[j, Hadamard]
 ]

$RaisingLoweringRules = Join[ $RaisingLoweringRules,
  { S_?SpinQ[j___,1] :> (S[j,4] + S[j,5]) / 2 ,
    S_?SpinQ[j___,2] :> (S[j,4] - S[j,5]) / (2 I)
   }
 ]


(* MultiplyDegree for operators *)
MultiplyDegree[_?SpinQ] = 1


(* Base: See Cauchy *)

Base[ S_?SpinQ[j___, _] ] := S[j]
(* For Spins, the final Flavor index is special. *)


(* FlavorCap: See Cauchy package *)

FlavorCap[S_?SpinQ] := S[$]


(* FlavorMute: See Cauchy *)

FlavorMute[S_Symbol?SpinQ] := S[$]

FlavorMute[S_Symbol?SpinQ[j___, _]] := S[j, $]

FlavorMute[S_Symbol?SpinQ[j___, _] -> m_] := S[j, $] -> m


(**** <Ket> ****)

theKetTrim[Rule[S_?SpinQ, m_]] := Nothing /; Spin[S] == m

KetVerify::spin = "Invalid value `` for spin ``."

theKetVerify[Rule[op_?SpinQ, m_]] := (
  Message[KetVerify::spin, m, op];
  $Failed
) /; Not[-Spin[op] <= m <= Spin[op]]
(* NOTE: The following definition would not allow to assign a symbolic value:
   theKetVerify[Rule[_?SpinQ, m]] = $Failed /; SpinNumberQ @ {Spin[op], m} *)

(**** </Ket> ****)


(**** <Basis> ****)

Basis[ op_?SpinQ ] := With[
  { J = Spin[op] },
  Ket /@ Thread[FlavorCap[op] -> Range[J, -J, -1]]
 ]

(**** </Basis> ****)


(**** <Matrix> ****)

TheMatrix[S_?SpinQ[___,j_]] := TheWigner @ {Spin[S], j}

TheMatrix[ Ket[ Association[S_?SpinQ -> m_] ] ] := TheWignerKet @ {Spin[S], m}

(**** </Matrix> ****)


(**** <ExpressionFor> ****)

TheExpression[S_?SpinQ] := {
  {1/2 + S[3], S[4]},
  {S[5], 1/2 - S[3]}
 } /; Spin[S] == 1/2
(* NOTE: This makes ExpressionFor to generate an operator expression in terms
   of the Pauli raising and lowering operators instead of the Pauli X and Y
   operators. Many evaluations are faster with the raising and lowering
   operators rather than X and Y operators. When an expression in terms of the
   X and Y operators are necessary, one can use Elaborate. *)

(**** </ExpressionFor> ****)


(**** <WignerSpinSpin> ****)

WignerSpinSpin::usage = "WignerSpinSpin[dir][S1, S2, ...] returns the sum of exchange couplings between Spins S1, S2, ... for components specified by dir."

WignerSpinSpin[All][ss__] := WignerSpinSpin[{1,2,3}][ss]

WignerSpinSpin[dir:(1|2|3|{(1|2|3)..})][ss__] := Module[
  { tt = FlavorCap @ {ss},
    links },
  links = Chain @@ tt;
  Total[ wSpinSpin[dir] /@ links ]
 ] /; And @@ SpinQ /@ Flatten @ {ss}

wSpinSpin[dir:(1|2|3)][a_ -> b_] := a[dir] ** b[dir]

wSpinSpin[dir:{(1|2|3)..}][a_ -> b_] := MultiplyDot[a[dir], b[dir]]

(**** </WignerSpinSpin> ****)


(**** <WignerAddZ> ****)

WignerAddZ::usage = "WignerAddZ[J1, J2, ...] returns in an Association the irreducible basis of the total angular momentum J1 + J2 + ... invariant under the U(1) rotation around spin z-axis."

WignerAddZ::duplicate = "Duplicate angular momentum operators appear."


WignerAddZ[ ls:{(_?SpinQ|_Association)..} ] :=
  WignerAddZ @@ Map[WignerAddZ] @ ls

WignerAddZ[] := Association[ {0} -> {Ket[]} ]

WignerAddZ[irb_Association] := irb

WignerAddZ[a_?SpinQ] := Module[
  { aa = FlavorCap @ a,
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

(**** </WignerAddZ> ****)


(**** <WignerAdd> ****)

WignerAdd::usage = "WignerAdd[J1, J2, ...] returns in an Association the irreducible basis of the total angular momentum J1 + J2 + ...."

WignerAdd::duplicate = "Duplicate angular momentum operators appear."

WignerAdd[ ls:{(_?SpinQ|_Association)..} ] :=
  WignerAdd @@ Map[WignerAdd] @ ls

WignerAdd[] := Association[ {0,0} -> {Ket[]} ]

WignerAdd[irb_Association] := irb

WignerAdd[a_?SpinQ] := Module[
  { aa = FlavorCap @ a,
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

(**** </WignerAddZ> ****)


(**** <Rotation> ****)

Rotation /:
Elaborate @ Rotation[phi_, v:{_,_,_}, S_?SpinQ, ___] :=
  Cos[phi/2] - I*Sin[phi/2]*Dot[2*S[All], Normalize @ v] /;
  Spin[S] == 1/2

Rotation /:
Elaborate @ Rotation[phi_, v:{_,_,_}, S_?SpinQ, ___] := Module[
  { bs = Basis[S],
    vn = v / Norm[v],
    Rn },
  Rn = vn . {
    TheWigner[{Spin[S], 1}],
    TheWigner[{Spin[S], 2}],
    TheWigner[{Spin[S], 3}] };
  Rn = MatrixExp[ -I phi Rn ];
  Inner[Dyad[S], bs.Rn, bs]
 ]

(**** </Rotation> ****)



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
  ss = Map[ (#[$])&, ss, {2} ];
  cc = Map[ CoefficientTensor[op, Sequence @@ #]&, kk ];
  cc /= Power[2, n];
  Association[ Thread[ss->cc] ]
 ]


SpinCoherentState::usage = "SpinCoherentState[S, th, ph] gives the spin coherent state."

SpinCoherentState[S_?SpinQ, 0, ph_] := Ket[S -> Spin[S]]

SpinCoherentState[S_?SpinQ, Pi, ph_] := Ket[S -> -Spin[S]]

SpinCoherentState[S_?SpinQ, th_, ph_] := Module[
  { J = Spin[S],
    sin = Sin[th]/2,
    cot = Cot[th/2],
    basis = Basis[{S}] },
  
  cc = Table[
    Sqrt[Binomial[2 J, J + m]] * cot^m * Exp[-I*ph*(J+m)],
    {m, J, -J, -1} ];
  
  Power[sin, J] * Dot[cc, basis]
 ]


(**** <WignerDistributionW> ****)
(* Wigner distribution function W; See Pezze et al (2018a, Section II.D.2) *)

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
  Return[rho . YY]
]

(**** </WignerDistributionW> ****)


(**** <WignerDistributionC> ****)
(* Wigner distribution function C; See Pezze et al (2018a, Section II.C.3) *)

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

(**** </WignerDistributionC> ****)


(**** <ClebschGordanTable> ****)

ClebschGordanTable::usage = "ClebschGordanTable[j1,j2] returns the matrix of the Clebsch-Gordan coefficients."

Options[ClebschGordanTable] = { "PrintTable" -> True }

ClebschGordanTable[j1_?SpinNumberQ, j2_?SpinNumberQ, OptionsPattern[]] := Module[
  { JJ = Range[j1+j2, Abs[j1-j2], -1],
    JM, printQ },

  JM = Catenate @ Map[SpinNumbers] @ JJ;
  cg = Quiet[
     Outer[ ClebschGordan,
       SpinNumbers[j1], SpinNumbers[j2], JM,
       1 ],
     ClebschGordan::phy
  ];
  cg = Flatten[cg, 1];
   
  If[OptionValue["PrintTable"], printCG[j1, j2, cg]];
  Return[cg]
]


printCG::usage = "Displays the Clebsch-Gordan table."

printCG[j1_, j2_, cg_] := Module[
  { JJ = Range[j1+j2, Abs[j1-j2], -1], JM,
    m1 = Range[j1, -j1, -1],
    m2 = Range[j2, -j2, -1], m1m2,
    jj, mm, table },

  (* Header row *)
  JM = Catenate @ Map[SpinNumbers] @ JJ;
  JM = {Ket /@ JM}; (* 1 x N matrix *)
  
  (* Header column *)
  m1m2 = Tuples @ {m1, m2};
  m1m2 = Transpose @ {Bra /@ m1m2}; (* N x 1 matrix *)
  
  (* The whole table *)
  table = ArrayFlatten @ {
    { {{""}}, JM },
    { m1m2, cg }
  };
  
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

(**** </ClebschGordanTable> ****)


(**** <NineJSymbol> ****)

NineJSymbol::usage = "NineJSymbol[{j1,j2,j3}, {j4,j5,j6},{j7,j8,j9}] gives the Wigner 9j-symbol."

(* Special cases with one of J's is zero, in which case the Nine-J symbol is related to the Six-J symbol. *)

NineJSymbol[
  {j1_,  j2_,  j12_},
  {j3_,  j4_,  j34_},
  {j13_, j24_,  0 }
 ] :=
  KroneckerDelta[j12, j34] *
  KroneckerDelta[j13, j24] *
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

(**** </NineJSymbol> ****)


(**** <WignerEckart> ****)

WignerEckart::usage = "WignerEckart[{i1,i2,ii}, {k1,k2,kk}, {j1,j2,jj}] returns the Wigner-Eckart coefficient."

WignerEckart[{i1_,i2_,ii_}, {k1_,k2_,kk_}, {j1_,j2_,jj_}] :=
  Sqrt[(2*i1+1)(2*i2+1)(2*kk+1)(2*jj+1)] *
  NineJSymbol[{j1,j2,jj}, {k1,k2,kk}, {i1,i2,ii}]

(**** </WignerEckart> ****)


Protect[Evaluate @ $symb]

End[]

EndPackage[]
