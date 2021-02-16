(* -*- mode:math -*- *)
(* Mahn-Soo Choi *)
(* $Date: 2021-01-28 11:24:46+09 $ *)
(* $Revision: 1.9 $ *)


BeginPackage[ "Q3`Dicke`",
  { "Q3`Fock`", "Q3`Quisso`",
    "Q3`Pauli`", "Q3`Cauchy`", "Q3`" }
 ]

Unprotect[Evaluate[$Context<>"*"]]

Begin["`Private`"]
`Version = StringJoin[
  $Input, " v",
  StringSplit["$Revision: 1.9 $"][[2]], " (",
  StringSplit["$Date: 2021-01-28 11:24:46+09 $"][[2]], ") ",
  "Mahn-Soo Choi"
 ];
End[]

{ DickeBasis };


Begin["`Private`"]

$symbs = Unprotect[ Multiply ]

DickeBasis::usage = "DickeBasis[{S1, S2, ...}, {b1, b2, ...}, {m,n}] constructs a basis for Qubits/Qudits S1, S2, ... and Bosonic modes b1, b2, ..., where the number of particles in each Bosonic modes is limited in the range [m, n].\nDickeBasis[ {S1, S2, ...}, {b1, b2, ...}, n] is equivalent to DickeBasis[ {S1, S2, ...}, {b1, b2, ...}, {0,n}]."

DickeBasis[ ss:{__?QubitQ}, bb:{__?BosonQ}, n_Integer ] :=
  DickeBasis[ ss, bb, {0, n} ]

DickeBasis[ ss:{__?QubitQ}, bb:{__?BosonQ}, {m_Integer, n_Integer} ] :=
  Flatten @ Outer[ CircleTimes, Basis @ ss, BosonBasis[bb, {m,n}] ]


DickeBasis[ ss:{__?QuditQ}, bb:{__?BosonQ}, n_Integer ] :=
  DickeBasis[ ss, bb, {0, n} ]

DickeBasis[ ss:{__?QuditQ}, bb:{__?BosonQ}, {m_Integer, n_Integer} ] :=
  Flatten @ Outer[ CircleTimes, Basis @ ss, BosonBasis[bb, {m,n}] ]


Protect[ Evaluate @ $symbs ]

End[]


Q3Protect[]


EndPackage[]
