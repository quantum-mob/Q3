(* -*- mode:math -*- *)

BeginPackage["Q3`"]

`Dicke`Information`$Version = StringJoin[
  $Input, " v",
  StringSplit["$Revision: 1.21 $"][[2]], " (",
  StringSplit["$Date: 2021-06-03 09:03:42+09 $"][[2]], ") ",
  "Mahn-Soo Choi"
 ];

{ DickeBasis };

Begin["`Private`"]

DickeBasis::usage = "DickeBasis[{S1, S2, ...}, {b1, b2, ...}, {m,n}] constructs a basis for Qubits/Qudits S1, S2, ... and Bosonic modes b1, b2, ..., where the number of particles in each Bosonic modes is limited in the range [m, n].\nDickeBasis[ {S1, S2, ...}, {b1, b2, ...}, n] is equivalent to DickeBasis[ {S1, S2, ...}, {b1, b2, ...}, {0,n}]."

DickeBasis[ s_?QubitQ, b_?BosonQ, n_Integer ] :=
  DickeBasis[{s}, {b}, n]

DickeBasis[ ss:{__?QubitQ}, b_?BosonQ, n_Integer ] :=
  DickeBasis[ss, {b}, n]

DickeBasis[ s_?QubitQ, bb:{__?BosonQ}, n_Integer ] :=
  DickeBasis[{s}, bb, n]

DickeBasis[ ss:{__?QubitQ}, bb:{__?BosonQ}, n_Integer ] :=
  DickeBasis[ ss, bb, {0, n} ]

DickeBasis[ ss:{__?QubitQ}, bb:{__?BosonQ}, {m_Integer, n_Integer} ] :=
  Flatten @ Outer[ CircleTimes, Basis @ ss, BosonBasis[bb, {m,n}] ]


DickeBasis[ ss:{__?QuditQ}, bb:{__?BosonQ}, n_Integer ] :=
  DickeBasis[ ss, bb, {0, n} ]

DickeBasis[ ss:{__?QuditQ}, bb:{__?BosonQ}, {m_Integer, n_Integer} ] :=
  Flatten @ Outer[ CircleTimes, Basis @ ss, BosonBasis[bb, {m,n}] ]

End[]

EndPackage[]
