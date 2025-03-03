(* -*- mode:math -*- *)
BeginPackage["QuantumMob`Q3S`", {"System`"}]

{ DickeBasis };

Begin["`Private`"]

(**** <DickeBasis> ****)

DickeBasis::usage = "DickeBasis[s1, s2, \[Ellipsis], {m, n}] returns the computational basis for a system Flatten[{s1, s2, \[Ellipsis]}] of qubits, qudits, bosons or a list of such species, where the number of particles in each bosonic mode is limited in Range[m, n].\nDickeBasis[spec, n] is equivalent DickeBasis[spec, {m, n}], where m is the maximum of the Bottom values of the bosonic moodes.\nDickeBasis[spec] is equivalent to DickeBasis[spec, {m, n}], where m is the maximum of the Bottom values of the bosonic moodes and n is the minimum of the Top values of the bosonic modes."

DickeBasis[ss:(_?QubitQ | _?QuditQ | _?BosonQ | {(_?QubitQ | _?QuditQ | _?BosonQ)..})..] :=
  Module[
    { bb = Cases[Flatten @ {ss}, _?BosonQ],
      m, n },
    m = Max[Bottom /@ bb];
    n = Min[Top /@ bb];
    Flatten @ Outer[CircleTimes, Basis @ Supplement[Flatten @ {ss}, bb], Catenate @ BosonBasis[bb, {m, n}]]
  ]

DickeBasis[ss:(_?QubitQ | _?QuditQ | _?BosonQ | {(_?QubitQ | _?QuditQ | _?BosonQ)..}).., n_Integer] :=
  Module[
    { bb = Cases[Flatten @ {ss}, _?BosonQ],
      m },
    m = Max[Bottom /@ bb];
    Flatten @ Outer[CircleTimes, Basis @ Supplement[Flatten @ {ss}, bb], Catenate @ BosonBasis[bb, {m, n}]]
  ]

DickeBasis[ss:(_?QubitQ | _?QuditQ | _?BosonQ | {(_?QubitQ | _?QuditQ | _?BosonQ)..}).., {m_Integer, n_Integer}] :=
  With[
    { bb = Cases[Flatten @ {ss}, _?BosonQ] },
    Flatten @ Outer[CircleTimes, Basis @ Supplement[Flatten @ {ss}, bb], Catenate @ BosonBasis[bb, {m, n}]]
  ]

(**** </DickeBasis> ****)

End[]

EndPackage[]
