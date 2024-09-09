(* stabilizer formalism *)
BeginPackage["Q3`"]

{ CliffordState, CliffordUnitary };

{ GottesmanFlip };

Begin["`Private`"]


CliffordState[data_, ss : {___?QubitQ}, rest___] :=
 CliffordState[data, FlavorCap @ ss, rest] /; Not[FlavorCapQ @ ss]

CliffordState /:
Matrix @ CliffordState[data_?MatrixQ, ___] := Module[
  { mm = FromGottesmanVector /@ Most /@ data,
    m, n },
  {m, n} = Dimensions[data];
  n = Power[2, (n - 1)/2];
  mm = Matrix[mm*Map[Last, data]];
  Apply[Dot, ConstantArray[One[n], m] + mm]/n
]


CliffordUnitary[mat_, ___][cs_CliffordState] := Module[
  { vec = Most /@ First[cs],
    sig = Last /@ First[cs] },
   sig *= IntegerParity[vec . Last[mat]];
   vec = Mod[vec . Most[mat], 2];
   CliffordState[Transpose @ Append[Transpose @ vec, sig]]
] /; MatrixQ[mat, BinaryQ]

CliffordUnitary /:
Multiply[pre___, cu_CliffordUnitary, cs_CliffordState, post___] :=
  Multiply[pre, cu[cs], post]

CliffordUnitary /:
Matrix @ CliffordUnitary[mat_?MatrixQ, ___] := Dot[
  Matrix @ FromGottesmanMatrix[Most @ mat],
  Matrix @ FromGottesmanVector @ GottesmanFlip[Last @ mat]
]


GottesmanFlip::usage = "GottesmanFlip[vec] swaps the x-bit and z-bit of each qubit in Gottesman vector vec."

GottesmanFlip[vec_?VectorQ] := 
  Append[GottesmanFlip[Most @ vec], Last @ vec] /;
  OddQ[Length @ vec]

GottesmanFlip[vec_] := 
  Flatten[Reverse /@ Partition[vec, 2]] /;
  VectorQ[vec, BinaryQ] && EvenQ[Length @ vec]


End[]

EndPackage[]
