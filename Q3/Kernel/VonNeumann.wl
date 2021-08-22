(* -*- mode:math -*- *)
(* Package for stabilizer formalism *)

BeginPackage["Q3`"]

`VonNeumann`$Version = StringJoin[
  $Input, " v",
  StringSplit["$Revision: 1.9 $"][[2]], " (",
  StringSplit["$Date: 2021-08-21 11:35:27+09 $"][[2]], ") ",
  "Mahn-Soo Choi"
 ];

{ ShannonEntropy, WeightedLog };
{ VonNeumannEntropy, QuantumLog };


Begin["`Private`"]

WeightedLog::usage = "WeightedLog[z] returns -z*Log[2, z], the weighted logarithm to base 2.\nWeightedLog[0] = 0.\nWeightedLog[p, q] returns -p*Log[2, q].\nWeightedLog[0, q] = 0.\nWeightedLog[p>0, 0] = \[Infinity]."

SetAttributes[WeightedLog, Listable]

WeightedLog[0] = 0

WeightedLog[z_?Positive] := -z * Log2[z]


WeightedLog[0, _] = 0

WeightedLog[_?Positive, 0] = Infinity

WeightedLog[p_?Positive, q_?Positive] := -p * Log2[q]


ShannonEntropy::usage = "ShannonEntropy[{p1, p2, \[Ellipsis]}] returns the base 2 Shannon entropy of the probability distribution {p1, p2, \[Ellipsis]}.\nShannonEntropy[{p1, p2, \[Ellipsis]}, {q1, q2, \[Ellipsis]}] returns the relative entropy between the two probability distributions {p1, p2, \[Ellipsis]} and {q1, q2, \[Ellipsis]}."

ShannonEntropy::noprb = "`` does not seem to be a probability distribution."

ShannonEntropy[pp:{__}] :=
  (Message[ShannonEntropy::noprb, pp]; 0) /;
  AnyTrue[pp, Negative]

ShannonEntropy[pp:{__}, qq:{__}] :=
  (Message[ShannonEntropy::noprb, pp]; 0) /;
  AnyTrue[pp, Negative]

ShannonEntropy[pp:{__}, qq:{__}] :=
  (Message[ShannonEntropy::noprb, qq]; 0) /;
  AnyTrue[qq, Negative]

ShannonEntropy[pp:{__}] := Total[WeightedLog[pp]]

ShannonEntropy[pp:{__}, qq:{__}] := Total[WeightedLog[pp, qq]]


QuantumLog::usage = "QuantumLog[p, q] returns -Tr[p ** Log[2, q]] for the observables p and q.\nQuantumLog[p, q, {s1, s2, \[Ellipsis]}] assumes that states p and q, either density operators or ket vectors, are defined for the systems {s1, s2, \[Ellipsis]}.\nQuantumLog is a low-level mathematical function intended for the use in VonNeumannEntropy or related functions."

QuantumLog[a_?VectorQ, b_?VectorQ] :=
  If[Fidelity[a, b] == 1, 0, Infinity]

QuantumLog[a_?MatrixQ, b_?VectorQ] := Module[
  { aval, avec,
    bval, bvec },
  {aval, avec} = Transpose @ Select[Transpose @ Eigensystem[a], First[#] > 0&];
  If[ Length[aval] > 1, Return[Infinity] ];

  avec = Flatten[avec];
  If[ AllTrue[avec, NumericQ], avec = Normalize[avec] ];
  If[ Fidelity[avec, b] == 1, 0, Infinity ]
 ]

QuantumLog[a_?VectorQ, b_?MatrixQ] := Module[
  { bval, bvec },
  {bval, bvec} = Eigensystem[b];
  If[ AllTrue[Flatten @ bvec, NumericQ] && Not[UnitaryMatrixQ @ bvec],
    bvec = Orthogonalize[bvec]
   ];
  Total @ WeightedLog[Abs[Conjugate[a] . Transpose[bvec]]^2, bval]
 ]

QuantumLog[a_?MatrixQ, b_?MatrixQ] := Module[
  { aval, avec,
    bval, bvec },
  {aval, avec} = Eigensystem[a];  
  If[ AllTrue[Flatten @ avec, NumericQ] && Not[UnitaryMatrixQ @ avec],
    avec = Orthogonalize[avec]
   ];
  {bval, bvec} = Eigensystem[b];
  If[ AllTrue[Flatten @ bvec, NumericQ] && Not[UnitaryMatrixQ @ bvec],
    bvec = Orthogonalize[bvec]
   ];
  Total @ WeightedLog[aval . Abs[Conjugate[avec] . Transpose[bvec]]^2, bval]
 ]


QuantumLog[a_, b_, ss:{___?SpeciesQ}] :=
  QuantumLog[Matrix[a, ss], Matrix[b, ss]]

QuantumLog[a_, b_] := QuantumLog[a, b, NonCommutativeSpecies @ {a, b}]


VonNeumannEntropy::usage = "VonNeumannEntropy[mat|vec] returns the base 2 VonNeumann entropy of the quantum state described by the density matrix 'mat' or vector 'vec'.\nVonNeumannEntropy[mat1, mat2] returns the quantum relative entropy of the mixed state mat1 with respect to mat2."

VonNeumannEntropy[vec_?VectorQ] = 0

VonNeumannEntropy[mat_?MatrixQ] := ShannonEntropy[Eigenvalues @ mat]

VonNeumannEntropy[rho_, ss:{___?SpeciesQ}] :=
  VonNeumannEntropy @ Matrix[rho, ss]

VonNeumannEntropy[rho_] :=
  VonNeumannEntropy[rho, NonCommutativeSpecies @ rho]

VonNeumannEntropy[rho_, sig_, ss:{___?SpeciesQ}] :=
  QuantumLog[rho, sig, ss] - VonNeumannEntropy[rho, ss]

VonNeumannEntropy[rho_, sig_] :=
  VonNeumannEntropy[rho, sig, NonCommutativeSpecies @ {rho, sig}]


End[]

EndPackage[]
