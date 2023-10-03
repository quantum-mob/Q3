(* -*- mode:math -*- *)
(* Package for stabilizer formalism *)

BeginPackage["Q3`"]

`VonNeumann`$Version = StringJoin[
  $Input, " v",
  StringSplit["$Revision: 1.22 $"][[2]], " (",
  StringSplit["$Date: 2023-10-01 11:18:47+09 $"][[2]], ") ",
  "Mahn-Soo Choi"
 ];

{ ShannonEntropy, WeightedLog };
{ VonNeumannEntropy, QuantumLog };
{ RenyiEntropy };

{ MutualInformation };


Begin["`Private`"]

WeightedLog::usage = "WeightedLog[z] returns -z*Log[2, z], the weighted logarithm to base 2.\nWeightedLog[0] = 0.\nWeightedLog[p, q] returns -p*Log[2, q].\nWeightedLog[0, q] = 0.\nWeightedLog[p>0, 0] = \[Infinity]."

SetAttributes[WeightedLog, Listable]

WeightedLog[0] = 0

WeightedLog[z_] := 0 /; Chop[z] == 0

WeightedLog[z_?Positive] := -z * Log2[z]


WeightedLog[0, _] = 0

WeightedLog[_?Positive, 0] = Infinity

WeightedLog[p_?Positive, q_?Positive] := -p * Log2[q]


WeightedLog[z_] := -z * Log2[z]


ShannonEntropy::usage = "ShannonEntropy[{p1, p2, \[Ellipsis]}] returns the base 2 Shannon entropy of the probability distribution {p1, p2, \[Ellipsis]}.\nShannonEntropy[{p1, p2, \[Ellipsis]}, {q1, q2, \[Ellipsis]}] returns the relative entropy between the two probability distributions {p1, p2, \[Ellipsis]} and {q1, q2, \[Ellipsis]}."

ShannonEntropy::noprb = "`` does not seem to be a probability distribution."

ShannonEntropy[pp_?VectorQ] :=
  (Message[ShannonEntropy::noprb, pp]; 0) /;
  AnyTrue[pp, Negative]

ShannonEntropy[pp_?VectorQ, qq_?VectorQ] :=
  (Message[ShannonEntropy::noprb, pp]; 0) /;
  AnyTrue[pp, Negative]

ShannonEntropy[pp_?VectorQ, qq_?VectorQ] :=
  (Message[ShannonEntropy::noprb, qq]; 0) /;
  AnyTrue[qq, Negative]

ShannonEntropy[pp_?VectorQ] := Total[WeightedLog @ pp]

ShannonEntropy[pp_?VectorQ, qq_?VectorQ] :=
  Total[WeightedLog[pp, qq]] - Total[WeightedLog[pp]]


QuantumLog::usage = "QuantumLog[p, q] returns -Tr[p ** Log[2, q]] for the observables p and q.\nQuantumLog[p, q, {s1, s2, \[Ellipsis]}] assumes that states p and q, either density operators or ket vectors, are defined for the systems {s1, s2, \[Ellipsis]}.\nQuantumLog is a low-level mathematical function intended for the use in VonNeumannEntropy or related functions."

QuantumLog[a_?VectorQ, b_?VectorQ] :=
  If[Fidelity[a, b] == 1, 0, Infinity]

QuantumLog[a_?MatrixQ, b_?VectorQ] := Module[
  {val, vec},
  {val, vec} = Transpose @ Select[Transpose @ Eigensystem[a], First[#] > 0&];
  If[ Length[val] > 1, Return[Infinity] ];

  vec = Flatten[vec];
  If[ AllTrue[vec, NumericQ], vec = Normalize[vec] ];
  If[ Fidelity[vec, b] == 1, 0, Infinity ]
 ]

QuantumLog[a_?VectorQ, b_?MatrixQ] := Module[
  {val, vec},
  {val, vec} = Eigensystem[b];
  If[ AllTrue[Flatten @ vec, NumericQ] && Not[UnitaryMatrixQ @ vec],
    vec = Orthogonalize[vec]
   ];
  Total @ WeightedLog[Abs[Conjugate[a] . Transpose[vec]]^2, val]
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

QuantumLog[a_, b_] := QuantumLog[a, b, Agents @ {a, b}]


VonNeumannEntropy::usage = "VonNeumannEntropy[mat|vec] returns the base 2 VonNeumann entropy of the quantum state described by the density matrix 'mat' or vector 'vec'.\nVonNeumannEntropy[mat1, mat2] returns the quantum relative entropy of the mixed state mat1 with respect to mat2."

VonNeumannEntropy[vec_?VectorQ] = 0

VonNeumannEntropy[mat_?MatrixQ] := ShannonEntropy[Eigenvalues @ mat]


VonNeumannEntropy[rho_, S_?SpeciesQ] := VonNeumannEntropy[rho, {S}]

VonNeumannEntropy[rho_, ss:{___?SpeciesQ}] :=
  VonNeumannEntropy @ Matrix[rho, ss]

VonNeumannEntropy[rho_] :=
  VonNeumannEntropy[rho, Agents @ rho]


VonNeumannEntropy[rho_, sgm_, S_?SpeciesQ] :=
  VonNeumannEntropy[rho, sgm, {S}]

VonNeumannEntropy[rho_, sgm_, ss:{___?SpeciesQ}] :=
  QuantumLog[rho, sgm, ss] - VonNeumannEntropy[rho, ss]

VonNeumannEntropy[rho_, sgm_] :=
  VonNeumannEntropy[rho, sgm, Agents @ {rho, sgm}]


(**** <MutualInformation> ****)

MutualInformation::usage = "MutualInformation[p] returns the classical information between two random variables X and Y associated with the joint probability distriubtion {p(xi,yj):i=1,2,\[Ellipsis]; j=1,2,\[Ellipsis]}.\nMutualInformation[rho, {s1,s2,\[Ellipsis]}] returns the mutual information between the system consisting of {s1,s2,\[Ellipsis]} and the rest in the state rho."

MutualInformation[p_?MatrixQ] :=
  ShannonEntropy[Total @ p] + ShannonEntropy[Total @ Transpose @ p] - 
  ShannonEntropy[Flatten @ p]


MutualInformation[rho_?MatrixQ, kk:{__Integer}] :=
  MutualInformation[rho, ConstantArray[2, Log[2, Length @ rho]], kk]

MutualInformation[rho_?MatrixQ, dd:{__Integer}, kk:{__Integer}] := With[
  { cc = Supplement[Range @ Length @ dd, kk] },
  VonNeumannEntropy[PartialTrace[rho, dd, kk]] +
    VonNeumannEntropy[PartialTrace[rho, dd, cc]] - 
    VonNeumannEntropy[rho]
 ]


MutualInformation[rho_, S_?SpeciesQ] := MututalInformation[rho, {S}]

MutualInformation[rho_, ss:{__?SpeciesQ}] := Module[
  { qq = Agents @ {rho, FlavorNone @ ss},
    rr },
  rr = Supplement[qq, FlavorNone @ ss];
  VonNeumannEntropy[PartialTrace[rho, rr], ss] +
    VonNeumannEntropy[PartialTrace[rho, ss], rr] -
    VonNeumannEntropy[rho, qq]
 ]

(**** </MutualInformation> ****)


(**** <RenyiEntropy> ****)

RenyiEntropy::usage = "RenyiEntropy[\[Alpha], {p1,p2,\[Ellipsis]}] returns the Renyi entropy of order \[Alpha] for a random variable with associated probability distribution {p1,p2,\[Ellipsis]}.\nRenyiEntropy[\[Alpha],\[Rho]] returns the quantum Renyie entropy of order \[Alpha] for density matrix \[Rho].\nRenyiEntropy[\[Alpha],\[Rho],\[Sigma]] returns the relative Renyi entropy of density matrix \[Rho] with respect to another density matrix \[Sigma].\nRenyiEntropy[\[Alpha], \[Rho], {s1,s2,\[Ellipsis]}] or RenyiEntropy[\[Alpha], \[Rho], \[Sigma]] allows to specify otherwise unclear systems by {s1,s2,\[Ellipsis]}."

RenyiEntropy[1, pp_?VectorQ] := ShannonEntropy[pp]

RenyiEntropy[a_?Positive, pp_?VectorQ] := Log2[Norm[pp, a]] * a / (1 - a)


RenyiEntropy[1, rho_?MatrixQ] := VonNeumannEntropy[rho]

RenyiEntropy[a_?Positive, rho_?MatrixQ] :=
  Log2[Tr @ MatrixPower[rho, a]] / (1 - a)


RenyiEntropy[1, pp_?VectorQ, qq_?VectorQ] := ShannonEntropy[pp, qq]

RenyiEntropy[a_?Positive, pp_?VectorQ, qq_?VectorQ] := With[
  { n = Max[Length @ pp, Length @ qq] },
  Log2[ Norm[PadRight[pp, n] * Power[PadRight[qq, n], (1-a)/a], a] ] *
    a / (a - 1)
 ]

RenyiEntropy[1, rho_?MatrixQ, sgm_?MatrixQ] := VonNeumannEntropy[rho, sgm]

RenyiEntropy[a_?Positive, rho_?MatrixQ, sgm_?MatrixQ] :=
  Log2[ Tr @ MatrixPower[
      Dot[
        MatrixPower[sgm, (1-a)/(2*a)], rho,
        MatrixPower[sgm, (1-a)/(2*a)]
       ], a ] ] / (a - 1)


RenyiEntropy[a_, rho_] := RenyiEntropy[a, rho, Agents @ rho]

RenyiEntropy[a_, rho_, S_?SpeciesQ] := RenyiEntropy[a, rho, {S}]

RenyiEntropy[a_, rho_, ss:{___?SpeciesQ}] :=
  RenyiEntropy[a, Matrix[rho, ss]]


RenyiEntropy[a_, rho_, sgm_, S_?SpeciesQ] :=
  RenyiEntropy[a, rho, sgm, {S}]

RenyiEntropy[a_, rho_, sgm_] :=
  RenyiEntropy[a, rho, sgm, Agents @ {rho, sgm}]

RenyiEntropy[a_, rho_, ss:{___?SpeciesQ}] :=
  RenyiEntropy[a, Matrix[rho, ss], Matrix[sgm, ss]]

(**** </RenyiEntropy> ****)

End[]

EndPackage[]
