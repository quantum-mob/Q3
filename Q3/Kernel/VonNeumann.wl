(* -*- mode:math -*- *)
(* Package for stabilizer formalism *)

BeginPackage["Q3`"]

{ ShannonEntropy, ShannonLog };
{ VonNeumannEntropy, QuantumLog };
{ RenyiEntropy };

{ EntanglementEntropy, CrossEntropy };

{ MutualInformation };


Begin["`Private`"]

(**** <ShannonLog> ****)

ShannonLog::usage = "ShannonLog[b,z] returns -z*Log[b, z] for z\[NotEqual]0 and 0 for z=0.\nShannonLog[b, p, q] returns -p*Log[2, q] for p,q\[NotEqual]0, ShannonLog[b, 0, q] = 0 for p=0 and all q, and ShannonLog[p>0, 0] = \[Infinity] for and positive p and q=0."

SetAttributes[ShannonLog, Listable]


ShannonLog[_, 0] = 0

ShannonLog[_, _?ZeroQ] = 0

ShannonLog[base_, z_] := -z * Log[base, z]


ShannonLog[_, 0, _] = 0

ShannonLog[_, _?ZeroQ, _] = 0

ShannonLog[_?Positive, _?Positive, _?ZeroQ] = Infinity

ShannonLog[_, _, _?ZeroQ] = ComplexInfinity

ShannonLog[base_, p_, q_] := -p * Log[base, q]

(**** </ShannonLog> ****)


(**** <QuantumLog> ****)

QuantumLog::usage = "QuantumLog[b, rho] retruns -Tr[rho ** Log[b, rho]].\nQuantumLog[b, rho, sgm] returns -Tr[rho ** Log[b, sgm]] for density operators rho and sgm.\nQuantumLog[b, rho, {s1, s2, \[Ellipsis]}] or QuantumLog[b, rho, sgm, {s1, s2, \[Ellipsis]}] assumes that states rho and sgm, either density operators or ket vectors, are defined for systems {s1, s2, \[Ellipsis]}.\nQuantumLog is a low-level mathematical function intended for the use in VonNeumannEntropy or related functions."

QuantumLog[base_, mat_?MatrixQ] := Total @ ShannonLog[base, Eigenvalues @ mat]


QuantumLog[_?Positive, a_?VectorQ, b_?VectorQ] :=
  If[Fidelity[a, b] == 1, 0, Infinity]

QuantumLog[_?Positive, a_?MatrixQ, b_?VectorQ] := Module[
  {val, vec},
  {val, vec} = Transpose @ Select[Transpose @ Eigensystem[a], First[#] > 0&];
  If[ Length[val] > 1, Return[Infinity] ];

  vec = Flatten[vec];
  If[ AllTrue[vec, NumericQ], vec = Normalize[vec] ];
  If[ Fidelity[vec, b] == 1, 0, Infinity ]
]

QuantumLog[base_, a_?VectorQ, b_?MatrixQ] := Module[
  {val, vec},
  {val, vec} = Eigensystem[b];
  If[ MatrixQ[vec, NumericQ] && Not[UnitaryMatrixQ @ vec],
    vec = Orthogonalize[vec]
  ];
  Total @ ShannonLog[base, Abs[Conjugate[a] . Transpose[vec]]^2, val]
]

QuantumLog[base_, a_?MatrixQ, b_?MatrixQ] := Module[
  { aval, avec,
    bval, bvec },
  {aval, avec} = Eigensystem[a];  
  If[ MatrixQ[avec, NumericQ] && Not[UnitaryMatrixQ @ avec],
    avec = Orthogonalize[avec]
  ];
  {bval, bvec} = Eigensystem[b];
  If[ MatrixQ[bvec, NumericQ] && Not[UnitaryMatrixQ @ bvec],
    bvec = Orthogonalize[bvec]
  ];
  Total @ ShannonLog[base, aval . Abs[Conjugate[avec] . Transpose[bvec]]^2, bval]
]


QuantumLog[base_, rho_, ss:{___?SpeciesQ}] :=
  QuantumLog[base, Matrix[rho, ss]]

QuantumLog[base_, a_, b_, ss:{___?SpeciesQ}] :=
  QuantumLog[base, Matrix[a, ss], Matrix[b, ss]]

QuantumLog[base_, a_, b_] := QuantumLog[base, a, b, Agents @ {a, b}]

(**** </QuantumLog> ****)


(**** <ShannonEntropy> ****)

ShannonEntropy::usage = "ShannonEntropy[{p1, p2, \[Ellipsis]}] returns the base 2 Shannon entropy of the probability distribution {p1, p2, \[Ellipsis]}.\nShannonEntropy[{p1, p2, \[Ellipsis]}, {q1, q2, \[Ellipsis]}] returns the relative entropy between the two probability distributions {p1, p2, \[Ellipsis]} and {q1, q2, \[Ellipsis]}."

ShannonEntropy::noprb = "`` does not seem to be a probability distribution."

ShannonEntropy[pp_?VectorQ] :=
  (Message[ShannonEntropy::noprb, pp]; 0) /;
  Not @ AllTrue[Chop @ pp, NonNegative]

ShannonEntropy[pp_?VectorQ] := Total @ ShannonLog[2, pp]


ShannonEntropy[pp_?VectorQ, qq_?VectorQ] :=
  (Message[ShannonEntropy::noprb, pp]; 0) /;
  Not @ AllTrue[Chop @ pp, NonNegative]

ShannonEntropy[pp_?VectorQ, qq_?VectorQ] :=
  (Message[ShannonEntropy::noprb, qq]; 0) /;
  Not @ AllTrue[Chop @ qq, NonNegative]

ShannonEntropy[pp_?VectorQ, qq_?VectorQ] :=
  Total[ShannonLog[2, pp, qq]] - Total[ShannonLog[2, pp]]

(**** </ShannonEntropy> ****)


(**** <VonNeumannEntropy> ****)

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
  QuantumLog[2, rho, sgm, ss] - VonNeumannEntropy[rho, ss]

VonNeumannEntropy[rho_, sgm_] :=
  VonNeumannEntropy[rho, sgm, Agents @ {rho, sgm}]

(**** </VonNeumannEntropy> ****)


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


MutualInformation[rho_, S_?SpeciesQ] := MutualInformation[rho, {S}]

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
       ], a ] 
  ] / (a - 1)


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


(**** <EntanglementEntropy> ****)

EntanglementEntropy::usage = "EntanglementEntropy[vec, {d1, d2, \[Ellipsis]}, {k1, k2, \[Ellipsis]}] returns the entanglement entropy in pure state 'vec' between subsystem k1, k2, \[Ellipsis] and the rest. The subsystems are assumed to be associated with the Hilbert spaces with dimensions d1, d2, \[Ellipsis].\nEntanglementEntropy[vec, {k1, k2, \[Ellipsis]}] assumes that the subsystems are qubits.\nEntanglementEntropy[expr, {k1, k2, \[Ellipsis]}] assumes that 'expr' is a ket expression for unlabelled qubits k1, k2, \[Ellipsis].\nEntanglementEntropy[expr, {s1, s2, \[Ellipsis]}] assumes subsystems specified by species {s1, s2, \[Ellipsis]}."

EntanglementEntropy::qubit = "`` does not seem to be a vector or matrix for qubits."

EntanglementEntropy[rho:(_?VectorQ|_?MatrixQ), jj:{__Integer}] := (
  Message[EntanglementEntropy::qubit, rho];
  rho
) /; Not @ IntegerQ @ Log[2, Length @ rho]

EntanglementEntropy[rho:(_?VectorQ|_?MatrixQ), jj:{__Integer}] :=
  EntanglementEntropy[rho, ConstantArray[2, Log[2, Length @ rho]], jj]

EntanglementEntropy[rho:(_?VectorQ|_?MatrixQ),
  dd:{__Integer}, jj:{__Integer}] :=
  VonNeumannEntropy @ PartialTrace[rho, dd, Complement[Range[Length @ dd], jj]]


EntanglementEntropy[expr_, S_?SpeciesQ] := EntanglementEntropy[expr, {S}]

EntanglementEntropy[expr_, ss:{__?SpeciesQ}] := Module[
  { qq = Agents[expr],
    rr = Agents[FlavorNone @ ss],
    jj },
  qq = Union[qq, rr];
  jj = Flatten @ Map[FirstPosition[qq, #]&, Complement[qq, rr]];
  VonNeumannEntropy @ PartialTrace[Matrix[expr, qq], Dimension[qq], jj]
]


EntanglementEntropy[expr_, jj:{__Integer}] := Module[
  { nn = Length @ FirstCase[expr, _Ket, Infinity] },
  VonNeumannEntropy @ PartialTrace[Matrix[expr], Complement[Range @ nn, jj]]
] /; fPauliKetQ[expr]

EntanglementEntropy[expr_, jj:{__Integer}] := Module[
  { nn = Length @ FirstCase[expr, _Pauli, Infinity] },
  VonNeumannEntropy @ PartialTrace[Matrix[expr], Complement[Range @ nn, jj]]
] /; Not @ FreeQ[expr, _Pauli]

(**** </EntanglementEntropy> ****)


(**** <CrossEntropy> ****)

CrossEntropy::usage = "CrossEntropy[{p1, p2, \[Ellipsis]}, {q1, q2, \[Ellipsis]}] returns the classical cross-entropy between two probability distributions {p1, p2, \[Ellipsis]} and {q1, q2, \[Ellipsis]}.\nCrossEntropy[rho, sgm] returns the quantum cross-entropy between two density matrices rho and sgm."

CrossEntropy[pp_?VectorQ, qq_?VectorQ] := Total @ ShannonLog[2, pp, pp]

CrossEntropy[rho_?MatrixQ, sgm_?MatrixQ] := QuantumLog[2, rho, sgm]

CrossEntropy[rho_, sgm_] := With[
  { ss = Agents @ {rho, sgm} },
  QuantumLog[2, Matrix[rho, ss], Matrix[sgm, ss]]
]

(**** </CrossEntropy> ****)

End[]

EndPackage[]
