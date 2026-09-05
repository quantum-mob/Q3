(* ::Package:: *)
(* Block Jacobi method for complex skew-symmetric matrices.
   Reference: A. Humeniuk, R. Mitric, Comput. Phys. Commun. 231 (2018) 187-197. *)

BeginPackage["QuantumMob`Q3`", {"System`"}];

{ SkewJacobiDecomposition, SkewJacobiSolve };

Begin["`Private`"];

(* Householder reflection:
   Returns the Householder vector v such that Uh = 1 - 2 v.v^H/(v^H.v),
   applied as A' = Transpose[Uh].A.Uh, annihilates the elements of column j
   below row i. Returns None if there is nothing to annihilate. *)
(* cf. QuantumMob`Q3`HouseholderMatrix *)
householderVector[A_, {i_Integer, j_Integer}] := 
  HouseholderVector[A[[All, j]], i];


(* Complex Jacobi rotation tangents *)
solveQuadraticPair[alpha_, beta_, gamma_] := Module[
  { aa, bb, gg, p, q, disc, r1, r2, t1, t2 },
  If[alpha == 0. && beta == 0., Return[{0. + 0. I, 0. + 0. I}]];
  aa = Abs[alpha]^2; bb = Abs[beta]^2; gg = Abs[gamma]^2;
  If[Abs[alpha] > Abs[beta],
   (* solve Eq. (81) for t2 *)
   p = (-aa + bb + gg)/(alpha Conjugate[gamma]);
   q = -(Conjugate[alpha] gamma)/(alpha Conjugate[gamma]);
   disc = Sqrt[p^2 - 4 q];
   r1 = (-p + disc)/2; r2 = (-p - disc)/2;
   (* root maximizing |t2 alpha + gamma| *)
   t2 = If[Abs[r1 alpha + gamma] >= Abs[r2 alpha + gamma], r1, r2];
   t1 = Conjugate[beta]/Conjugate[t2 alpha + gamma],      (* Eq. (78) *)
   (* else: solve Eq. (80) for t1 *)
   p = (aa - bb + gg)/(beta Conjugate[gamma]);
   q = -(Conjugate[beta] gamma)/(beta Conjugate[gamma]);
   disc = Sqrt[p^2 - 4 q];
   r1 = (-p + disc)/2; r2 = (-p - disc)/2;
   t1 = If[Abs[r1 beta + gamma] >= Abs[r2 beta + gamma], r1, r2];
   t2 = Conjugate[alpha]/Conjugate[t1 beta + gamma]       (* Eq. (79) *)
   ];
  {t1, t2}
];

jacobiMatrix[t1_, t2_] := Module[
  { c1, c2, s1, s2 },
  c1 = 1./Sqrt[1. + Abs[t1]^2]; 
  c2 = 1./Sqrt[1. + Abs[t2]^2];
  s1 = c1 t1; 
  s2 = c2 t2;
  { {c1, s1, 0., 0.},
    {-Conjugate[s1], c1, 0., 0.},
    {0., 0., c2, s2},
    {0., 0., -Conjugate[s2], c2} 
  } 
];

permMatrix[n_, i_, j_] := Module[
  { P = N[IdentityMatrix[n]] }, 
  P[[{i, j}]] = P[[{j, i}]]; 
  P
];

(* The 4x4 subproblem: 
   Find unitary Ubar with Transpose[Ubar].Abar.Ubar in Murnaghan form *)
solveFourByFour[Abar_] := Module[
  { A = N[Abar], 
    U = N[IdentityMatrix[4]], 
    v, Uh, P24, P23, Pw, alpha, beta, gamma, t1, t2, Uj, Us, d },
  (* two Householder reflections -> tridiagonal (Eq. 63) *)
  Do[
    v = householderVector[A, ij];
    If[v =!= None,
      Uh = ReflectionMatrix[v]; (* Householder reflection *)
      A = Transpose[Uh].A.Uh;
      U = U.Uh
    ],
    {ij, {{2, 1}, {3, 2}}}
  ];
  (* Jacobi rotation on the permuted matrix (Eqs. 64-91) *)
  If[ A[[2, 3]] != 0.,
    P24 = permMatrix[4, 2, 4]; P23 = permMatrix[4, 2, 3];
    Pw = P24.P23;
    A = Transpose[Pw].A.Pw; U = U.Pw;                     (* Eq. (65) *)
    alpha = A[[2, 3]];                                    (* = a34 *)
    beta = A[[1, 4]];                                     (* = a12 *)
    gamma = A[[2, 4]];                                    (* = -a23 *)
    {t1, t2} = solveQuadraticPair[alpha, beta, gamma];
    Uj = jacobiMatrix[t1, t2];
    A = Transpose[Uj].A.Uj; U = U.Uj;                     (* -> form (88) *)
    A = Transpose[P23].A.P23; U = U.P23                   (* Eq. (91) *)
  ];
  (* complex scaling -> real non-negative diagonal blocks (Eq. 92) *)
  Us = N[IdentityMatrix[4]];
  Do[
    d = A[[idx, idx + 1]];
    If[d != 0., Us[[idx + 1, idx + 1]] = Conjugate[d]/Abs[d]],
    {idx, {1, 3}}
  ];
  U.Us
];

(* Off-diagonal block norm tau(A)^2 *)
tauSquared[A_, m_] := Total @ Flatten @ Table[
  If[ p != q,
    Total[Abs[A[[2 p - 1 ;; 2 p, 2 q - 1 ;; 2 q]]]^2, 2], 
    0.
  ],
  {p, m}, 
  {q, m}
];


(**** <SkewJacobiDecomposition> ****)
SkewJacobiDecomposition::usage = "SkewJacobiDecomposition[A] reduces a complex skew-symmetric matrix A of even dimension to Murnaghan's normal form. Returns {alphas, U} with unitary U such that Transpose[U].A.U is block-diagonal with 2x2 blocks {{0, alphas[[l]]}, {-alphas[[l]], 0}}. The alphas are the singular values of A, each of multiplicity two. Options: \"Tolerance\" (default 10.^-13), \"MaxSweeps\" (default 100).";

SkewJacobiDecomposition::odddim = "The matrix dimension must be even.";
SkewJacobiDecomposition::notskew = "The matrix must be skew-symmetric (Transpose[A] == -A).";
SkewJacobiDecomposition::noconv = "No convergence within `1` sweeps.";

Options[SkewJacobiDecomposition] = {
  "Tolerance" -> 10.^-13,
  "MaxSweeps" -> 100
};

SkewJacobiDecomposition[Ain_?MatrixQ, OptionsPattern[]] := Module[
  { A = N[Ain], 
    n, m, NN, U, normA, tol, maxSweeps,
    t2, thresh, rows, Abar, Ubar, w, Us, xi, s, sweep, converged, l },
  If[ Max[Abs[A + Transpose[A]]] > 10.^-12 Max[1., Max[Abs[A]]],
    Message[SkewJacobiDecomposition::notskew]; 
    Return[$Failed]
  ];
  n = Length[A];
  m = n/2;
  NN = A; 
  U = N[IdentityMatrix[n]];
  normA = Norm[A, "Frobenius"];
  If[normA == 0., Return[{ConstantArray[0., m], U}]];
  tol = OptionValue["Tolerance"];
  maxSweeps = OptionValue["MaxSweeps"];

  (* trivial n = 2 case (Eq. 20) *)
  If[m == 1,
    w = NN[[1, 2]];
    If[ w != 0.,
      Us = {{1., 0.}, {0., Conjugate[w]/Abs[w]}};
      NN = Transpose[Us].NN.Us; 
      U = U.Us
    ];
    Return[{{Abs[w]}, U}]
  ];

  converged = False;
  Do[
    t2 = tauSquared[NN, m];
    If[Sqrt[t2] <= tol normA, converged = True; Break[]];
    thresh = 0.5 t2/(m (m - 1));                          (* Eq. (42) *)
    Do[
      If[Total[Abs[NN[[2 p - 1 ;; 2 p, 2 q - 1 ;; 2 q]]]^2, 2] >= thresh,
        rows = {2 p - 1, 2 p, 2 q - 1, 2 q};
        Abar = NN[[rows, rows]];
        Ubar = solveFourByFour[Abar];
        (* generalized Jacobi rotation (Eq. 22), applied to the four
           affected rows/columns only *)
        NN[[All, rows]] = NN[[All, rows]].Ubar;
        NN[[rows, All]] = Transpose[Ubar].NN[[rows, All]];
        U[[All, rows]] = U[[All, rows]].Ubar
      ],
      {p, 1, m - 1}, 
      {q, p + 1, m}
    ],
    {sweep, maxSweeps}
  ];
  If[!converged, Message[SkewJacobiDecomposition::noconv, maxSweeps]];

  (* final complex scaling (Eq. 41): make all diagonal blocks
     real and non-negative *)
  Do[
    xi = NN[[2 l - 1, 2 l]];
    If[xi != 0. && (Im[xi] != 0. || Re[xi] < 0.),
      s = Conjugate[xi]/Abs[xi];
      NN[[All, 2 l]] *= s;
      NN[[2 l, All]] *= s;
      U[[All, 2 l]] *= s
    ],
    {l, m}
  ];

  { Re @ Table[NN[[2 l - 1, 2 l]], {l, m}], 
    U }
] /; If[ EvenQ[Length @ Ain], True,
  Message[SkewJacobiDecomposition::odddim]; False
];
(**** </SkewJacobiDecomposition> ****)


(**** <SkewJacobiSolve> ****)
SkewJacobiSolve::usage = "SkewJacobiSolve[A, b] solves A.x == b in the least-square (pseudoinverse) sense for a possibly singular complex skew-symmetric matrix A: singular values <= eps (default 10.^-8) are treated as zero and discarded in pairs, so that the skew-symmetric structure of the pseudoinverse is retained. SkewJacobiSolve[{alphas, U}, b, eps] reuses a decomposition previously computed with SkewJacobiDecomposition.";

Options[SkewJacobiSolve] = {
  "Threshold" -> 10.^-8,
  "Tolerance" -> 10.^-13,
  "MaxSweeps" -> 100
};

(* Least-square solution of A.x == b:
   Small singular values are removed in pairs. *)
SkewJacobiSolve[A_?MatrixQ, b_?VectorQ, OptionsPattern[]] :=
 SkewJacobiSolve[SkewJacobiDecomposition[A, opts], b, opts];

SkewJacobiSolve[{alphas_?VectorQ, U_?MatrixQ}, b_?VectorQ, OptionsPattern[]] := Module[
  { eps = OptionValue["Threshold"],
    m = Length[alphas],
    y, z },
  y = Transpose[U].N[b];
  z = ConstantArray[0. + 0. I, Length[b]];
  Do[
    If[alphas[[l]] > eps,
      (* inverse of {{0, a}, {-a, 0}} is {{0, -1/a}, {1/a, 0}} *)
      z[[2 l - 1]] = -y[[2 l]]/alphas[[l]];
      z[[2 l]] = y[[2 l - 1]]/alphas[[l]]
    ],
    {l, m}
  ];
  U.z
];
(**** </SkewJacobiSolve> ****)

End[];
EndPackage[];
