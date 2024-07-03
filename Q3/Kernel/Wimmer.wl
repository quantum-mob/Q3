(* Algorithms to calculate the Pfaffian of skew-symmetric matrices. *)
(* Source: M. Wimmer, ACM Transactions on Mathematical Software, Vol. 38, No. 4, Article 30 (2012), "Algorithm 923: Efficient Numerical Computation of the Pfaffian for Dense and Banded Skew-Symmetric Matrices." *)

BeginPackage["Q3`"]

{ Pfaffian, SkewTridiagonalize };

{ Zero, One }; (* mainly in Pauli *)

{ PfaffianMine };


Begin["`Private`"]

(**** <array tools> ****)
(**** REMARK:
  Depending on the type of entries, different methods must chosen. However, for large arrays, the type test itself takes time. Therefore, it is important to have an efficient test method.
  *)

arrayRealQ::usage = "\
arrayRealQ[array] returns True if array is an array of real numbers.\n\
arrayRealQ[array, test] first invokes ArrayQ[array, 1|2, test]."

arrayRealQ[obj_, test_] := And[
  ArrayQ[obj, 1|2, test],
  arrayRealQ[obj]
]

arrayRealQ[obj_SymmetrizedArray] :=
  FreeQ[Values @ SymmetrizedArrayRules @ obj, _Complex]

arrayRealQ[obj_SparseArray] :=
  FreeQ[obj["ExplicitValues"], _Complex]

arrayRealQ[obj_] :=
  FreeQ[obj, _Complex]
(* NOTE: FreeQ is much fastern than, e.g., MatrixQ[obj, Not[MatchQ[#, _Complex]]&] *)

(**** </array tools> ****)


(**** <Pfafian> ****)

Pfaffian::usage = "Pfaffian[mat] returns the Pfaffian of an anti-symmetric matrix mat."

Pfaffian::method = "Unrecognized option `1`; must be Automatic, \"Parlett-Reid\", \"Householder\", \"Hessenberg\" or \"Heuristic\".";

Pfaffian::number = "Non-numerical matrix `` is given; Pfaffian can be computed efficiently only for a numerical matrix. If the matrix is small enough, try option Method -> \"Heuristic\"."

Pfaffian::Hessenberg = "Pfaffian computation with Hessenberg decomposition only works for real matrices of finite precision; using the Parlett-Reid method instead.";

Pfaffian::sparse = "Too density for a sparse array; converted to a normal form."

Options[Pfaffian] = {Method -> Automatic}


Pfaffian[mat_SymmetrizedArray, opts:OptionsPattern[]] :=
  Pfaffian[SparseArray @ mat, opts]
(* NOTE: The current implementation of Pfaffian breaks the structured array. *)

Pfaffian[mat_SparseArray, opts:OptionsPattern[]] :=
  ( Message[Pfaffian::sparse];
    Pfaffian[Normal @ mat, opts] 
  ) /; mat["Density"] > 0.2


Pfaffian[mat_?SquareMatrixQ, OptionsPattern[]] := 0 /; OddQ[Length @ mat]

Pfaffian[mat_?SquareMatrixQ, OptionsPattern[]] :=
  PfaffianHeuristic[mat] /; OptionValue[Method] == "Heuristic"


Pfaffian[mat_, OptionsPattern[]] :=
  Switch[ OptionValue[Method],
    Automatic,
      If[ arrayRealQ[mat],
        PfaffianHessenberg[N @ mat],
        PfaffianLTL[mat]
      ],
    "Parlett-Reid", PfaffianLTL[mat],
    "Householder", PfaffianHouseholder[mat], 
    "Hessenberg", PfaffianHessenberg[mat],
    _, Message[Pfaffian::method, OptionValue @ Method]; 0
  ] /; MatrixQ[mat, NumericQ]

(**** </Pfaffian> ****)


(**** <SkewTridiagonalize> ****)

SkewTridiagonalize::usage = "SkewTridiagonalize[mat] tridiagonalizes the skew-symmetric matrix mat and returns {T, L, P} such that P.mat.P^T = L.T.L^T, where T is a skew-symmetric tridiagonal matrix.\nIn the Parlett-Reid method, L is a unit lower triangular matrix and P is a permutation matrix.\nIn the Householder method, L is a unitary matrix and P is the identity matrix."

SkewTridiagonalize::method = "Unrecognized option `1`; must be Automatic, \"Parlett-Reid\", \"Householder\", \"Hessenberg\" or \"Heuristic\".";

SkewTridiagonalize::number = "Non-numerical matrix `` is given; the tridiagonalization can be computed efficiently only for a numerical matrix."

SkewTridiagonalize::Hessenberg = "SkewTridiagonalize with the Hessenberg decomposition only works for real matrices; instead, using Householder method.";


Options[SkewTridiagonalize] = {Method -> Automatic}

SkewTridiagonalize[mat_, OptionsPattern[]] :=
  Switch[ OptionValue[Method],
    Automatic,
      Which[
        arrayRealQ[mat], SkewHessenberg[N @ mat], (* cf. SkewHouseholderReal *)
        True, SkewLTL[mat]
      ],
    "Parlett-Reid", SkewLTL[mat],
    "Householder", SkewHouseholder[mat], 
    "Hessenberg", SkewHessenberg[mat],
    _, Message[Skew::method, OptionValue @ Method]; 0
  ] /; MatrixQ[mat, NumericQ]

(**** </SkewTridiagonalize> ****)


(**** <PositionLargest> ****)

(* PosiitionLargest used in PfaffianLTL and SkewLTL was introduced Mathematica v13.2. *)

If[ $VersionNumber < 13.2,
  PositionLargest[list_?VectorQ] := FirstPosition[Normal @ list, Max @ list]
  (* NOTE: Normal is required here for older versions of Mathematica. *)
];

(**** </PositionLargest> ****)


(**** <Method: Parlett-Reid tridiagonalization> ****)

PfaffianLTL::usage = "PfaffianLTL[mat] computes the Pfaffian of the skew-symmetric matirx mat using the L T L^T decomposition."

PfaffianLTL[mat_] := Module[
  { new = mat,
    val = 1,
    pos, aa, bb },
  If[OddQ[Length @ new], Return[0]];
  While[ Length[new] > 2,
    pos = First @ PositionLargest[Abs @ First @ new];
    If[ZeroQ @ new[[1, pos]], Return[0]];
    If[ pos != 2,
      new[[{2, pos}, ;;]] = new[[{pos, 2}, ;;]]; 
      new[[;;, {2, pos}]] = new[[;;, {pos, 2}]];
      val *= -1
    ];
    val *= new[[1, 2]];

    aa = new[[1, 3;;]] / new[[1, 2]];
    bb = new[[2, 3;;]];
    new = new[[3;;, 3;;]];
    new -= (# - Transpose[#]&) @ Outer[Times, aa, bb];
  ];
  Return[val * new[[1, 2]]]
] /; MatrixQ[mat, NumericQ]

PfaffianLTL[mat_] := (
  Message[Pfaffian::number, mat];
  Return[Indeterminate]
)


SkewLTL::usage = "SkeyLTL[mat] computes the L T L^T decomposition of skew-symmetric matrix mat using the Parlett-Reid algorithm, and returns T, L and P, where T is a tridiagonal matrix, L a unit lower triangular matrix and P a permutation matrix such that P A P^T=L T L^T."

(* NOTE: This function is not needed for the Pfaffian computation, but is only provided for demonstration purposes. *)
SkewLTL[Mat_] := Module[
  {A, L, Pv, N, ip},
  A = Mat;
  N = Dimensions[A][[1]];
  L = IdentityMatrix[N];
  Pv = Range[N];
  For[ i = 1, i < N - 1, i++,
    (* Find the maximum entry in column i, starting from row i+1. *)
    ip = i + First @ PositionLargest[Abs @ A[[i+1;;, i]]];
    (* if the maximum entry is not at i+1, permute the matrix so that it is. *)
    If[i + 1 != ip, 
      (* Interchange rows and columns in A *)
      A[[{i + 1, ip}, ;;]] = A[[{ip, i + 1}, ;;]]; 
      A[[;; , {i + 1, ip}]] = A[[;; , {ip, i + 1}]];
      (*interchange rows in L; this amounts to accumulating the product of individual Gauss eliminations and permutations*)
      L[[{i + 1, ip}, 1 ;; i]] = L[[{ip, i + 1}, 1 ;; i]];
      (*Accumulate the total permutation matrix*)
      Pv[[{i + 1, ip}]] = Pv[[{ip, i + 1}]];
    ];
    (* Build the Gauss vector *)
    L[[i + 2 ;;, i + 1]] = A[[i + 2 ;;, i]]/A[[i + 1, i]];
    (*Row and column i are eliminated*)
    A[[i + 2 ;;, i]] = 0; A[[i, i + 2 ;;]] = 0;
    (* Update the remainder of the matrix using an outer product skew-symmetric update. Note that column and row i+1 are not affected by the update. *)
    A[[i + 2 ;; , i + 2 ;; ]] += 
      Transpose[{L[[i + 2 ;;, i + 1]]}] . {A[[i + 2 ;;, i + 1]]} - 
        Transpose[{A[[i + 2 ;;, i + 1]]}] . { L[[i + 2 ;;, i + 1]]};
  ];
  Return[{A, L, SparseArray[{i_, i_} -> 1, {N, N}][[Pv]]}]
]

(**** </Method: Parlett-Reid tridiagonalization> ****)


(**** <Method: Householder tridiagonalization> ****)

HouseholderVector::usage = "HouseholderVector[vec] returns the Householder vector w of input vector vec; such that (I-2w w^\[Dagger]/w^\[Dagger]\[CenterDot]w) vec is a multiple of the unit vector Subscript[e, 1]."

HouseholderVector[vec_?VectorQ] := If[
  arrayRealQ[vec],
  HouseholderVectorReal[vec],
  HouseholderVectorComplex[vec]
]

HouseholderVectorReal[x_] := Module[
  { nrm = Norm[x],
    new, fac },
  If[ nrm == 0, 
    Return[{UnitVector[Lenth @ x, 1], 0, 0}],
    fac = If[x[[1]] > 0, nrm, -nrm];
    new = x;
    new[[1]] += fac;
    Return[{Normalize[new], 2, -fac} ]
  ]
]

HouseholderVectorComplex[x_] := Module[
  { nrm = Norm[x],
    new, fac },
  If[ nrm == 0,
    Return[{UnitVector[Lenth @ x, 1], 0, 0}],
    fac = nrm * Exp[I * Arg[First @ x]]; 
    new = x;
    new[[1]] += fac;
    Return[{Normalize[new], 2, -fac} ]
  ]
]


PfaffianHouseholder::usage = "PfaffianHouseholder[mat] calculates the Pfaffian of skew-symmetric matrix mat by using the Householder tridiagonalization."

PfaffianHouseholder[mat_] := If[
  arrayRealQ[mat], 
  PfaffianHouseholderReal[mat], 
  PfaffianHouseholderComplex[mat]
]

PfaffianHouseholderReal[mat_] := Module[
  { new = mat,
    dim = Length @ mat,
    val, v, w, beta, alpha },
  If[OddQ[dim], Return[0]];
  val = 1;
  For[i = 1, i < dim-1, i += 2,
    (* Compute the Householder vector. *) 
    {v, beta, alpha} = HouseholderVectorReal[new[[i+1 ;; , i]]];
    (* multiply with off-diagonal entry and determinant of Householder reflection *) 
    val *= If[beta == 0, 1, -1]*(-alpha);
    (* Update the matrix *)
    w = beta * new[[i+1 ;; , i+1 ;;]] . v; 
    new[[i+1 ;; , i+1 ;; ]] += Transpose[{v}] . {w} - Transpose[{w}] . {v}
  ]; 
  Return[ val * new[[dim-1, dim]] ]
]

PfaffianHouseholderComplex[mat_] := Module[
  { new = mat,
    dim = Length @ mat,
    val, v, w, beta, alpha },
  val = 1;
  If[OddQ[dim], Return[0]];
  For[i = 1, i < dim-1, i += 2, 
    (* Compute the Householder vector. *) 
    {v, beta, alpha} = HouseholderVectorComplex[new[[i+1 ;; , i]]]; 
    (* multiply with off-diagonal entry and determinant of Householder reflection *) 
    val *= If[beta == 0, 1, -1]*(-alpha);
    (* Update the matrix. *)
    w = beta * new[[i+1 ;; , i+1 ;;]] . Conjugate[v]; 
    new[[i+1 ;; , i+1 ;; ]] += Transpose[{v}] . {w} - Transpose[{w}] . {v}
  ]; 
  Return[ val * new[[dim-1, dim]] ]
]


SkewHouseholder::usage = "SkewHouseholder[mat] returns {T, Q} such that mat=Q T Q^T for a skew-symmetric matrix mat, where T is a skew-symmetric tridiagonal matrix and Q is a unitary matrix.\nFor real matrices, this should be the same as what is returned from the HessenbergDecomposition.\nFor the complex case, there is no Mathematica equivalent.\nThis full tridiagonalization is at the heart of the Pfaffian calculation in the Householder method."

SkewHouseholder[mat_?MatrixQ] := If[
  arrayRealQ[mat], 
  SkewHouseholderReal[mat],
  SkewHouseholderComplex[mat]
]

(* NOTE: These functions are not needed for the Pfaffian calculation, they are here merely for testing. *)
(* NOTE: These functions don't check (yet) if the input matrix is really skew-symmetric. *)

SkewHouseholderReal[mat_] := Module[
  {A, Q, v, beta, alpha},
  A = mat;
  Q = IdentityMatrix[Dimensions[A][[1]]];
  For[i = 1, i < Dimensions[A][[1]] - 1, i++, 
    (*Compute the Householder vector*)
    {v, beta, alpha} = HouseholderVectorReal[A[[i + 1 ;; , i]]];
    (*eliminate the entries in row and column i*) 
    A[[i + 1, i]] = alpha;
    A[[i, i + 1]] = -alpha;
    A[[i + 2 ;;, i]] = 0; 
    A[[i, i + 2 ;;]] = 0;
    (* update the matrix *)
    w = beta * A[[i + 1 ;; , i + 1 ;;]] . v; 
    A[[i + 1 ;; , i + 1 ;; ]] += Transpose[{v}] . {w} - Transpose[{w}] . {v};
    (*accumulate the Householder reflections into the full transformation*)
    y = Q[[1 ;;, i + 1 ;;]] . v; 
    Q[[1 ;; , i + 1 ;;]] -= beta*Transpose[{y}] . {v}
  ]; 
  Return[{A, Q, One @ Length @ mat}]
]

SkewHouseholderComplex[mat_] := Module[
  {A, Q, v, beta, alpha},
  A = mat;
  Q = IdentityMatrix[Dimensions[A][[1]]];
  For[i = 1, i < Dimensions[A][[1]] - 1, i++, 
    (*Compute the Householder vector*)
    {v, beta, alpha} = HouseholderVectorComplex[A[[i + 1 ;; , i]]]; 
    (*eliminate the entries in row and column i*) 
    A[[i + 1, i]] = alpha;
    A[[i, i + 1]] = -alpha;
    A[[i + 2 ;;, i]] = 0; 
    A[[i, i + 2 ;;]] = 0;
    (*update the matrix*)
    w = beta* A[[i + 1 ;; , i + 1 ;;]] . Conjugate[v]; 
    A[[i + 1 ;; , i + 1 ;; ]] += Transpose[{v}] . {w} - Transpose[{w}] . {v};
    (*accumulate the Householder reflections into the full transformation*)
    y = Q[[1 ;;, i + 1 ;;]] . v; 
    Q[[1 ;; , i + 1 ;;]] -= beta*Transpose[{y}] . Conjugate[{v}]
  ]; 
  Return[{A, Q, One @ Length @ mat}]
]

(**** </Method: Householder tridiagonalization> ****)


(**** <Method: Hessenberg decomposition> ****)

(* Essentially the same as the Householder tridiagonalization. *)

(* For real matrices, the Pfaffian can also be computed using the Hessenberg decomposition. Since the Hessenberg decomposition is implemented efficiently in Mathematica (in contrast to the above implementation of Householder tridiagonalization), this approach is usually fastest for real matrices. For complex matrices there is no alternative and the algorithms here are the only option. *)

PfaffianHessenberg::usage = "PfaffianHessenberg[mat] calculates the Pfaffian of real skew-symmetric matrix mat by using the Hessenberg decomposition."

(* NOTE: HessenbergDecomposition only receives a finite-preciesion matrix. *)
PfaffianHessenberg[mat_?arrayRealQ] := Module[
  {H, Q},
  {Q, H} = HessenbergDecomposition[N @ mat];
  Det[Q] * Apply[Times, Diagonal[H, 1][[1;; ;;2]]]
]

PfaffianHessenberg[mat_] := (
  Message[Pfaffian::Hessenberg];
  PfaffianLTL[mat]
)


SkewHessenberg::usage = "SkewHessenberg[mat] tridiagonalize the real skew-symmetric matrix mat by using the Hessenberg decomposition.\nIt is an alias of HessenbergDecomposition."

SkewHessenberg[mat_] := Which[
  Not @ FreeQ[Normal @ mat, _Complex, {2}], (* complex numbers *)
  Message[Skew::Hessenberg];
  SkewHouseholderComplex[mat],
  FreeQ[Normal @ mat, _Real, {2}], (* exact numbers  *)
  Message[Skew::Hessenberg];
  SkewHouseholderReal[mat],
  True,
  Module[
    {H, Q},
    {Q, H} = HessenbergDecomposition[mat];
    {H, Q, One[Length @ mat]}
  ]
] /; MatrixQ[mat, NumericQ]

(**** </Method: Hessenberg decomposition> ****)


(**** <Method: Heuristic recursion> ****)

PfaffianHeuristic::usage = "Pfaffian[mat] calculates the Pfaffian of an skew-symmetric matrix mat by using the heuristic recursive method.\nNote that this method is very slow for large matrices."

PfaffianHeuristic[mat_?SquareMatrixQ] := mat[[1, 2]] /; Length[mat] == 2

PfaffianHeuristic[mat_?SquareMatrixQ] := Total @ Times[
  Table[Power[-1, k], {k, 2, Length @ mat}],
  Rest @ First @ mat,
  Table[PfaffianHeuristic[colDelete[mat, k]], {k, 2, Length @ mat}]
]

colDelete[mat_, k_] := Delete[
  Transpose @ Delete[Transpose @ mat, {{1}, {k}}],
  {{1}, {k}}
]

(**** </Method: Heuristic recursion> ****)

End[]

EndPackage[]
