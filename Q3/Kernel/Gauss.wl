(* ::Package:: *)

BeginPackage["QuantumMob`Q3`", {"System`"}]

{ Zero, One };

{ UpperTriangular, LowerTriangular }; (* See also Diagonal[] *)
{ UpperRightMatrix, LowerLeftMatrix };
{ AntisymmetricMatrix };

{ MatrixConditionNumber };
{ CanonicalizeVector };
{ BasisComplete, BasisComplement };

{ ArrayShort, MatrixObject };

{ CommonEigensystem, CommonEigenvectors, CommonEigenvalues };

{ CSDecomposition,
  PhaseDecomposition };

{ GivensFactor, GivensRotation };
{ HouseholderMatrix };
{ TridiagonalToeplitzMatrix };

{ TensorFlatten, Tensorize };
{ ArrayPermute };

{ RandomVector, RandomMatrix,
  RandomHermitian, RandomPositive,
  RandomSymmetric, RandomAntisymmetric,
  RandomUnitary, RandomIsometric, RandomOrthogonal,
  RandomSymplectic RandomUnitarySymplectic };

{ GraphForm, ChiralGraphForm,
  Vertex, VertexLabelFunction, EdgeLabelFunction };


Begin["`Private`"]

(**** <MatrixConditionNumber> ****)

(**** <Zero> ****)

Zero::usage = "Zero[n] return an one-diemnsional array of lenth n with all elements zero.\nZero[{m, n, \[Ellipsis]}] returns an m\[Times]n\[Times]\[Ellipsis] tensor with all elements zero."

Zero[n_Integer] := Zero[{n}]

Zero[mn:{__Integer}] := SparseArray[{}, mn]

(**** </Zero> ****)


(**** <One> ****)

One::usage = "One[n] or One[{n}] returns the n\[Times]n identiy matrix in a sparse array; cf. IdentityMatrix[n].\nOne[{m, n, \[Ellipsis]}] returns the m\[Times]n\[Times]\[Ellipsis] pseudo-identity tensor, i.e., the tensor where the main diagonal elements are 1 and the other elements are all zero.\nOne[{m, n}, k] returns an m\[Times]n matrix with the elements on the \*SuperscriptBox[k,th] diagonal being 1 and zero elsewhere."

One[n_Integer] := One @ {n, n}

One[{n_Integer}] := One @ {n, n}

One[{m_Integer, n__Integer}] :=
  SparseArray[ConstantArray[j_, Length @ {m, n}] -> 1, {m, n}]


One[{n_Integer}, p_Integer] := One[{n, n}, p]

One[{m_Integer, n_Integer}, k_Integer] := 
  SparseArray[{i_, j_} :> 1 /; j == i+k, {m, n}]

(**** </One> ****)


MatrixConditionNumber::usage = "MatrixConditionNumber[mat] returns the condition number of matrix mat."

MatrixConditionNumber[mat_?MatrixQ] := Module[
  {min, max},
  {min, max} = MinMax[SingularValueList @ mat];
  max/min
]

(**** </MatrixConditionNumber> ****)


(**** <CanonicalizeVector> *****)

CanonicalizeVector::usage = "CanonicalizeVector[vec] returns a vector with elements are rescaled so that the first non-zero element is real positive with the same magnitude as vec.\nCanonicalizeVector[vec, a] returns the same vector with elements rescaled so that the first non-zero element is normalized to a. That is, it does not preserve the norm of vec."

(* BUG (v14.1, fixed in v14.2): SelectFirst gives a wrong answer for SparseArray, or evan crashes the Wolfram Kernel. *)
If[ $VersionNumber < 14.2,
  CanonicalizeVector[in_SparseArray?VectorQ, a_:Automatic] := Module[
    { val = First[in @ "NonzeroValues"] },
    If[val === {}, Return @ in];
    If[a === Automatic || a === False, 
      in * (Conjugate[val] / Abs[val]),
      in * (a / val)
    ]
  ]
]

CanonicalizeVector[in_?VectorQ, a_:Automatic] := Module[
  { val = SelectFirst[in, Not[ZeroQ @ #]&] },
  If[MissingQ @ val, Return @ in];
  If[a === Automatic || a === False, 
    (* NOTE: Here, a === False is for backward compatibility. *)
    in * (Conjugate[val] / Abs[val]),
    in * (a / val)
  ]
]

(**** </CanonicalizeVector> *****)


(**** <BasisComplete> *****)

BasisComplete::usage = "BasisComplete[{v1, v2, \[Ellipsis]}] returns a complete basis of the n-dimensional complex vector spaces that are spanned by the n-dimensional vectors v1, v2, \[Ellipsis]."

BasisComplete[vv_?MatrixQ] :=
  ConjugateTranspose[HouseholderMatrix @ vv]

(**** </BasisComplete> *****)


(**** <BasisComplement> *****)

svdBasisComplement::usage = "svdBasisComplement[{v1,v2,\[Ellipsis]}, {w1,w2,\[Ellipsis]}] returns a new basis of the subspace W\[UpTee]\[Subset]\[ScriptCapitalV] that is orgohtonal to \[ScriptCapitalW], where \[ScriptCapitalV] is the vector space spanned by the basis {v1,v2,\[Ellipsis]}, and \[ScriptCapitalW] is a subspace of \[ScriptCapitalV] spanned by the basis {w1,w2,\[Ellipsis]}."

svdBasisComplement[aa_?MatrixQ, bb_?MatrixQ] := Module[
  { aaa = SparseArray @ aa,
    mat = Orthogonalize[SparseArray @ bb],
    any, val, new },
  new = aaa - aaa . Topple[mat] . mat;
  {any, val, new} = SingularValueDecomposition[new];
  val = DeleteCases[Chop @ Diagonal @ val, 0];
  Take[Topple @ new, Length @ val]
 ] /; ArrayQ @ Join[aa, bb]
(* NOTE: This works even if aa and bb are not orthonormal. *)


BasisComplement::usage = "BasisComplement[{v1,v2,\[Ellipsis]}, {w1,w2,\[Ellipsis]}] returns a new basis of the subspace W\[UpTee]\[Subset]\[ScriptCapitalV] that is orgohtonal to \[ScriptCapitalW], where \[ScriptCapitalV] is the vector space spanned by the basis {v1,v2,\[Ellipsis]}, and \[ScriptCapitalW] is a subspace of \[ScriptCapitalV] spanned by the basis {w1,w2,\[Ellipsis]}."

Options[BasisComplement] = { Method -> "GramSchmidt" };
(* Possible options: "SVD" (singular value decomposition) as well as those of
   Orthogonalize. *)

BasisComplement[aa_?MatrixQ, bb_?MatrixQ, opts:OptionsPattern[]] := Module[
  { aaa, mat, new },
  
  If[OptionValue[Method] == "SVD", Return @ svdBasisComplement[aa, bb]];
  
  aaa = SparseArray @ aa;
  mat = Orthogonalize[SparseArray @ bb];
  
  new = aaa - aaa . Topple[mat] . mat;
  new = Orthogonalize @ Select[new, Positive[Chop @ Norm @ #]&, opts];
  (* NOTE: Theoretically, the above two lines may be combined to a single line,
       new = Orthogonalize[aaa - aaa.Topple[mat].mat];
     However, it gives a strange result when some rows of mat are contained in
     aaa. This issue is inherited from the built-in function Orthogonalize. *)
  Select[new, Positive[Chop @ Norm @ #]&]
 ] /; ArrayQ @ Join[aa, bb] 
(* NOTE: This works even if aa and bb are not orthonormal. *)

BasisComplement[aa_List, bb_List, opts:OptionsPattern[]] := Module[
  { ss = Agents @ {aa, bb},
    new },
  new = BasisComplement[
    SparseArray @ Matrix[aa, ss],
    SparseArray @ Matrix[bb, ss],
    opts ];
  ExpressionFor[#, ss]& /@ new
 ] /; NoneTrue[Join[aa, bb], FreeQ[#, _Ket]&]
(* NOTE: This works even if aa and bb are not orthonormal. *)

(**** </BasisComplement> *****)


UpperTriangular::usage = "UpperTriangular[m] gives the list of elements on the upper triangular part of the matrix m. UpperTriangular[m,n] ... See also Diagonal[] and UpperTriangularize[]."

UpperTriangular[m_?MatrixQ, n_: 0] := With[
  {nn = Range[n, Length[m]-1]},
  Flatten[ MapThread[Drop, {Drop[m, -n], nn}], 1 ]
]

LowerTriangular::usage = "LowerTriangular[m] gives the list of elements on the lower triangular part of the matrix m. LowerTriangular[m,n] ... See also Diagonal[] and LowerTriangularize[].\nLowerTriangular[m] is equivalent to Values @ Most @ ArrayRules @ LowerTriangularMatrix @ LowerTriangularize[m]."

LowerTriangular[m_?MatrixQ, n_: 0] := With[
  {nn = Range[1, Length[m]-n]},
  Flatten[ MapThread[Take, {Drop[m,n], nn}], 1 ]
]


(**** <UpperRightMatrix> ****)
(* NOTE: UpperTriangularMatrix would be a proper name, but it was taken by a built-in function. *)

UpperRightMatrix::usage = "UpperRightMatrix[vec] returns an upper triangular matrix with the non-zero elements given by the elements of list vec."

UpperRightMatrix::len = "List `` cannot fill an upper triangular matrix."

UpperRightMatrix[v_?VectorQ] := UpperRightMatrix[v, 0]

UpperRightMatrix[v_?VectorQ, k_Integer] := Module[
  { n = (2k-1 + Sqrt[1 + 8 Length[v]])/2,
   mm },
  mm = TakeList[v, Reverse @ Range[n-k]]; 
  RotateLeft[PadLeft[mm, {n, n}], k] /;
  If[IntegerQ[n], True,
    Message[UpperRightMatrix::len, v]; False
  ]
]

(**** </UpperRightMatrix> ****)


(**** <LowerLeftMatrix> ****)
(* NOTe: LowerTriangularMatrix would be a proper name, but it was taken by a built-in function. *)

LowerLeftMatrix::usage = "LowerLeftMatrix[vec] returns an lower triangular matrix with the non-zero elements given by the elements of list vec."

LowerLeftMatrix::len = "List `` cannot fill an upper triangular matrix."

LowerLeftMatrix[v_?VectorQ] := LowerLeftMatrix[v, 0]

LowerLeftMatrix[v_?VectorQ, k_Integer] := Module[
  { n = (2k-1 + Sqrt[1 + 8 Length[v]])/2,
   mm },
  mm = TakeList[v, Range[n-k]]; 
  RotateRight[PadRight[mm, {n, n}], k] /;
  If[IntegerQ[n], True,
    Message[LowerLeftMatrix::len, v]; False
  ]
]

(**** </LowerLeftMatrix> ****)


(**** <AntisymmetricMatrix> ****)

AntisymmetricMatrix::usage = "AntisymmetricMatrix[vec] returns the anti-symmetric matrix with the upper triangular elements given by the elements in list vec."

AntisymmetricMatrix[v_?VectorQ] := With[
  { mat = UpperRightMatrix[v,1] },
  mat - Transpose[mat]
]

(**** </AntisymmetricMatrix> ****)


(**** <ArrayShort> ****)

ArrayShort::usage = "ArrayShort[mat] displays matrix mat in a short form."

Options[ArrayShort] = {
  "Size" -> 4
}

ArrayShort[mat_SymmetrizedArray, rest___] := ArrayShort[Normal @ mat, rest]
(* NOTE: SymmetrizedArray does not support Span properly. *)

ArrayShort[vec_?VectorQ, opts:OptionsPattern[{ArrayShort, MatrixForm}]] := With[
  { n = OptionValue["Size"] },
  If[ Length[vec] > n,
    Append[Take[vec, n], "\[Ellipsis]"],
    Take[vec, UpTo @ n]
  ] // Normal[#, SparseArray]& // Chop // IntegerChop
]

ArrayShort[mat_?ArrayQ, opts:OptionsPattern[{ArrayShort, MatrixForm}]] := Module[
  { dim = Flatten @ { OptionValue["Size"] },
    hdr = OptionValue[TableHeadings],
    spc },
  dim = PadRight[dim, ArrayDepth @ mat, dim];
  spc = Thread @ {0, Boole @ Thread[Dimensions[mat] > dim]};
  dim = Thread[1 ;; UpTo /@ dim];
  If[hdr === Automatic, hdr = Range /@ Take[Dimensions @ mat, 2]];
  If[ Length[hdr] == 2,
    hdr = ArrayPad[
      hdr[[Sequence @@ Take[dim, 2]]],
      Take[spc, 2],
      "\[Ellipsis]"
    ]
  ];
  MatrixForm[
    ArrayPad[
      IntegerChop @ Chop @ mat[[Sequence @@ dim]],
      spc, 
      "\[Ellipsis]"
    ],
    TableHeadings -> hdr,
    FilterRules[{opts}, Options[MatrixForm]]
  ]
]

ArrayShort[any_] = any

(**** </ArrayShort> ****)


(**** <MatrixObject> ****)

MatrixObject::usage = "MatrixObject[{{m11,m12,\[Ellipsis]}, {m21,m22,\[Ellipsis]}, \[Ellipsis]}] represents a dense matrix.\nIt may be useful to display a dense matrix in a compact form."

MatrixObject /:
MakeBoxes[MatrixObject[mat_List?MatrixQ], fmt_] :=
  BoxForm`ArrangeSummaryBox[
    MatrixObject, mat, None,
    { BoxForm`SummaryItem @ { "Type: ", "Dense" },
      BoxForm`SummaryItem @ { "Dimensions: ", Dimensions[mat] }
    },
    { BoxForm`SummaryItem @ { "Elements: ", ArrayShort[mat] }
    },
    fmt,
    "Interpretable" -> Automatic
  ]

MatrixObject[{}] = {}

MatrixObject[mat_SparseArray?MatrixQ] = mat

MatrixObject[mat_SymmetrizedArray?MatrixQ] = mat

(**** </MatrixObject> ****)


(**** <CommonEigensystem> ****)
(* NOTE: Here, we use a heuristic method. More techincal and sophisticate algorithm was first provided in Cardoso (1996). *)

CommonEigensystem::usage = "CommonEigensystem[{m1, m2, ...}] finds the simultaneous eigenvectors and corresponding eigenvales of the mutually commuting square matrices."

CommonEigenvectors::usage = "CommonEigenvectors[{m1, m2, ...}] finds the simultaneous eigenvectors of the mutually commuting square matrices."

CommonEigenvalues::usage = "CommonEigenvalues[{m1, m2, ...}] finds the simultaneous eigenvalues of the mutually commuting square matrices."

CommonEigensystem[mm:{__?MatrixQ}] := Module[
  { id = One[Dimensions @ First @ mm],
    val, vec },
  {val, vec} = Transpose @ FoldPairList[blockEigensystem, {id}, mm, Identity];
  {Transpose @ val, Catenate @ Last @ vec}
]

CommonEigenvalues[mm:{__?MatrixQ}] := Module[
  { id = One[Dimensions @ First @ mm] },
  Transpose @ FoldPairList[blockEigensystem, {id}, mm]
]

CommonEigenvectors[mm:{__?MatrixQ}] := Module[
  { id = One[Dimensions @ First @ mm] },
  Catenate @ FoldPair[blockEigensystem, {id}, mm, Last]
]


blockEigensystem[bs:{__?MatrixQ}, mat_?MatrixQ] := Module[
  { sys, val, vec },
  sys = Transpose @ Map[blockEigensystem[#, mat]&, bs];
  {val, vec} = Catenate /@ sys;
  {Catenate @ val, vec}
]

blockEigensystem[bs_?MatrixQ, mat_?MatrixQ] := Module[
  { sys, val, vec },
  sys = Transpose @ Eigensystem[Conjugate[bs] . mat . Transpose[bs]];
  {val, vec} = Transpose[Transpose /@ GatherBy[sys, First]];
  vec = Map[Normalize, vec, {2}];
  vec = Map[# . bs&, vec];
  {val, vec}
]
(* The basis bs is assumed to be orthonormal. *)

(**** </CommonEigensystem> ****)


(**** <HouseholderMatrix> ****)

HouseholderMatrix::usage = "HouseholderMatrix[v] returns the Householder reflection matrix h such that v.h is proportional to {1, 0, 0, \[Ellipsis]} for a vector v.\nHouseholderMatrix[v, k] returns the Householder reflection matrix that transforms {vk, \[Ellipsis], vn} with the earlier components {v1, \[Ellipsis], v(k-1)} kept intact.\nHouseholderMatrix[m], for a rectangular matrix m, returns the Householder matrix h such that m.h is a lower triangular matrix with all diagonal elements are real positive."

HouseholderMatrix::numeric = "`` is supposed to be a numeric vector."

HouseholderMatrix::neg = "The second input argument `` must be larger than 1."

HouseholderMatrix[vec_?VectorQ] := theHouseholderMatrix[vec] /; 
  If[ VectorQ[vec, NumericQ], True,
    Message[HouseholderMatrix::numeric, ArrayShort @ vec];
    False
  ]

HouseholderMatrix[mat_?MatrixQ] := Module[
  { new, m, n },
  {m, n} = Dimensions[mat];
  new = If[m > n, Take[mat, n], mat];
  theHouseholderMatrix[new]
] /; If[ MatrixQ[mat, NumericQ], True,
    Message[HouseholderMatrix::numeric, ArrayShort @ mat];
    False
  ]

HouseholderMatrix[vec_?VectorQ, k_Integer] := With[
  { mat = HouseholderMatrix[Drop[vec, k-1]] },
  CirclePlus[One[k-1], mat]
] /; If[ k > 1, True,
    Message[HouseholderMatrix::neg, k];
    False
  ]

theHouseholderMatrix[vec_?VectorQ] :=
  {Conjugate @ vec} /; Length[vec] == 1
(* NOTE: In principle, this does not need to be handled separately. However, sometimes an additional factor of -1 is added due to numerical errors (Normalize and Dyad in the following code). *)

theHouseholderMatrix[vec_?VectorQ] := Module[
  { new = -vec,
    fac = Norm[vec],
    phs = Exp[I * Arg[First @ vec]] },
  fac *= phs;
  new[[1]] += fac;
  new = Normalize[new];
  new = One[Length @ vec] - 2*KroneckerProduct[Conjugate @ new, new];
  new * Conjugate[phs]
]

theHouseholderMatrix[vv_?MatrixQ] :=
  theHouseholderMatrix[First @ vv] /;
  Length[vv] == 1

theHouseholderMatrix[vv_?MatrixQ] := Module[
  { uu = theHouseholderMatrix[First @ vv],
    ww = Rest[vv] },
  ww = Dot[ww, uu][[All, 2;;All]];
  ww = CirclePlus[{{1}}, theHouseholderMatrix @ ww]; 
  Dot[uu, ww]
]

(**** </HouseholderMatrix> ****)


(***** <TridiagonalToeplitzMatrix> ****)

TridiagonalToeplitzMatrix::usage = "TridiagonalToeplitzMatrix[n, {a,b,c}] represents an n\[Times]n tridiagonal Toeplitz matrix with a, b, and c on the lower-diagonal, main-diagonal, and upper-diagonal, respectively. See also Noschese et al. (Numerical Linear Algebra with Applications, 2012) and Jocobi matrices.\nEigenvalues[TridiagonalToeplitzMatrix[n,{a,b,c}]] gives the eigenvalues.\nEigenvalues[TridiagonalToeplitzMatrix[n,{a,b,c}]] gives the normalized eigenvectors."

TridiagonalToeplitzMatrix /:
Matrix @ TridiagonalToeplitzMatrix[n_Integer, {a_, b_, c_}] := Plus[
  DiagonalMatrix[Table[a, n-1], -1],
  DiagonalMatrix[Table[b, n]],
  DiagonalMatrix[Table[c, n-1], +1]
 ]

TridiagonalToeplitzMatrix /:
Elaborate @ TridiagonalToeplitzMatrix[n_Integer, {a_, b_, c_}] :=
  Matrix @ TridiagonalToeplitzMatrix[n, {a, b, c}]

TridiagonalToeplitzMatrix /:
Eigenvalues @ TridiagonalToeplitzMatrix[n_Integer, {a_, b_, c_}] :=
  Table[b + 2*Sqrt[a*c] * Cos[k*Pi/(n+1)], {k, n}]

(* the right eigenvectors *)
TridiagonalToeplitzMatrix /:
Eigenvectors @ TridiagonalToeplitzMatrix[n_Integer, {a_, b_, c_}] :=
  Sqrt[2/(n+1)] * Table[Power[a/c, k/2] * Sin[i*k*Pi/(n+1)], {i, n}, {k, n}]

TridiagonalToeplitzMatrix /:
Eigensystem @ TridiagonalToeplitzMatrix[n_Integer, {a_, b_, c_}] := {
  Eigenvalues @ TridiagonalToeplitzMatrix[n, {a, b, c}],
  Eigenvectors @ TridiagonalToeplitzMatrix[n, {a, b, c}]
 }

(***** </TridiagonalToeplitzMatrix> ****)


(**** <CSDecomposition> ****)

CSDecomposition::usage = "CSDecomposition[u, p] returns the cosine-sine (CS) decomposition of unitary matrix u."
(* NOTE: We follow the convention in Horn (2013a). *)

CSDecomposition::old = "CSDecomposition is supported in Mathematica 14.2 or later.";

CSDecomposition[mat_?MatrixQ, p_Integer] := Module[
  { n = Length[mat],
    k, uu, vv, ww, aa, bb, cc, dd, qq, rr, kk },
  kk = Reverse @ One[p];
  {vv[1], aa, ww[1]} = SingularValueDecomposition[ mat[[1;;p, 1;;p]] ];
  aa = kk . aa . kk;
  vv[1] = kk . ConjugateTranspose[vv[1]];
  ww[1] = ww[1] . kk;
  bb = vv[1] . mat[[1;;p, p+1;;All]];
  cc = mat[[p+1;;All, 1;;p]] . ww[1];

  {qq, rr} = QRDecomposition[Transpose @ bb];
  ss = Sign[Diagonal @ rr];
  ss = PadRight[TrimRight @ ss, n-p, 1];
  ss = DiagonalMatrix[ss, TargetStructure -> "Sparse"];
  ww[2] = Transpose @ BasisComplete[qq] . ss;
  bb = PadRight[Transpose @ rr, Dimensions @ bb] . ss;

  {qq, rr} = QRDecomposition[cc];
  ss = -Sign[Diagonal @ rr];
  ss = PadRight[TrimRight @ ss, n-p, 1];
  ss = DiagonalMatrix[ss, TargetStructure -> "Sparse"];
  vv[2] = ss . BasisComplete[qq];
  cc = ss . PadRight[rr, Dimensions @ cc];

  dd = mat[[p+1;;All, p+1;;All]];
  dd = vv[2] . dd . ww[2];

  k = SelectFirst[1-Diagonal[aa], ZeroQ -> "Index"];
  If[MissingQ[k], k = p+1];
  qq = ConjugateTranspose[ dd[[k;;All, k;;All]] ];
  qq = CirclePlus[One[k-1], qq];
  dd = CirclePlus[dd[[1;;k-1, 1;;k-1]], One[Length[dd]-k+1]];
  ww[2] = ww[2] . qq;

  { ConjugateTranspose @ CirclePlus[vv[1], vv[2]],
    ArrayFlatten @ {
      {aa, bb},
      {cc, dd}
    },
    CirclePlus[ww[1], ww[2]]
  }
] /; If[ $VersionNumber < 14.2,
  Message[CSDecomposition::old]; False,
  True
]
(* NOTE: SelectFirst[..., test->property] used here is introduced in Mathematica v14.2. *)

(**** </CSDecomposition> ****)


(**** <PhaseDecomposition> ****)

PhaseDecomposition::usage = "PhaseDecomposition[u] gives the phase decomposition of unitary matrix u as a list {v, d, w} of special orthogonal matrices v and w and digonal matrix d."
(* SEE: Tucci (2005) *)

PhaseDecomposition[uu_?MatrixQ] := Module[
  { n = Length[uu],
    xx = Re[uu],
    yy = Im[uu],
    vv, ww, dd, ff, val, trs, r },
  If[ ArrayZeroQ[xx],
    {vv, dd, ww} = SingularValueDecomposition[yy];
    dd *= I,
    
    (* else *)
    {vv, dd, ww} = SingularValueDecomposition[xx];
    ff = Transpose[vv] . yy . ww;
  
    (* the rank of xx *)
    r = LengthWhile[Diagonal @ dd, Not[ZeroQ @ #]&];
    If[ r == n,
      {val, trs} = CommonEigensystem[{dd, ff}];
      trs = Transpose[trs];
      dd = DiagonalMatrix[Complex @@@ val, TargetStructure -> "Sparse"];
      vv = vv . trs;
      ww = ww . trs,
    
      (* else *)
      {val, trs} = CommonEigensystem[{Take[dd, r, r], Take[ff, r, r]}];
      trs = Transpose[trs];
      dd = DiagonalMatrix[Complex @@@ val, TargetStructure -> "Sparse"];
      {vv1, ff1, ww1} = SingularValueDecomposition[Take[ff, r-n, r-n]];
      dd = CirclePlus[dd, I*ff1];
      vv = vv . CirclePlus[trs, vv1];
      ww = ww . CirclePlus[trs, ww1]
    ]
  ];
  (* require that vv and ww be SO(n) *)
  If[Det[vv] < 0, vv[[All, 1]] *= -1; dd[[1, 1]] *= -1];
  If[Det[ww] < 0, ww[[All, 1]] *= -1; dd[[1, 1]] *= -1];
  {vv, dd, ww}
]
(* TODO: The current implementation uses a heuristic algorithm for CommonEigensystem. More sophisticated algorithm is needed for large matrices. *)

(**** </PhaseDecomposition> ****)


(**** <TensorFlatten> ****)

TensorFlatten::usage = "TensorFlatten[tsr] flattens out the given tensor tsr to a matrix and returns it.\nIt generalizes ArrayFlatten and operates on tensors of any rank.\nTo flatten out a tensor to a vector (rather than a matrix), just use Flatten."

TensorFlatten[t_?TensorQ] := With[
  { r = TensorRank[t] },
  Flatten[t, {Range[1,r,2], Range[2,r,2]}]
 ]

TensorFlatten[c:Except[_List]] := c

(**** </TensorFlatten> ****)


(**** <Tensorize> ****)

Tensorize::usage = "Tensorize[m] gives the tensor product form of the matrix m. The matrix m is supposed to be the matrix representation of a multi-qubit system and hence a square matrix of size 2^n, where n is the number of qubits.\nTensorize[v] gives the tensor product form of the vector v. The vector v is supposed to be the matrix representation of a multi-qubit system and hence a column vector of size 2^n.\nTensorize[m, dim] and Tensor[v, dim] are the same but for general subsystems of dimensions dim.\nNotice the difference between TensorProduct and CircleTimes. While TensorProduct preseves the tensor product form (in blocks), CircleTimes gives the matrix direct product with component blocks flattened. In fact, CircleTimes = Flatten @ TensorProdut for vectors and CircleTimes = TensorFlatten @ TensorProduct for matrices. Tensorize recovers the tensor product form from the matrix direct product form."

Tensorize::badShape = "The dimenion(s) `` of the matrix is (are) not compatible with the subdimensions ``."

Tensorize::notQubit = "The input array should be either a (2^n)\[Times](2^n) square matrix or a vector of length 2^n."

Tensorize[m_?MatrixQ, dim:{__Integer}] := Module[
  { r = Length[dim],
    oo = dim[[1;; ;;2]],
    ee = dim[[2;; ;;2]],
    ll = Dimensions[m],
    ii },
  If[ ll != {Whole @ oo, Whole @ ee},
    Message[Tensorize::badShape, ll, dim];
    Return[m]
  ];
  ii = Join[ Range[1, r, 2], Range[2, r, 2] ];
  Transpose[ ArrayReshape[m, Join[oo, ee]], ii ]
]

Tensorize[m_?MatrixQ] := Module[
  { n = Log[2, Length[m]],
    ii },
  If[ !IntegerQ[n],
    Message[Tensorize::notQubit];
    Return[m]
   ];
  ii = Join[ Range[1, 2*n, 2], Range[2, 2*n, 2] ];
  Transpose[ ArrayReshape[m, ConstantArray[2, 2*n]], ii ]
 ]

Tensorize[v_?VectorQ, dim:{__Integer}] := Module[
  { l = Length[v] },
  If[ l != Whole[dim],
    Message[Tensorize::badShape, l, dim];
    Return[v]
  ];
  ArrayReshape[v, dim]
]

Tensorize[v_?VectorQ] := Module[
  { n = Log[2, Length[v]] },
  If[ !IntegerQ[n],
    Message[Tensorize::badQubit];
    Return[v]
   ];
  ArrayReshape[v, ConstantArray[2,n]]
 ]

(**** </Tensorize> ****)


(**** <ArrayPermute> ****)

ArrayPermute::usage = "ArrayPermute[array, perm, n] permutes the elements of array by perm at level n.\nArrayPermute[array, perm, {n1, n2, \[Ellipsis]}] performs the permutation perm at levels n1, n2, \[Ellipsis].\nArrayPermute[array, perm] or ArrayPermute[array, perm, All] is equivalent to ArrayPermute[array, perm, Range[ArrayDepth @ array]].\nThe argument perm may be specified by using TwoWayRules, Cycles or a permutation list (see PermutationList)."

SyntaxInformation[ArrayPermute] = {"ArgumentsPattern" -> {_, _, _.}}

ArrayPermute[obj_?ArrayQ, spec:(_TwoWayRule|_Cycles|_?PermutationListQ)] :=
  ArrayPermute[obj, spec, Range @ ArrayDepth @ obj]

ArrayPermute[obj_?ArrayQ, spec_, All] :=
  ArrayPermute[obj, spec, Range @ ArrayDepth @ obj]

ArrayPermute[obj_, spec_, n_Integer] :=
  ArrayPermute[obj, spec, {n}]

ArrayPermute[obj_, a_Integer <-> b_Integer, rest___] :=
  ArrayPermute[obj, Cycles @ {{a, b}}, rest]

ArrayPermute[obj_, perm_?PermutationListQ, rest___] :=
  ArrayPermute[obj, PermutationCycles @ perm, rest]


ArrayPermute[obj_, ss:{(_TwoWayRule|_Cycles|_?PermutationListQ)..}] :=
  ArrayPermute[obj, Transpose @ {ss, Range @ Length @ ss}]

ArrayPermute[obj_, ss:{{(_TwoWayRule|_Cycles|_?PermutationListQ), _Integer}..}] :=
  Fold[ArrayPermute[#1, First @ #2, Last @ #2]&, obj, ss]


(* structured array: symmetry preserved *)

ArrayPermute[obj_SymmetrizedArray, cc_Cycles, nn:{__Integer}] :=
  Module[
    { dd = Most[ArrayRules @ obj] },
    dd = Thread[xchPositions[Keys @ dd, cc, nn] -> Values[dd]];
    SymmetrizedArray[dd, Dimensions @ obj, obj["Symmetry"]]
  ] /; ContainsAll[nn, First[obj @ "Symmetry"]]


(* structured array: symmetry not preserved *)

ArrayPermute[obj:(_SymmetrizedArray|_SparseArray), cc_Cycles, nn:{__Integer}] := 
  Module[
    { dd = Most[ArrayRules @ obj] },
    dd = Thread[xchPositions[Keys @ dd, cc, nn] -> Values[dd]];
    SparseArray[dd, Dimensions @ obj]
  ]


(* dense array *)

ArrayPermute[obj_List?ArrayQ, spec_, All] :=
  ArrayPermute[obj, spec, Range[ArrayDepth @ obj]]

ArrayPermute[obj_List?ArrayQ, cc_Cycles, nn:{__Integer}] :=
  Module[
    { rr = Thread[1 <-> nn] },
    Fold[Transpose[Permute[Transpose[#1, #2], cc], #2]&, obj, rr]
  ]


(* tool *)

xchPositions[pp:{{__}..}, cc_Cycles, nn:{__Integer}] := Module[
  { rr = PermutationList[cc] },
  rr = DeleteCases[Thread[Sort[rr] -> rr], Rule[i_, i_]];
  Transpose @ MapAt[ReplaceAll[rr], Transpose @ pp, List /@ nn]
]

(**** </ArrayPermute> ****)


(**** <RandomVector> ****)

RandomVector::usage = "RandomVector[n] generates an n-dimensional random normalized complex vector distributed uniformly in terms of the Haar measure.\nRandomVector[] is equivalent to RandomVector[2]."

RandomVector[] := RandomVector[2]

RandomVector[n_Integer?Positive] := Flatten[RandomIsometric @ {n, 1}]

(**** </RandomVector> ****)


(**** <RandomIsometric> ****)

(* See Mezzadri (2007) *)
RandomIsometric::usage = "RandomIsometric[{m, n}] generates an m\[Times]n random isometric matrix uniformly distributed in the terms of the Haar measure."

RandomIsometric::dim = "The first dimenion of an isometric matrix cannot be smaller than the second dimension."

RandomIsometric[n_Integer?Positive] := RandomUnitary[n]

RandomIsometric[{n_Integer?Positive, n_Integer?Positive}] := RandomUnitary[n]
(* NOTE: RandomUnitary is faster since it is based on the built-in function CircularUnitaryMatrixDistribution. *)

RandomIsometric[{m_Integer?Positive, n_Integer?Positive}] := Module[
  { mat = RandomMatrix[1, {m, n}],
    qq, rr },
  {qq, rr} = QRDecomposition[mat];
  rr = DiagonalMatrix[Sign @ Diagonal @ rr]; (* NOTE: Sign[z] = z / Abs[z] for complex z. *)
  Topple[qq] . rr
] /; If[TrueQ[m > n], True, Message[RandomIsometric::dim]; False]
(* NOTE: For m ~ n, RandomUnitary[m][[;;, ;;n]] is faster since RandomUnitary is based on the built-in function CircularUnitaryMatrixDistribution. *)

(**** </RandomIsometric> ****)


(**** <RandomMatrix> ****)

RandomMatrix::usage = "RandomMatrix[\[Sigma], {m, n}] returns an m\[Times]n random complex matrix with independent identically distributed real and imaginary matrix elements that follow NormalDistribution[0,\[Sigma]].\nRandomMatrix[\[Sigma], n] is equivalent to RandomMatrix[\[Sigma], {n, n}].\nRandomMatrix[nspec] is equivalent to RandomMatrix[1, nspec].\nRandomMatrix[] is equivalent to RandomMatrix[1, {2, 2}]."

RandomMatrix[] := RandomMatrix[1, {2, 2}]

RandomMatrix[mn_] := RandomMatrix[1, mn]

RandomMatrix[sgm_?Positive, n_Integer?Positive] := RandomMatrix[sgm, {n, n}]

RandomMatrix[sgm_?Positive, {m_Integer?Positive, n_Integer?Positive}] := 
  Table[
    Complex[
      RandomReal @ NormalDistribution[0, sgm],
      RandomReal @ NormalDistribution[0, sgm]
    ],
    m, n
  ]


RandomSymplectic::usage = "RandomSymplectic[\[Sigma], n] returns an 2n\[Times]2n randomly generated complex symplectic matrix (m+Dagger[m] - J.Transpose[m+Dagger[m]].J)/4, where m is a square matrix with independent identically distributed real and imaginary matrix elements that follow NormalDistribution[0,\[Sigma]], and where J is the skew-symmetric matrix KroneckerProduct[{{0,-1},{1,0}}, IdentityMatrix[n]].\nRandomSymplectic[] is equivalent to RandomSymplectic[1].\nRandomSymplectic[n] is equivalent to RandomSymplectic[1, n]."

RandomSymplectic[] := RandomSymplectic[1, 1]

RandomSymplectic[n_Integer?Positive] := RandomSymplectic[1, n]

RandomSymplectic[sgm_?Positive, n_Integer?Positive] := 
  RandomVariate @ GaussianSymplecticMatrixDistribution[sgm, n]


RandomSymmetric::usage = "RandomSymmetric[\[Sigma], n] returns an n\[Times]n randomly generated real symmetric matrix (m+Transpose[m])/2, where m is a square matrix with independent identically distributed matrix elements that follow NormalDistribution[0,\[Sigma]].\nRandomSymmetric[] is equivalent to RandomSymmetric[3].\nRandomSymmetric[n] is equivalent to RandomSymmetric[1, n]."

RandomSymmetric[] := RandomSymmetric[1, 3]

RandomSymmetric[n_Integer?Positive] := RandomSymmetric[1, n]

RandomSymmetric[sgm_?Positive, n_Integer?Positive] := 
  RandomVariate @ GaussianOrthogonalMatrixDistribution[sgm, n]


RandomAntisymmetric::usage = "RandomAntisymmetric[\[Sigma], n] returns an n\[Times]n random anti-symmetric matrix (m-Transpose[m])/2, where m is a complex square matrix with independent identically distributed real and imaginary matrix elements that follow NormalDistribution[0, \[Sigma]].\nRandomAntisymmetric[n] is equivalent to RandomAntisymmetric[1, n].\nRandomAntisymmetric[] is equivalent to RandomAntisymmetric[1, 2]."

RandomAntisymmetric[] := RandomAntisymmetric[1, 2]

RandomAntisymmetric[n_Integer?Positive] := RandomAntisymmetric[1, n]

RandomAntisymmetric[sgm_?Positive, n_Integer?Positive] := With[
  { mat = RandomMatrix[sgm, n] },
  ReplacePart[
    (mat - Transpose[mat])/2,
    {i_, i_} -> 0
  ]
]


RandomHermitian::usage = "RandomHermitian[\[Sigma], n] returns an n\[Times]n random Hermitian matrix (m+Dagger[m])/2, where m is a complex square matrix with independent identically distributed real and imaginary matrix elements that follow NormalDistribution[0,\[Sigma]].\nRandomHermitian[n] is equivalent to RandomHermitian[1, n].\nRandomHermitian[] is equivalent to RandomHermitian[1, 2]."

RandomHermitian[] := RandomHermitian[1, 2]

RandomHermitian[n_Integer?Positive] := RandomHermitian[1, n]

RandomHermitian[sgm_?Positive, n_Integer?Positive] := 
  RandomVariate @ GaussianUnitaryMatrixDistribution[sgm, n]


RandomPositive::usage = "RandomPositive[\[Sigma], n] returns an n\[Times]n random positive matrix Dagger[m]m, where m is a complex square matrix with independent identically distributed real and imaginary matrix elements that follow NormalDistribution[0, \[Sigma]].\nRandomPositive[n] is equivalent to RandomPositive[1, n].\nRandomPositive[] is equivalent to RandomPositive[1, 2]."

RandomPositive[] := RandomPositive[1, 2]

RandomPositive[n_Integer?Positive] := RandomPositive[1, n]

RandomPositive[sgm_?Positive, n_Integer?Positive] := With[
  { mat = RandomMatrix[sgm, n] },
  Topple[mat] . mat
]


(* See Mezzadri (2007) *)
RandomUnitary::usage = "RandomUnitary[n] generates an n\[Times]n uniformly distributed random unitary matrix in the terms of the Haar measure."

RandomUnitary[] := RandomUnitary[2]

RandomUnitary[n_Integer?Positive] := 
RandomVariate[CircularUnitaryMatrixDistribution @ n]


(* See Mezzadri (2007) *)
RandomOrthogonal::usage = "RandomOrthogonal[n] generates an n\[Times]n random real orthogonal matrix uniformly distributed in terms of the Haar measure."

RandomOrthogonal[] := RandomOrthogonal[3]

RandomOrthogonal[n_Integer?Positive] :=
  RandomVariate[CircularRealMatrixDistribution @ n]


RandomUnitarySymplectic::usage = "RandomUnitarySymplectic[n] returns a 2n\[Times]2n random unitary symplectic matrix uniformly distributed in terms of the Haar measure on the unitary symplectic group USp(2n)."

RandomUnitarySymplectic[] := RandomUnitarySymplectic[1]

RandomUnitarySymplectic[n_Integer?Positive] :=
  RandomVariate[CircularQuaternionMatrixDistribution @ n]

(**** </RandomMatrix> ****)


(**** <GraphForm> ****)

Vertex::usage = "Vertex[a, b, ...] represents an interaction vertex.\nNot to be confused with Vertices in Graph or related functions."


VertexLabelFunction::usage = "VertexLabelFunction is an option for GraphForm and ChiralGraphForm that specifies the function to generate primities for redering each vertex label.\nSee also VertexLabels."


EdgeLabelFunction::usage = "EdgeLabelFunction is an option for GraphForm and ChiralGraphForm that speicifes the function to generate primities for redering each edge label.\nSee also EdgeLabels."

defaultEdgeLabelFunction[lbl_] :=
  Framed[lbl, FrameStyle -> None, Background -> LightDarkSwitched @ White]

defaultEdgeLabelFunction[Placed[lbl_, rest__]] := 
  Placed[defaultEdgeLabelFunction @ lbl, rest]


makeEdgeLabel[func_][ Rule[edge_, $] ] := Nothing

makeEdgeLabel[func_][ Rule[edge_, lbl_] ] := Rule[edge, func @ lbl] 

makeEdgeLabel[func_][ RuleDelayed[edge_, cnd_Condition] ] := With[
  { lbl = First @ cnd,
    tst = Last @ cnd },
  RuleDelayed @@ List[edge, Condition[func @ lbl, tst]]
]
(* NOTE: This includes dirty tricks to overcome the restrictions put by
   the HoldRest attribute of RuleDelayed. *)

makeEdgeLabel[func_][ RuleDelayed[edge_, lbl_] ] :=
  RuleDelayed[edge, func @ lbl]


GraphForm::usage = "GraphForm[A] converts the matrix A to a graph revealing the connectivity, assuming that the matrix is a linear map on one vector space.\nGraphForm allows the same options as Graph, but their specifications may be slightly different.\nGraphForm is a variation of the built-in function GraphPlot.\nGraphForm[expr] returns a graph visualizing the connectivity of different particles in the expression.\nGraphForm allows all options of Graph.\nSee also ChiralGraphForm, GraphPlot, AdjacencyGraph, IncidenceGraph."

Options[GraphForm] = {
  "HideSelfLinks" -> True,
  VertexLabels -> Automatic,
  VertexLabelFunction -> Automatic,
  EdgeLabels -> Automatic,
  EdgeLabelFunction -> Automatic
}

GraphForm[A_SparseArray?MatrixQ, opts___?OptionQ] := Module[
  { data = Most @ ArrayRules[A] },
  data = KeySort @ Association @ Flatten[ survey /@ data ];
  Return @ fBuildGraph[data, opts];
]

GraphForm[A_?MatrixQ, opts___?OptionQ] := Module[
  { data = Flatten @ MapIndexed[survey, A, {2}],
    jj = Range @ Max @ Dimensions @ A },
  data = Join[Thread[jj -> jj], data];
  data = KeySort @ Association @ data;
  fBuildGraph[data, opts]
]

GraphForm[expr_, opts___?OptionQ] := Module[
  { raw, val, data },
  raw = Flatten @ Cases[expr, _Multiply, Infinity];
  val = Coefficient[expr, raw];

  data = KeySort @ Association @ Flatten[ survey /@ Thread[raw -> val] ];
  
  fBuildGraph[ data, opts,
    EdgeStyle -> {
      UndirectedEdge[_, _, "Pairing"] -> 
        Directive[LightDarkSwitched @ Red, Thick],
      UndirectedEdge[_, _, "Interaction"] -> Dashed
    }
  ]
]

fBuildGraph[data_Association, opts___?OptionQ] := Module[
  { nodes, edges, jj, ee, fVertexLabel, fEdgeLabel, v },

  edges = Normal @ KeySelect[ data, MatchQ[#, _UndirectedEdge]& ];
  nodes = Normal @ KeyDrop[ data, Keys @ edges ];

  If[ "HideSelfLinks" /. {opts} /. Options[GraphForm],
    edges = DeleteCases[edges, UndirectedEdge[v_, v_] -> _]
  ];

  jj = Keys @ nodes;
  ee = Keys @ edges;

  nodes = { VertexLabels -> nodes };
  edges = { EdgeLabels -> edges };

  fVertexLabel = VertexLabelFunction /. {opts} /. Options[GraphForm] /.
    { Automatic -> Identity };
  fEdgeLabel = EdgeLabelFunction /. {opts} /. Options[GraphForm] /.
    { Automatic -> defaultEdgeLabelFunction };
  fEdgeLabel = makeEdgeLabel[fEdgeLabel];
  
  Graph[ jj, ee,
    VertexCoordinates -> vertexRulesShort[ jj,
      VertexCoordinates /. {opts} /. Options[GraphForm] /. Options[Graph]
    ],
    VertexLabels -> fVertexLabel /@ vertexRules[ jj,
      VertexLabels /. {opts} /. nodes /. Options[GraphForm] /. Options[Graph]
    ],
    VertexStyle -> vertexRules[ jj,
      VertexStyle /. {opts} /. Options[GraphForm] /. Options[Graph]
    ],
    VertexSize -> vertexRules[ jj,
      VertexSize /. {opts} /. Options[GraphForm] /. Options[Graph]
    ],
    EdgeLabels -> fEdgeLabel /@ ReplaceAll[
      EdgeLabels, Join[{opts}, edges, Options @ GraphForm, Options @ Graph]
    ],
    Sequence @@ FilterRules[{opts}, Options[Graph]],
    ImageSize -> Large
  ]
]

survey::usage = "Surveys the matrix and constructs Vertices, Edges and relevant options for the graph corresponding to the matrix."

survey[0, {_Integer, _Integer}] := Nothing

survey[_, {j_Integer, j_Integer}] := Nothing

survey[val_, {i_Integer, j_Integer}] := {
  Sort @ UndirectedEdge[i, j] -> val
}

survey[{i_Integer, j_Integer} -> val_] := {
  i -> i,
  j -> j,
  Sort @ UndirectedEdge[i, j] -> val
}


HoldPattern @ survey[ Multiply[Dagger[a_], Dagger[b_]] -> val_ ] := {
  a -> a,
  b -> b,
  UndirectedEdge[Sequence @@ Sort[{a, b}], "Pairing"] -> val
}

HoldPattern @ survey[ Multiply[a_?SpeciesQ, b_?SpeciesQ] -> val_ ] := {
  a -> a,
  b -> b,
  UndirectedEdge[Sequence @@ Sort[{a, b}], "Pairing"] -> val
}

HoldPattern @ survey[ Multiply[Dagger[a_], b_?SpeciesQ] -> val_ ] := {
  a -> a,
  b -> b,
  UndirectedEdge @@ Sort[{a, b}] -> val
}

HoldPattern @ survey[ Multiply[a_, b_, cc__] -> val_ ] := Module[
  { nodes = Sort[Peel @ {a, b, cc}],
    edges, vtx },
  vtx = Vertex @@ nodes;
  edges = Thread @ UndirectedEdge[vtx, nodes, "Interaction"];
  Join[ {vtx -> val}, Thread[edges -> $] ]
]


vertexRules::usage = "vertexRules[jj, spec] constructs a list of Rule[]s, the form appropriate for the optioncs of Graph. It uses the specificiation cyclically if it is shorter than the index list jj."

vertexRules[ jj_, spec:(None|All|Automatic|"Indexed"|"Name") ] := spec

vertexRules[ jj_, spec:{__Rule} ] := spec

vertexRules[ jj_, spec_List ] :=
  Thread[ jj -> PadRight[spec, Length @ jj, spec] ]

vertexRules[ jj_, spec_ ] := Thread[ jj -> spec ]


vertexRulesShort::usage = "vertexRules[a] constructs a list of Rule[]s, the form appropriate for the optioncs of Graph."

vertexRulesShort[ jj_, spec:(None|All|Automatic|"Indexed"|"Name") ] := spec

vertexRulesShort[ jj_, spec:{__Rule} ] := spec

vertexRulesShort[ jj_, spec_List ] := With[
  { n = Min @ {Length @ jj, Length @ spec} },
  Thread[ Take[jj, n] -> Take[spec, n] ]
 ]

vertexRulesShort[ jj_, spec_ ] := { First[jj] -> spec }


ChiralGraphForm::usage = "ChiralGraphForm[M] converts the matrix M to a graph exhibiting its connectivity. Here it is assumed that the matrix M maps one vector space (say, B) to a different space (say, A), M: B\[RightArrow]A. Such a matrix typically appears in the off-diagonal block of chiral-symmetric matrices in the chiral basis.\nChiralGraphForm allows the same options as Graph, but their specifications may be slightly different.\nChiralGraphForm is a variation of GraphPlot.\nSee also GraphForm, GraphPlot."

Options[ChiralGraphForm] = {
  VertexLabels -> Automatic
 }

ChiralGraphForm[A_SparseArray?MatrixQ, opts___?OptionQ] := Module[
  { data = Most @ ArrayRules[A],
    ii, jj },
  data = Union /@ Merge[ chiralSurvey /@ data, Flatten ];
  ii = Cases[data["nodes"], _Integer];
  jj = Cases[data["nodes"], _Primed];
  fChiralBuildGraph[ ii, jj, data["edges"], opts,
    Sequence @@ Normal @ KeyDrop[data, {"nodes", "edges"}],
    VertexStyle -> {Blue, Red}
   ]
 ]

ChiralGraphForm[A_?MatrixQ, opts___?OptionQ] := Module[
  { data = Flatten @ MapIndexed[chiralSurvey, A, {2}],
    m, n, ii, jj },
  { m, n } = Dimensions[A];
  ii = Range[m];
  jj = Primed @ Range[n];
  data = Join[ data,
    { VertexLabels -> Join[Thread[ii -> ii], Thread[jj -> jj] ] }
   ];
  data = Union /@ Merge[data, Flatten];
  fChiralBuildGraph[ ii, jj, data["edges"], opts,
    Sequence @@ Normal @ KeyDrop[data, {"nodes", "edges"}],
    VertexStyle -> {Blue, Red}
   ]
 ]

fChiralBuildGraph[
  ii:{__Integer},
  jj:{__Primed},
  ee:{(_UndirectedEdge|_TwoWayRule|_DirectedEdge|_Rule)..},
  opts___?OptionQ
 ] := Module[
   { fVertexLabel, fEdgeLabel },
   
   fVertexLabel = VertexLabelFunction /. {opts} /. Options[GraphForm] /.
     { Automatic -> Identity };
   fEdgeLabel = EdgeLabelFunction /. {opts} /. Options[GraphForm] /.
     { Automatic -> defaultEdgeLabelFunction };
   fEdgeLabel = makeEdgeLabel[fEdgeLabel];
   
   Graph[ Join[ii, jj], ee,
     VertexCoordinates -> chiralVertexRulesShort[ ii, jj,
       VertexCoordinates /. {opts} /.
         Options[ChiralGraphForm] /. Options[Graph]
      ],
     VertexLabels -> fVertexLabel /@ chiralVertexRules[ ii, jj,
       VertexLabels /. {opts} /. Options[ChiralGraphForm] /. Options[Graph]
      ],
     VertexStyle -> chiralVertexRules[ ii, jj,
       VertexStyle /. {opts} /. Options[ChiralGraphForm] /. Options[Graph]
      ],
     VertexSize -> chiralVertexRules[ ii, jj,
       VertexSize /. {opts} /. Options[ChiralGraphForm] /. Options[Graph]
      ],
     EdgeLabels -> fEdgeLabel /@ ReplaceAll[
       EdgeLabels, Join[{opts}, Options @ GraphForm, Options @ Graph]
      ],
     Sequence @@ FilterRules[{opts}, Options[Graph]],
     ImageSize -> Large
    ]
  ]


chiralSurvey::usage = "..."

chiralSurvey[0, {i_, j_}] := Nothing

chiralSurvey[val_, {i_, j_}] := With[
  { edge = UndirectedEdge[i, Primed[j]] },
  { "nodes" -> {i, Primed[j]},
    "edges" -> {edge},
    VertexLabels -> { i -> i, Primed[j] -> Primed[j] },
    EdgeLabels -> { edge -> val }
   }
 ]

chiralSurvey[{i_Integer, j_Integer} -> val_] := chiralSurvey[val, {i, j}]

chiralVertexRules::usage = "..."

chiralVertexRules[ii_List, jj_List, spec:Except[_List]] := spec

chiralVertexRules[ii_List, jj_List, spec:{__Rule}] := spec

chiralVertexRules[ii_List, jj_List, spec:{row_, col_}] :=
  Join[ vertexRules[ii, row], vertexRules[jj, col] ]

chiralVertexRulesShort::usage = "..."

chiralVertexRulesShort[ii_List, jj_List, spec:Except[_List]] := spec

chiralVertexRulesShort[ii_List, jj_List, spec:{__Rule}] := spec

chiralVertexRulesShort[ii_List, jj_List, spec:{row_, col_}] :=
  Join[ vertexRulesShort[ii, row], vertexRulesShort[jj, col] ]

(**** </GraphForm> ****)


End[]


EndPackage[]
