(* -*- mode:math -*- *)
BeginPackage["QuantumMob`Q3`", {"System`"}]

(**** <obsolete> ****)
{ GateFactor }; (* 2025-10-10 v4.2.13  *)
{ YoungShapePile, GelfandYoungPile, SchurLabelPile };  (* 2025-06-10 v4.2.5 *)
{ BratteliDiagram, KostkaMatrix }; (* 2025-06-09 v4.2.4 *)
{ GD, GIntegrate }; (* 2025-05-31 v4.2.2 *)
{ AdjacentTranspositions }; (* rename 2025-05-27 v4.2.1 *)
{ GelfandAttach }; (* rename 2025-05-23 v4.1.11 *)
{ ToYoungTableau, ToGelfandPattern }; (* obsolete v4.1.11 2025-05-22 *)
{ GroupRegularRepresentation }; (* obsolete 2025-05-09 *)
{ PileYoungShape }; (* renamed 2025-04-13 v4.1.7 *)
{ ConditionNumber }; (* renamed 2025-04-02 v4.1.5 *)
{ AmplitudeEmbeddingGate,
  BasisEmbeddingGate }; (* renamed 2025-03-19 v4.1.4 *)
{ Affect }; (* obsolete 2025-03-12 *)
{ QuantumCircuitTrim }; (* renamed 2025-03-12 *)
{ GottesmanInner }; (* renamed *)
{ WickRandomCircuit }; (* renamed *)
{ NoisyWickSimulate }; (* renamed *)
{ WeightedLog }; (* renamed *)
{ FlavorNone, FlavorNoneQ }; (* renamed *)
{ TimesDaggerLeft, TimesLeftRight }; (* renamed *)
{ TheLower, TheRaise, RaiseLower }; (* renamed *)
{ TheState, TheOperator }; (* obsolete and excised *)
{ NormalForm }; (* renamed *)
{ LogicalForm, DefaultForm }; (* obsolete since 2023-02-18 *)
{ DyadExpression }; (* renamed *)
{ WignerFunction }; (* obsolete *)

{ FockMatrix, FockMatrixForm }; (* obsolete *)
{ FockFourier, FockInverseFourier }; (* Obsolete *)

{ TwoLevelU, GrayTwoLevelU, TwoLevelDecomposition }; (* renamed *)
{ FromTwoLevelU }; (* obsolete *)
{ GrayControlledW }; (* obsolete *)

{ CountWeylTableaux }; (* renamed *)
{ CountYoungTableaux }; (* renamed *)
{ YoungDominatesQ }; (* renamed *)

{ LindbladSolveNaive}; (* legacy *)
{ KrausProduct }; (* obsolete *)
{ LindbladGenerator }; (* renamed *)
{ LindbladBasis, LindbladBasisMatrix }; (* renamed *)

{ VerifyOracle }; (* excised *)
{ ControlledU }; (* renamed *)
{ QuissoAdd, QuissoAddZ }; (* renamed *)

(**** </obsolete> ****)


Begin["`Private`"]

(**** <FALLBACK> ****)

MultiplyPower[a_?CommutativeQ, b_?CommutativeQ] := Power[a, b]

MultiplyExp[z_?CommutativeQ] := Power[E, z]

MultiplyExp /:
Elaborate[ HoldPattern @ MultiplyExp[expr_] ] := MultiplyExp[expr]

(**** </FALLBACK> ****)


(**** <EXPERIMENTAL> ****)

HoldPattern @ Multiply[ pre___,
  Ket[a_Association], Bra[b_Association], post___] :=
  Multiply[pre, Dyad[a, b], post]
(* NOTE: This must come at the final stage and is moved to here.
   Otherwise, for example, Dagger[a[1]] ** Ket[] ** Bra[] ** a[1]
   results in Dagger[a[1]] ** Dyad[<||>,<|a[1]->1|>]. *)

(**** </EXPERIMENTAL> ****)


(**** <deprecated> *****)

(* 2025-08-31 *)
(* Mathematica 14.3 has added multiple functions to represent noncommutative algebras and perform operations on polynomials in such algebras: https://www.wolfram.com/mathematica/quick-revision-history/ *)
If[ $VersionNumber < 14.3,
  Commutator[a_, b_, n_Integer] := (
    Message[Q3General::deprecated];
    LiePower[a, b, n]
  );
  Anticommutator[a_, b_, n_Integer] := (
    Message[Q3General::deprecated];
    Fold[Anticommutator, b, ConstantArray[a, n]]    
  );
];

(* 2025-08-24 *)

Q3General::expand = "Expand[`1`[\[Ellipsis]]] and ExpandAll[`1`[\[Ellipsis]]] are deprecated; use Unfold[`1`[\[Ellipsis]]] and UnfoldAll[`1`[\[Ellipsis]]], respectively."

Scan[
  ( # /: Expand[HoldPattern[#[any__]], rest___] := (
      Message[Q3General::expand, #];
      Unfold[#[any], rest]
    );
    # /: ExpandAll[HoldPattern[#[any__]], rest___] := (
      Message[Q3General::expand, #];
      UnfoldAll[#[any], rest]
    );
  )&,
  { GivensRotation, ProductState, AmplitudeEncoding, BlockEncoding, QuantumCircuit, EulerRotation, SWAP, iSWAP, ControlledGate, UniformlyControlledRotation, UniformlyControlledGate, QFT, QBR, QCR, Projector, UnitaryInteraction }
]

(* 2025-05-08 *)
WickMeasurement::deprecated = "This form is now deprecated; use WickMeasurement[k, n] or WickMeasurment[{k1,k2,\[Ellipsis]}, n]."

(* 2025-05-08 *)
(* non-canonical form for backward compatibility *)
FermionCount[WickMeasurement[k_Integer, ___?OptionQ]] = k

(* 2025-05-08 *)
(* non-canonical form for backward compatibility *)
FermionCount[WickMeasurement[kk:{__Integer}, ___?OptionQ]] := Max[kk]

(* 2025-05-08 *)
(* non-canonical form for backward compatibility *)
WickMeasurement[k_Integer][in:WickState[{fac_?NumericQ, cvr_?MatrixQ}, rest___]] := Module[
  {aa, bb, new},
  Message[WickMeasurement::deprecated];
  {aa, bb} = WickMeasurementKernel[k, Length[cvr]/2];
  new = theWickMeasurement[{aa, bb}, cvr];
  $MeasurementOut[k] = $MeasurementOut[0];
  KeyDrop[$MeasurementOut, 0];
  WickState[{1, new}, rest]
]

(* 2025-05-08 *)
(* non-canonical form for backward compatibility *)
WickMeasurement[kk:{__Integer}][in:WickState[{fac_?NumericQ, cvr_?MatrixQ}, rest___]] := (
  Message[WickMeasurement::deprecated];
  Fold[#2[#1]&, in, WickMeasurement /@ kk]
)

(**** </deprecated> *****)


(**** <changed> ****)

TheKet[a_Integer, bc__Integer] := (
  Message[Q3General::changed, "TheKet",
    "The directions must be given in a list like TheKet[{k1,k2,...}]"];
  TheKet @ {a, bc}
)

ThePauli[a_Integer, bc__Integer] := (
  Message[Q3General::changed, "ThePauli",
    "The directions must be given in a list like ThePauli[{k1,k2,...}]"];
  ThePauli @ {a, bc}
 )

Ket[a_Integer, bc__Integer] := (
  Message[Q3General::changed, "Ket",
    "The values must be given in a list like Ket[{b1,b2,...}]"];
  Ket @ {a, bc}
 )

Bra[a_Integer, bc__Integer] := (
  Message[Q3General::changed, "Bra",
    "The values must be given in a list like Bra[{b1,b2,...}]"];
  Bra @ {a, bc}
)

Pauli[a_Integer, bc__Integer] := (
  Message[Q3General::changed, "Pauli",
    "The directions must be given in a list like Pauli[{k1,k2,...}]"];
  Pauli @ {a, bc}
)

Rotation[phi_, S:(_?QubitQ|_?SpinQ), v:{_, _, _}, opts___?OptionQ] := (
  Message[Q3General::changed, Rotation,
    "The vector must come before species specification."];
  Rotation[phi, v, S, opts]
)

Zero[m_Integer, n__Integer] := (
  Message[Q3General::changed, Zero, "Use the form Zero[{n1, n2, \[Ellipsis]}]."];
  Zero[{m, n}]
)

One[] := (
  Message[Q3General::changed, One, "Use One[2] or One[{2, 2}]."];
  One @ {2, 2}
)

One[m_Integer, n__Integer] := (
  Message[Q3General::changed, One, "Use the form One[{n1, n2, \[Ellipsis]}]."];
  One @ {m, n}
)

KetPermute[expr_, qq:{__?SpeciesQ}, spec_] := (
  Message[Q3General::changed, KetPermute, "The list of species must come last."];
  KetPermute[expr, spec, qq]
)

FermionBasis[c_?FermionQ, cc__?FermionQ, rest___] := (
  Message[Q3General::changed, FermionBasis, "Fermions need to be wrapped in a list."];
  FermionBasis[{c, cc}, rest]
)

BosonBasis[c_?BosonQ, cc__?BosonQ, rest___] := (
  Message[Q3General::changed, BosonBasis, "Bosons need to be wrapped in a list."];
  BosonBasis[{c, cc}, rest]
)

Rotation[S:(_?QubitQ|_?SpinQ), ang_, rest___] := (
  Message[Q3General::angle, Rotation];
  Rotation[ang, S, rest]
)

Rotation[qq:{(_?QubitQ|_?SpinQ)..}, ang_, rest___] := (
  Message[Q3General::angle, Rotation];
  Rotation[ang, qq, rest]
)

EulerRotation[S:(_?SpinQ|_?QubitQ), ang_, rest___] := (
  Message[Q3General::angle, EulerRotation];
  EulerRotation[ang, S, rest]
)

EulerRotation[ss:{(_?SpinQ|_?QubitQ)..}, ang_, rest___] := (
  Message[Q3General::angle, EulerRotation];
  EulerRotation[ang, ss, rest]
)

Phase[q_?QubitQ, phi_, rest___] := (
  Message[Q3General::angle, Phase];
  Phase[phi, q, rest]
)

Phase[qq:{__?QubitQ}, phi_, rest___] := (
  Message[Q3General::angle, Phase];
  Phase[phi, qq, rest]
)

(**** </changed> ****)


(**** <ToYoungTableau> ****)
(* obsolete since 2025-05-22 v4.1.11 *)

ToYoungTableau::usage = "OBSOLETE. Use YoungTableau instead.\nToYoungTableau[gz] converts Gelfand pattern gz to the corresponding Weyl tableau (semi-standard Young tableau)."
(* See Krovi119a. *)

ToYoungTableau::notgp = "Data `` is not a valid Gelfand pattern."

ToYoungTableau[gp_GelfandPattern] := (
  Message[Q3General::obsolete, "ToYoungTableau", "YoungTableau"];
  YoungTableau[gp]
)

ToYoungTableau[gp:{{___Integer}..}] := Module[
  { n = Length @ gp,
    dd },
  Message[Q3General::obsolete, "ToYoungTableau", "YoungTableau"];
  dd = Differences /@ Transpose @ Reverse @ PadRight[gp, {n+1, n}];
  YoungTableau @ YoungTrim[ 
    Flatten /@ Table[Table[k, dd[[j, k]]], {j, n}, {k, n}] 
  ]
]

ToYoungTableau[gp_] := (
  Message[Q3General::obsolete, "ToYoungTableau", "YoungTableau"];
  Message[ToYoungTableau::notgp, gp];
  gp
)

(**** </ToYoungTableau> ****)


(**** <ToGelfandPattern> ****)
(* obsolete since 2025-05-22 v4.1.11 *)

ToGelfandPattern::usage = "OBSOLETE. Use GelfandPattern instead.\nToGelfandPattern[tbl, d] converts a semi-standard Young tableau tbl to the corresponding Gelfand pattern of d letters.\nToGelfandPattern[d] represents an operation form."

ToGelfandPattern::notwt = "`` is not a valid Weyl tableau."

ToGelfandPattern[tb_?WeylTableauQ] := (
  CheckArguments[ToGelfandPattern[tb], 2];
  ToGelfandPattern[tb, Max @ tb]
)


ToGelfandPattern[d_Integer][any_] := ToGelfandPattern[any, d]

ToGelfandPattern[{}, 1] := { {0} }

ToGelfandPattern[tb_?WeylTableauQ, 1] := { Length /@ tb }

ToGelfandPattern[tb_List?WeylTableauQ, d_Integer] := (
  Message[Q3General::obsolete, "ToGelfandPattern", "GelfandPattern"];
  Prepend[
    ToGelfandPattern[YoungTrim @ DeleteCases[tb, d, {2}], d-1],
    PadRight[Length /@ tb, d]
  ]  
)

ToGelfandPattern[tb_YoungTableau, d_Integer] := (
  Message[Q3General::obsolete, "ToGelfandPattern", "GelfandPattern"];
  GelfandPattern @ ToGelfandPattern[First @ tb, d]  
)

ToGelfandPattern[tb_, _Integer] := (
  Message[ToGelfandPattern::notwt, tb];
  { {0} }
)

(**** </ToGelfandPattern> ****)


(**** <obsolete> ****)

GateFactor::usage = "GateFactor is obsolte since v4.2.13 (2025-10-10); Use Unfold or UnfoldAll instead."

GateFactor[expr_] = expr
GateFactor[any___] := (
  Message[Q3General::obsolete, "GateFactor", "Unfold"];
  Unfold[any]
)

GelfandYoungPile::usage = "GelfandYoungPile is obsolete since v4.2.5 (2025-06-10); use YoungPileUp instead."

GelfandYoungPile[any___] := (
  Message[Q3General::obsolete, "GelfandYoungPile", "YoungPileUp"];
  YoungPileUp[any]
)

YoungShapePile::usage = "YoungShapePile is obsolete since v4.2.5 (2025-06-10); use YoungPileUp instead."

YoungShapePile[any___] := (
  Message[Q3General::obsolete, "YoungShapePile", "YoungPileUp"];
  YoungPileUp[any]
)

SchurLabelPile::usage = "SchurLabelPile has been renamed SchurPileUp since v4.2.4 (2025-06-09)."

SchurLabelPile[any___] := (
  Message[Q3General::renamed, "SchurLabelPile", "SchurPileUp"];
  SchurPileUp[any]
)

BratteliDiagram::usage = "BratteliDiagram has been renamed YoungBratteliDiagram since v4.2.4 (2025-06-09)."

BratteliDiagram[any___] := (
  Message[Q3General::renamed, "BratteliDiagram", "YoungBratteliDiagram"];
  YoungBratteliDiagram[any]
)

KostkaMatrix::usage = "KostkaMatrix has been renamed KostkaNumber since v4.2.4 (2025-06-09)."

KostkaMatrix[any___] := (
  Message[Q3General::renamed, "KostkaMatrix", "KostkaNumber"];
  KostkaNumber[any]
)

GD::usage = "GD has been renamed GrassmannD since v4.2.2 (2025-05-31)."

GD[any___] := (
  Message[Q3General::renamed, "GD", "GrassmannD"];
  GrassmannD[any]
)

GIntegrate::usage = "GIntegrate has been renamed GrassmannIntegrate since v4.2.2 (2025-05-31)."

GIntegrate[any___] := (
  Message[Q3General::renamed, "GIntegrate", "GrassmannIntegrate"];
  GrassmannIntegrate[any]
)

AdjacentTranspositions::usage = "AdjacentTranspositions has been renamed PermutationTranspositions since v4.2.1 (2025-05-27)."

AdjacentTranspositions[any___] := (
  Message[Q3General::renamed, "AdjacentTranspositions", "PermutationTranspositions"];
  PermutationTranspositions[any]
)

GelfandAttach::usage = "GelfandAttach has been renamed GelfandYoungPile since v4.1.10 (2025-05-23)."

GelfandAttach[any___] := (
  Message[Q3General::renamed, "GelfandAttach", "GelfandYoungPile"];
  GelfandYoungPile[any]
)

GroupRegularRepresentation::usage = "GroupRegularRepresentation is obsolete since v4.1.10 (2025-05-09); use LeftRegularRepresentation instead."

GroupRegularRepresentation[any___] := (
  Message[Q3General::obsolete, "GroupRegularRepresentation", "LeftRegularRepresentation"];
  LeftRegularRepresentation[any]
)

PileYoungShape::usage = "PileYoungShape has been renamed YoungShapePile since v4.1.7 (2025-04-13)."

PileYoungShape[any___] := (
  Message[Q3General::renamed, "PileYoungShape", "YoungShapePile"];
  YoungShapePile[any]
)

ConditionNumber::usage = "ConditionNumber has been renamed MatrixConditionNumber since v4.1.5 (2025-04-02)."

ConditionNumber[any___] := (
  Message[Q3General::renamed, "ConditionNumber", "MatrixConditionNumber"];
  MatrixConditionNumber[any]
)

AmplitudeEmbeddingGate::usage = "AmplitudeEmbeddingGate has been renamed AmplitudeEncoding since v4.1.4 (2025-03-19)."

AmplitudeEmbeddingGate[any___] := (
  Message[Q3General::renamed, "AmplitudeEmbeddingGate", "AmplitudeEncoding"];
  AmplitudeEncoding[any]
)

BasisEmbeddingGate::usage = "BasisEmbeddingGate has been renamed BasisEncoding since v4.1.4 (2025-03-19)."

BasisEmbeddingGate[any___] := (
  Message[Q3General::renamed, "BasisEmbeddingGate", "BasisEncoding"];
  BasisEncoding[any]
)

Affect::usage = "Affect is obsolete since v3.8.6 (2025-03-12). Just use Multiply."

Affect[any___] := (
  Message[Q3General::obsolete, "Affect", "Multiply"];
  Apply[Multiply, Reverse @ {any}]
)

QuantumCircuitTrim::usage = "QuantumCircuitTrim has been renamed QuantumElements since v3.8.6 (2025-03-12)."
QuantumCircuitTrim[any___] := (
  Message[Q3General::renamed, "QuantumCircuitTrim", "QuantumElements"];
  QuantumElements[any]
)

GottesmanInner::usage = "GottesmanInner has been renamed GottesmanDot."

GottesmanInner[any___] := (
  Message[Q3General::renamed, "GottesmanInner", "GottesmanDot"];
  GottesmanDot[any]
)

NoisyWickSimulate::usage = "NoisyWickSimulate has been renamed WickSimulate."

NoisyWickSimulate[any___] := (
  Message[Q3General::renamed, "NoisyWickSimulate", "WickSimulate"];
  WickSimulate[any]
)

WickRandomCircuit::usage = "WickRandomCircuit has been renamed RandomWickCircuitSimulate."

WickRandomCircuit[any___] := (
  Message[Q3General::renamed, "WickRandomCircuit", "RandomWickCircuitSimulate"];
  RandomWickCircuitSimulate[any]
)

FlavorNone::usage = "FlavorNone has been renamed FlavorCap."

FlavorNone[spec_] := (
  Message[Q3General::renamed, "FlavorNone", "FlavorCap"];
  FlavorCap[spec]
)

FlavorNoneQ::usage = "FlavorNoneQ has been renamed FlavorCapQ."

FlavorNoneQ[spec_] := (
  Message[Q3General::renamed, "FlavorNoneQ", "FlavorCapQ"];
  FlavorCapQ[spec]
)

TimesDaggerRight::usage = "TimesDaggerRight has been renamed AbsSquareLeft."

TimesDaggerRight[args__] := (
  Message[Q3General::renamed, "TimesDaggerRight", "AbsSquareLeft"];
  AbsSquareLeft[args]
)

WeightedLog::usage = "WeightedLog has been renamed ShannonLog."

WeightedLog[args__] := (
  Message[Q3General::renamed, "WeightedLog", "ShannonLog"];
  ShannonLog[2, args]
)

TheState::usage = "TheState has been excised since 28 Feb 2024 (Q3 v3.3.3)."

TheState[___] := Message[Q3General::excised, "TheState"]

TheOperator::usage = "TheOperator has been excised since 28 Feb 2024 (Q3 v3.3.3)."

TheOperator[___] := Message[Q3General::excised, "TheOperator"]


DefaultForm::usage = "DefaultForm is obsolete now. Use KetTrim instead."

DefaultForm[args__] := (
  Message[Q3General::obsolete, "DefaultForm", "KetTrim"];
  KetTrim[args]
)

CountYoungTableaux::usage = "CountYoungTableaux has been renamed YoungTableauCount."

CountYoungTableaux[args__] := (
  Message[Q3General::renamed, "CountYoungTableaux", "YoungTableauCount"];
  YoungTableauCount[args]
)

CountWeylTableaux::usage = "CountWeylTableaux has been renamed WeylTableauCount."

CountWeylTableaux[args__] := (
  Message[Q3General::renamed, "CountWeylTableaux", "WeylTableauCount"];
  WeylTableauCount[args]
)

RaiseLower::usage = "RaiseLower has been renamed RaisingLoweringForm."

RaiseLower[args___] := (
  Message[Q3General::renamed, "RaiseLower", "RaisingLoweringForm"];
  RaisingLoweringForm[args]
)

DyadExpression::usage = "DyadExpression has been renamed DyadForm."

DyadExpression[args__] := (
  Message[Q3General::renamed, "DyadExpression", "DyadForm"];
  DyadForm[args]
)

NormalForm::usage = "NormalForm has been renamed KetCanonical."

NormalForm[args___] := (
  Message[Q3General::renamed, "NormalForm", "KetCanonical"];
  KetCanonical[args]
)

LogicalForm::usage = "LogicalForm has been renamed KetRegulate since v2.11.8."

LogicalForm[args__] := (
  Message[Q3General::renamed, "LogicalForm", "KetRegulate"];
  KetRegulate[args]
)

TwoLevelU::usage = "TwoLevelU has been renamed GivensRotation."

TwoLevelU[args___] := (
  Message[Q3General::renamed, TwoLevelU, GivensRotation];
  GivensRotation[args]
)


GrayTwoLevelU::usage = "GrayTwoLevelU has been renamed FromTwoLevelU."

GrayTwoLevelU[args___] := (
  Message[Q3General::renamed, "GrayTwoLevelU", "FromTwoLevelU"];
  FromTwoLevelU[args]
)


FromTwoLevelU::usage = "FromTwoLevelU is obsolte now. Use Unfold instead."

FromTwoLevelU[mat_?MatrixQ, rest__] := (
  Message[Q3General::obsolete, FromTwoLevelU, Unfold];
  Unfold @ GivensRotation[mat, rest]
)

FromTwoLevelU[GivensRotation[mat_?MatrixQ, ij_, _Integer], ss:{__?QubitQ}] :=
  ( Message[Q3General::obsolete, FromTwoLevelU, Unfold];
    List @@ Unfold @ GivensRotation[mat, ij, ss] )


TwoLevelDecomposition::usage = "TwoLevelDecomposition is obsolte now. Use GivensFactor or GrayGivensFactor instead."

TwoLevelDecomposition[args__] := (
  Message[
    Q3General::obsolete, 
    "TwoLevelDecomposition", 
    "GivensFactor or GrayGivensFactor"
  ];
  Unfold /@ GivensFactor[args]
)


GrayControlledW::usage = "GrayControlledW is obsolete now. Use GrayControlledGate instead."

GrayControlledW[args___] := (
  Message[Q3General::obsolete, GrayControlledW, GrayControlledGate];
  GrayControlledGate[args]
)

YoungDominatesQ::usage = "YoungDominatesQ has been renamed DominatesQ and extended to any lists."

YoungDominatesQ[a_?YoungShapeQ, b_?YoungShapeQ] := (
  Message[Q3General::renamed, "YoungDominatesQ", "DominatesQ"];
  DominatesQ[a, b]
)


LindbladBasisMatrix::usage = "LindbladBasisMatrix has been renamed LieBasisMatrix."

LindbladBasisMatrix[args___] := (
  Message[Q3General::renamed, "LindbladBasisMatrix", "LieBasisMatrix"];
  LieBasisMatrix[args]
)

LindbladBasis::usage = "LindbladBasis has been renamed LieBasis."

LindbladBasis[args___] := (
  Message[Q3General::renamed, "LindbladBasis", "LieBasis"];
  LieBasis[args]
)

LindbladGenerator::usage = "LindbladGenerator has been renamed LindbladSupermap."

LindbladGenerator[args__] := (
  Message[Q3General::renamed, "LindbladGenerator", "LindbladSupermap"];
  LindbladSupermap[args]
)

QuissoAdd::usage = "QuissoAdd has been renamed QubitAdd."

QuissoAdd[args__] := (
  Message[Q3General::renamed, "QuissoAdd", "QubitAdd"];
  QubitAdd[args]
)

QuissoAddZ::usage = "QuissoAddZ has been renamed QubitAddZ."

QuissoAddZ[args__] := (
  Message[Q3General::renamed, "QuissoAddZ", "QubitAddZ"];
  QubitAddZ[args]
)

Swap::usage = "Swap has been renamed SWAP."

Swap[args__] := (
  Message[Q3General::renamed, Swap, SWAP];
  SWAP[args]
)

FockFourier::usage = "FockFourier is now obsolete. Use TransformByFourier instead."

FockFourier[args__] := (
  Message[Q3General::obsolete, "FockFourier", "TransformByFourier"];
  FourierMap[args]
)

FockInverseFourier::usage = "FockInverseFourier is now obsolete. Use TransformByFourierInverse instead."

FockInverseFourier[args__] := (
  Message[Q3General::obsolete, "FockInverseFourier", "TransformByFourierInvere"];
  InverseFourierMap[args]
)

KrausProduct::usage = "KrausProduct is now obsolete. Use HilbertSchmidtProduct insteas."

KrausProduct[args___] := (
  Message[Q3General::obsolete, "KrausProduct", "HilbertSchmidtProduct"];
  HilbertSchmidtProduct[args]
)


WignerFunction::usage = "WignerFunction is now obsolete; use the build-in WignerD function."

WignerFunction[j_, m_, n_, z_] := (
  Message[Q3General::obsolete, WignerFunction, WignerD];
  WignerD[{j, m, n}, z]
)

ControlledU::usage = "ControlledU[...] is obsolete. Use Elaborate[ControlledGate[...]] instead."

ControlledU[args___] := (
  Message[
    Q3General::obsolete,
    "ControlledU",
    "Elaborate[ControlledGate[...]]"
   ];
  Elaborate @ ControlledGate[args]
)

VerifyOracle::usage = "VerifyOracle has been excises since Q3 v2.12.1."

VerifyOracle[args___] := Message[Q3General::excised, "VerifyOracle"]

FockMatrix::usage = "FockMatrix is obsolete. Instead, use MatrixIn.\nNOTE: First convert any cat-form basis to ket-form by using FockKet. Calculating matrix elements in terms of cat-form vectors is slow."

FockMatrix[args___] := (
  Message[Q3General::obsolete, "FockMatrix", "MatrixIn"];
  MatrixIn[args]
)

FockMatrixForm::usage = "FockMatrixForm has been excised. Instead, use Map[MatrixForm, ...]."

FockMatrixForm[args___] := Message[Q3General::excised, "FockMatrixForm"]

(**** </obsolete> ****)


(**** <NambuMatrix> ****)

NambuMatrix::obsolete = "NambuMatrix[mat, ``] is obsolete; use `` instead."

NambuMatrix[mat_, "Green's"] := (
  Message[NambuMatrix::obsolete, "\"Green's\"", NambuGreen];
  NambuGreen[mat]
)

NambuMatrix[mat_, "Unitary"] := (
  Message[NambuMatrix::obsolete, "Unitary", NambuUnitary];
  NambuGreen[mat]
)

NambuMatrix[mat_, "Hermitian"] := (
  Message[NambuMatrix::obsolete, "Hermitian", NambuHermitian];
  NambuGreen[mat]
)

(**** </NambuMatrix> ****)


End[]

EndPackage[]
