(* -*- mode:math -*- *)
BeginPackage["Q3`"]

(**** <obsolete> ****)

{ GottesmanInner }; (* renamed *)
{ WickRandomCircuit }; (* renamed *)
{ WeightedLog }; (* renamed *)
{ PauliDecompose, PauliDecomposeRL, PauliCompose, PauliCompseRL }; (* renamed *)
{ WickGreensFunction };
{ FlavorNone, FlavorNoneQ }; (* renamed *)
{ TimesDaggerLeft, TimesLeftRight }; (* renamed *)
{ TheLower, TheRaise, RaiseLower }; (* renamed *)
{ PauliEmbed, PauliApply }; (* obsolete and excised *)
{ TheState, TheOperator }; (* obsolete and excised *)
{ NormalForm }; (* renamed *)
{ LogicalForm, DefaultForm }; (* obsolete since 2023-02-18 *)
{ DyadExpression }; (* renamed *)
{ WignerFunction }; (* obsolete *)
{ PauliExpression, PauliExpressionRL }; (* obsolete *)
{ PauliInner }; (* obsolete *)

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
{ Dirac }; (* OBSOLETE *)

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


(**** <obsolete> ****)

GottesmanInner[any___] := (
  Message[Q3General::renamed, "GottesmanInner", "GottesmanDot"];
  GottesmanDot[any]
)

WickRandomCircuit[any___] := (
  Message[Q3General::renamed, "WickRandomCircuit", "RandomWickCircuitSimulate"];
  RandomWickCircuitSimulate[any]
)

WickGreensFunction[spec_] := (
  Message[Q3General::renamed, "WickGreensFunction", "WickGreenFunction"];
  WickGreenFunction[spec]
)

FlavorNone[spec_] := (
  Message[Q3General::renamed, "FlavorNone", "FlavorCap"];
  FlavorCap[spec]
)

FlavorNoneQ[spec_] := (
  Message[Q3General::renamed, "FlavorNoneQ", "FlavorCapQ"];
  FlavorCapQ[spec]
)

WeightedLog[args__] := (
  Message[Q3General::renamed, "TimesDaggerLeft", "AbsSquare"];
  AbsSquare[args]
)

WeightedLog[args__] := (
  Message[Q3General::renamed, "TimesDaggerRight", "AbsSquareLeft"];
  AbsSquareLeft[args]
)

WeightedLog[args__] := (
  Message[Q3General::renamed, "WeightedLog", "ShannonLog"];
  ShannonLog[2, args]
)


PauliDecompose[args__] := (
  Message[Q3General::renamed, "PauliDecompose", "PauliCoefficients"];
  PauliCoefficients[args]
)

PauliDecomposeRL[args__] := (
  Message[Q3General::renamed, "PauliDecomposeRL", "PauliCoefficients"];
  PauliCoefficients[args, "RaisingLowering" -> True]
)

PauliCompose[args__] := (
  Message[Q3General::renamed, "PauliCompose", "PauliSeries"];
  PauliSeries[args]
)

PauliComposeRL[args__] := (
  Message[Q3General::renamed, "PauliComposeRL", "PauliSeries"];
  PauliSeries[args]
)


TheState::usage = "TheState has been excised since 28 Feb 2024 (Q3 v3.3.3)."

TheState[___] := Message[Q3General::excised, "TheState"]

TheOperator::usage = "TheOperator has been excised since 28 Feb 2024 (Q3 v3.3.3)."

TheOperator[___] := Message[Q3General::excised, "TheOperator"]


PauliApply[args___] := Message[Q3General::excised, "PauliApply"]

DefaultForm[args__] := (
  Message[Q3General::obsolete, "DefaultForm", "KetTrim"];
  KetTrim[args]
)

CountYoungTableaux[args__] := (
  Message[Q3General::renamed, "CountYoungTableaux", "YoungTableauCount"];
  YoungTableauCount[args]
)

CountWeylTableaux[args__] := (
  Message[Q3General::renamed, "CountWeylTableaux", "WeylTableauCount"];
  WeylTableauCount[args]
)

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


FromTwoLevelU::usage = "FromTwoLevelU is obsolte now. Use Expand instead."

FromTwoLevelU[mat_?MatrixQ, rest__] := (
  Message[Q3General::obsolete, FromTwoLevelU, Expand];
  Expand @ GivensRotation[mat, rest]
)

FromTwoLevelU[GivensRotation[mat_?MatrixQ, ij_, _Integer], ss:{__?QubitQ}] :=
  ( Message[Q3General::obsolete, FromTwoLevelU, Expand];
    List @@ Expand @ GivensRotation[mat, ij, ss] )


TwoLevelDecomposition::usage = "TwoLevelDecomposition is obsolte now. Use GivensFactor or GrayGivensFactor instead."

TwoLevelDecomposition[args__] := (
  Message[Q3General::obsolete, FromTwoLevelU, GivensFactor|GrayGivensFactor];
  Expand @ GivensFactor[mat, rest]
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

PauliExpression::usage = "PauliExpression is obsolete now. Use ExpressionFor instead."

PauliExpression[args___] := (
  Message[Q3General::obsolete, "PauliExpression", "ExpressionFor"];
  ExpressionFor[args]
)


PauliExpressionRL::usage = "PauliExpressionRL is obsolete now. Use ExpressionFor instead."

PauliExpressionRL[args___] := (
  Message[Q3General::obsolete, "PauliExpressionRL", "ExpressionFor"];
  ExpressionFor[args]
)

PauliInner::usage = "PauliInner is obsolete. Use HilbertSchmidtProduct instead. Notice the difference in normalization -- PauliInner[m1, m2] = HilbertSchmidtProduct[m1,m2] / Length[m2] for matrices m1 and m2."

PauliInner[m1_?MatrixQ, m2_?MatrixQ] := (
  Message[Q3General::obsolete, PauliInner, HilbertSchmidtProduct];
  HilbertSchmidtProduct[m1, m2] / Length[m2]
)

PauliInner[v1_?VectorQ, v2_?VectorQ] := (
  Message[Q3General::obsolete, PauliInner, HilbertSchmidtProduct];
  HilbertSchmidtProduct[v1, v2]
)

PauliEmbed::usage = "PauliEmbed is obsolete; instead, use MatrixEmbed."

PauliEmbed[args___] := (
  Message[Q3General::obsolete, "PauliEmbed", "MatrixEmbed"];
  MatrixEmbed[args]
)

WignerFunction::usage = "WignerFunction is now obsolete; use the build-in WignerD function."

WignerFunction[j_, m_, n_, z_] := (
  Message[Q3General::obsolete, WignerFunction, WignerD];
  WignerD[{j, m, n}, z]
)

Dirac::usage = "Dirac is OBSOLETE. Instead, use Dyad."

Dirac[expr__] := (
  Message[Q3General::obsolete, Dirac, Dyad];
  Dyad[expr]
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
