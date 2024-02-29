(* -*- mode:math -*- *)
BeginPackage["Q3`"]

(**** <obsolete> ****)

{ LinearMap, LinearMapFirst }; (* deprecated *)

{ TheLower, TheRaise, RaiseLower }; (* renamed *)
{ PauliEmbed, PauliApply }; (* obsolete and excised *)
{ TheState, TheOperator }; (* obsolete and excised *)
{ NormalForm }; (* renamed *)
{ LogicalForm, DefaultForm }; (* obsolete since 2023-02-18 *)
{ PauliDecomposeOld, PauliComposeOld }; (* to be excised *)
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

HoldPattern @ Multiply[ pre___,
  Ket[a_Association], Bra[b_Association], post___] :=
  Multiply[pre, Dyad[a, b], post]
(* EXPERIMENTAL since v5.66 *)
(* NOTE (v5.85): This must come at the final stage and is moved to here.
   Otherwise, for example, Dagger[a[1]] ** Ket[] ** Bra[] ** a[1]
   results in Dagger[a[1]] ** Dyad[<||>,<|a[1]->1|>]. *)


(**** <fallbacks> ****)

MultiplyExp /:
HoldPattern @ Elaborate[ MultiplyExp[expr_] ] := MultiplyExp[expr]

(**** </fallbacks> ****)


(**** <deprecated> *****)

LinearMap::usage = "LinearMap represents linear maps.\nLet[LinearMap, f, g, \[Ellipsis]] defines f, g, \[Ellipsis] to be linear maps."

Let[LinearMap, {ls__Symbol}] := (
  Message[Q3General::deprecated, "LinearMap"];
  Scan[setLinearMap, {ls}]
)

setLinearMap[op_Symbol] := (
  op[a___, b1_ + b2_, c___] := op[a, b1, c] + op[a, b2, c];
  op[a___, z_?CommutativeQ, b___] := z op[a, b];
  op[a___, z_?CommutativeQ b_, c___] := z op[a, b, c];
 )


LinearMapFirst::usage = "LinearMapFirst represents functions that are linear for the first argument.\nLet[LinearMapFirst, f, g, \[Ellipsis]] defines f, g, \[Ellipsis] to be linear maps for their first argument."

Let[LinearMapFirst, {ls__Symbol}] := (
  Message[Q3General::deprecated, "LinearMapFirst"];
  Scan[setLinearMapFirst, {ls}]
)

setLinearMapFirst[op_Symbol] := (
  op[z_?CommutativeQ] := z;
  op[z_?CommutativeQ, b__] := z op[b];
  op[z_?CommutativeQ b_, c___] := z op[b, c]; (* NOTE: b_, not b__ ! *)
  op[b1_ + b2_, c___] := op[b1, c] + op[b2, c];
 )

(**** </deprecated> *****)


(**** <obsolete> ****)

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

TheRaise[args___] := (
  Message[Q3General::renamed, "TheRaise", "TheRaising"];
  TheRaising[args]
)

TheLower[args___] := (
  Message[Q3General::renamed, "TheLower", "TheLowering"];
  TheLowering[args]
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

SWAP::usage = "SWAP has been renamed Swap."

SWAP[args__] := (
  Message[Q3General::renamed, SWAP, Swap];
  Swap[args]
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


End[]

EndPackage[]
