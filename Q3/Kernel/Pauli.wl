(* -*- mode: math; -*- *)

BeginPackage["Q3`"]

`Pauli`$Version = StringJoin[
  $Input, " v",
  StringSplit["$Revision: 6.1 $"][[2]], " (",
  StringSplit["$Date: 2023-07-16 22:31:19+09 $"][[2]], ") ",
  "Mahn-Soo Choi"
 ];

{ Spin, SpinNumberQ };

{ State, TheKet, TheBra, TheState };

{ KetChop, KetDrop, KetUpdate, KetRule, KetTrim, KetVerify,
  KetFactor, KetPurge, KetSort,
  KetSpecies, KetRegulate, KetMutate,
  KetCanonical };

{ KetNorm, KetNormalize, KetOrthogonalize }; 

{ KetPermute, KetSymmetrize };

{ GateFactor };

{ Permutation };

{ OTimes, OSlash, ReleaseTimes };

{ ProductForm, SimpleForm, SpinForm };

{ XBasisForm, YBasisForm };

{ BraKet };

{ Vacuum };

{ Basis,
  Matrix, TheMatrix,
  ExpressionFor, TheExpression,
  MatrixIn, ExpressionIn };

{ ProperSystem, ProperValues, ProperStates };

{ CommonEigensystem, CommonEigenvectors, CommonEigenvalues };

{ BlochSphere, BlochVector };

{ Affect };

{ Pauli, Raise, Lower, Hadamard, Quadrant, Octant, Hexadecant,
  ThePauli, TheRaise, TheLower, TheHadamard };
{ Operator, TheOperator };

{ RaiseLower };

{ Rotation, EulerRotation,
  TheRotation, TheEulerRotation };

{ RotationAngle, RotationAxis, RotationSystem,
  TheEulerAngles }

{ RandomVector, RandomMatrix, RandomHermitian, RandomPositive, RandomUnitary };

{ TridiagonalToeplitzMatrix };

{ BasisComplement };

{ CircleTimes, CirclePlus };

{ Dyad, DyadForm };

{ Zero, One };

{ Parity, ParityValue, ParityEvenQ, ParityOddQ };

{ TensorFlatten, Tensorize };
{ PartialTrace, PartialTranspose };
{ ReducedMatrix, Reduced };

{ PauliDecompose, PauliCompose, PauliVector };
{ PauliDecomposeRL, PauliComposeRL };

{ MatrixEmbed };

{ SchmidtDecomposition, SchmidtForm };

{ HilbertSchmidtProduct, HilbertSchmidtNorm, HilbertSchmidtDistance,
  FrobeniusProduct, FrobeniusNorm };

{ TraceNorm, TraceDistance, Fidelity, ClassicalFidelity };

{ LogarithmicNegativity, Negativity, NormPT };

{ Purification, Snapping };

{ GraphForm, ChiralGraphForm,
  Vertex, VertexLabelFunction, EdgeLabelFunction };


(**** OBSOLETE SYMBOLS ****)

{ PauliEmbed, PauliApply }; (* obsolete and excised *)

{ NormalForm }; (* renamed *)

{ LogicalForm, DefaultForm }; (* obsolete since 2023-02-18 *)

{ PauliDecomposeOld, PauliComposeOld }; (* to be excised *)

(* Now comes as a built-in function with v13.1, but with an additional
   Transpose compared to the old one.
   Kept here for backward compatibility. *)
{ PermutationMatrix };

(* Now an experimental built-in symbol since v13.1.
   Kept here for backward compatibility. *)
{ BlockDiagonalMatrix };

{ DyadExpression }; (* renamed *)
{ WignerFunction }; (* obsolete *)
{ PauliExpression, PauliExpressionRL }; (* obsolete *)
{ PauliInner }; (* obsolete *)

Begin["`Private`"]

$symbs = Unprotect[CircleTimes, CirclePlus, Dot, Ket, Bra]

Spin::usage = "Spin is an option of several Species.\nSpin[c] returns the Spin quantum number of the Species c.\nLet[Spin, s] declares that s is the Spin species."

SpinNumberQ::usage = "SpinNumberQ[J] returns True if J is a valid angular momentum quantum number (non-negative integer or half-integer).\nSpinNumberQ[J,M] returns True if J is a valid angular momentum quantum number and M is a valid magnetic quantum number (-j<=m<=j)."
(* To be defined further in other packages; e.g., Wigner. *)

SetAttributes[SpinNumberQ, {NHoldAll, ReadProtected}]

SpinNumberQ[_Integer?NonNegative] = True

SpinNumberQ[Rational[_,2]?Positive] = True

SpinNumberQ[j_Integer?NonNegative, m_Integer] := And[ -j <= m <= j ]

SpinNumberQ[j:Rational[_,2]?Positive, m:Rational[_,2]] := And[ -j <= m <= j ]

SpinNumberQ[{j_, m_}] := SpinNumberQ[j, m]

SpinNumberQ[__] = False


TheBra::usage = "TheBra[...] is formally different from but equalt to TheKet[...]."

TheBra[args__] := TheKet[args]


TheKet::usage = "TheKet[0]={1,0}, TheKet[1]={0,1}.
  TheKet[s1,s2,...] = TheKet[s1]\[CircleTimes]TheKet[s2]\[CircleTimes]...."

TheKet[0] = TheKet[Up] = {1, 0}

TheKet[1] = TheKet[Down] = {0, 1}

TheKet[x_?BinaryQ] = {1-x, x}

TheKet[aa:(0|1|Up|Down)..] := Module[
  { bb = {aa} /. {Up -> 0, Down -> 1},
    k },
  k = 1 + FromDigits[bb, 2];
  SparseArray[{k -> 1}, Power[2, Length @ bb]]
 ]

(* TheKet[ a:(0|1|Up|Down).. ] := CircleTimes @@ Map[TheKet,{a}] *)
(* It takes quite long for bit strings longer than 10. *)


TheState::usage = "TheState[{0, theta, phi}] = TheRotation[phi, 3].TheRotation[theta, 2].TheKet[0].
TheState[{1, theta, phi}] = TheRotation[phi,3].TheRotation[theta,2].TheKet[1].
TheState[{s1,t1,p1}, {s2,t2,p2}, ...] = TheState[{s1,t1,p1}] \[CircleTimes]
TheState[s2,t2,p2]\[CircleTimes]....  TheState[{{s1,s2,...}, th, ph}] =
TheState[{s1,th,ph}, {s2,th,ph}, ...]."
(* Ket is used so often that it is better to simplify its definition as much
   as possible. Hence State[] and its counterpart TheState[]. *)

TheState[ {(0|Up), theta:Except[_List], phi:Except[_List]} ] := {
  Exp[-I*phi/2]Cos[theta/2],
  Exp[+I*phi/2]Sin[theta/2]
 }

TheState[ {(1|Down), theta:Except[_List], phi:Except[_List]} ] := {
  -Exp[-I*phi/2]Sin[theta/2],
  +Exp[+I*phi/2]Cos[theta/2]
 }

TheState[ a:{(0|1|Up|Down), Except[_List], Except[_List]}.. ] :=
  CircleTimes @@ Map[TheState,{a}]

TheState[ { m:{(0|1|Up|Down)..}, t:Except[_List], p:Except[_List] } ] :=
  CircleTimes @@ Map[TheState] @ Tuples[{m, {t}, {p}}]


ThePauli::usage = "ThePauli[n] (n=1,2,3) returns a Pauli matrix.
  ThePauli[4]=TheRaise[] is the Raising operator, ThePauli[5]=TheLower[] is the Lowering operator, ThePauli[6]=TheHadamard[] is the Hadamard operator, and ThePauli[0] returns the 2x2 identity matrix.\nThePauli[n1,n2,n3,...]=ThePauli[n1] \[CircleTimes] ThePauli[n2] \[CircleTimes] ThePauli[n3]\[CircleTimes] ...."

TheRaise::usage = "TheRaise[]=(ThePauli[1]+I*ThePauli[2])/2={{0,1},{0,0}}.\nTheRaise[{J,1}] returns the raising operator for angular momentum J.\nTheRaise[{J,0}] returns the identity operator."

TheLower::usage = "TheLower[]=(ThePauli[1]-I*ThePauli[2])/2={{0,0},{1,0}}.\nTheLower[{J,1}] returns the raising operator for angular momentum J.\nTheLower[{J,0}] returns the identity matrix."

TheHadamard::usage = "TheHadamard[0]=IdentityMatrix[2]. TheHadamard[1]={{1,1},{1,-1}}/Sqrt[2] is the matrix corresponding to TheRotation[Pi/2,2].ThePauli[3].\nTheHadamard[{J,1}] returns TheRotation[Pi/2, {J,2}].TheWigner[{J,3}] for angular momentum J.\nTheHadamard[{J,0}] returns the identity matrix."

SetAttributes[ThePauli, {NHoldAll, ReadProtected, Listable}]

ThePauli[kk__] := ThePauli @@ ReplaceAll[
  { kk },
  { All -> {1, 2, 3},
    Full -> {0, 1, 2, 3} }
 ] /; ContainsAny[{kk}, {All, Full}]


ThePauli[] = {{1}}

ThePauli[0] = SparseArray[{{1, 1} -> 1, {2, 2} -> 1}, {2, 2}]

ThePauli[1] = ThePauli[-1] = SparseArray[{{1, 2} -> 1, {2, 1} -> 1}, {2, 2}]

ThePauli[2] = ThePauli[-2] = SparseArray[{{1, 2} ->-I, {2, 1} -> I}, {2, 2}]

ThePauli[3] = ThePauli[-3] = SparseArray[{{1, 1} -> 1, {2, 2} ->-1}, {2, 2}]


ThePauli[4] = ThePauli[-5] = TheRaise[] = TheRaise[1] = TheLower[-1] =
  SparseArray[{{1, 2} -> 1}, {2, 2}]

ThePauli[5] = ThePauli[-4] = TheLower[] = TheLower[1] = TheRaise[-1] =
  SparseArray[{{2, 1} -> 1}, {2, 2}]

ThePauli[6] = ThePauli[-6] = TheHadamard[] = TheHadamard[1] =
  {{1,1},{1,-1}}/Sqrt[2]

ThePauli[7] = TheQuadrant[] = TheQuadrant[1] =
  SparseArray[{{1, 1} -> 1, {2, 2} -> +I}, {2, 2}]

ThePauli[8] = TheOctant[] = TheOctant[1] =
  SparseArray[{{1, 1} -> 1, {2, 2} -> Exp[+I*Pi/4]}, {2, 2}]

ThePauli[9] = TheHexadecant[] = TheHexadecant[1] =
  SparseArray[{{1, 1} -> 1, {2, 2} -> Exp[+I*Pi/8]}, {2, 2}]

ThePauli[10] = SparseArray[{{1,1} -> 1}, {2,2}]

ThePauli[11] = SparseArray[{{2,2} -> 1}, {2,2}]


ThePauli[-1] = ThePauli[1]

ThePauli[-2] = ThePauli[2]

ThePauli[-3] = ThePauli[3]

ThePauli[-4] = ThePauli[5]

ThePauli[-5] = ThePauli[4]

ThePauli[-6] = ThePauli[6]

ThePauli[k_Integer?Negative] := Topple @ ThePauli[-k]


(* special phase gates *)
ThePauli @ C[n_Integer] :=
  SparseArray[{{1, 1} -> 1, {2, 2} -> Exp[I*2*Pi*Power[2,n]]}, {2, 2}]

ThePauli[-C[n_Integer]] := Topple @ ThePauli @ C[n]


ThePauli[Raise] = ThePauli[4]

ThePauli[Lower] = ThePauli[5]

ThePauli[Hadamard] = ThePauli[6]

ThePauli[Quadrant] = ThePauli[7]

ThePauli[Octant] = ThePauli[8]

ThePauli[Hexadecant] = ThePauli[9]

TheRaise[0] = TheLower[0] = TheHadamard[0] = TheQuadrant[0] = ThePauli[0]


(* These are for Matrix[Dyad[...]]. *)
ThePauli[1 -> 0] = ThePauli[4]

ThePauli[0 -> 1] = ThePauli[5]

ThePauli[0 -> 0] = ThePauli[10]

ThePauli[1 -> 1] = ThePauli[11]


ThePauli[ nn:(0|1|2|3|4|5|6|7|8|9|10|11|_Integer?Negative|_Rule).. ] :=
  CircleTimes @@ Map[ThePauli] @ {nn}


TheOperator::usage = "TheOperator[{n,\[Theta],\[Phi]}] gives a Pauli matrix in the nth direction in the (\[Theta],\[Phi])-rotated frame.
  TheOperator[{n1,t1,p1},{n2,t2,p2},...] = TheOperator[{n1,t1,p1}] \[CircleTimes] TheOperator[{n2,t2,p2}] \[CircleTimes] ... .
  TheOperator[{{n1,n2,...}, th, ph}] = TheOperator[{n1,th,ph}, {n2,th,ph}, ...]."

TheOperator[{0, theta_,phi_}] = ThePauli[0]

TheOperator[{n:(1|2|3), theta_, phi_}] := Matrix @ Operator[{n,theta,phi}]

TheOperator[ nn:{(0|1|2|3|4|5|6|Raise|Lower|Hadamard), _, _}.. ] :=
  CircleTimes @@ Map[TheOperator] @ {nn}

TheOperator[ { n:{(0|1|2|3|4|5|6|Raise|Lower|Hadamard)..},
    th:Except[_List], ph:Except[_List] } ] :=
  CircleTimes @@ Map[TheOperator] @ Tuples[{n, {th}, {ph}}]



(**** <KetRegulate> ****)

KetRegulate::usage = "KetRegulate[expr] converts every Ket[...] and Bra[...] in expr into the fully logical form without dropping any element.\nKetRegulate[expr, {S1, S2, \[Ellipsis]}] assumes that expr involves systems labeled by S1, S2, ....\nKetRegulate[expr, S] is quivalent to KetRegulate[expr, {S}].\nSee also KetTrim."

KetRegulate[expr_] := expr /;
  FreeQ[expr, Ket[_Association] | Bra[_Association]]


KetRegulate[expr_] := KetRegulate[expr, KetSpecies @ expr]

KetRegulate[expr_, S_?SpeciesQ] := KetRegulate[expr, S @ {$}]

KetRegulate[expr_, ss:{__?SpeciesQ}] :=
  KetRegulate[expr, FlavorNone @ ss] /; Not[FlavorNoneQ @ ss]

KetRegulate[expr_, ss:{__?SpeciesQ}] := With[
  { tt = KetSpecies[expr] },
  KetRegulate[expr, Union[ss, tt]] /;
    Not @ ContainsAll[ss, tt]
 ]


KetRegulate[v:(_Ket|_Bra), ss:{___?SpeciesQ}] = v

KetRegulate[Ket[a_Association], ss:{___?SpeciesQ}] :=
  Ket @ KeySort @ Join[a, AssociationThread[ss -> Lookup[a, ss]]]

KetRegulate[Bra[a_Association], ss:{___?SpeciesQ}] :=
  Dagger @ KetRegulate[Ket @ a, ss]

KetRegulate[OTimes[args__], ___] :=
  OTimes @@ Map[KetRegulate, {args}]

KetRegulate[OSlash[Ket[a_Association], expr_], ss:{__?SpeciesQ}] :=
  OSlash[Ket[a], KetRegulate[expr, Supplement[ss, Keys @ a]]]

KetRegulate[expr_Association, ss:{___?SpeciesQ}] :=
  Map[KetRegulate[#, ss]&, expr]
(* NOTE: Association needs to be handled carefully due to HoldAllComplete
   Attribute of Association. Otherwise, the result may be different from what
   you would expect.  *)

KetRegulate[expr_, ss:{___?SpeciesQ}] := expr /. {
  Interpretation[__, v_] :> KetRegulate[v, ss],
  v_OTimes :> KetRegulate[v, ss],
  v_OSlash :> KetRegulate[v, ss],
  a_Association :> KetRegulate[a, ss],
  v_Ket :> KetRegulate[v, ss],
  v_Bra :> KetRegulate[v, ss]
 }


LogicalForm::usage = "LogicalForm has been renamed KetRegulate since v2.11.8."

LogicalForm[args__] := (
  Message[Q3General::renamed, "LogicalForm", "KetRegulate"];
  KetRegulate[args]
 )

(**** </KetRegulate> ****)


(**** <KetMutate> ****)

KetMutate::usage = "KetMutate[expr, {s1, s2, \[Ellipsis]}] changes every Ket[v1,v2,\[Ellipsis]] to Ket[<|s1->v1, s2->v2, \[Ellipsis]|>] and vice versa in expr."

KetMutate[any_, ss:{__?SpeciesQ}] :=
  KetMutate[any, FlavorNone @ ss] /; Not[FlavorNoneQ @ ss]

KetMutate[any_Association, ss:{__?QubitQ}] := Map[KetMutate[#, ss]&, any]
(* NOTE: Recall that Association has attribute HoldAllComplete. *)

KetMutate[Ket[v__], ss:{__?SpeciesQ}] := Ket[ss -> PadRight[{v}, Length @ ss]]

KetMutate[Bra[v__], ss:{__?SpeciesQ}] := Bra[ss -> PadRight[{v}, Length @ ss]]

KetMutate[Ket[a_Association], ss:{__?SpeciesQ}] := Ket @@ Lookup[a, ss]

KetMutate[Bra[a_Association], ss:{__?SpeciesQ}] := Bra @@ Lookup[a, ss]

KetMutate[Pauli[v__], ss:{__?SpeciesQ}] := With[
  { qq = Select[ss, QubitQ] },
  Multiply @@ MapThread[
    Construct,
    {qq, PadRight[{v}, Length @ qq]}
   ]
 ]

KetMutate[expr_, ss:{__?SpeciesQ}] := ReplaceAll[ expr,
  { v_Association :> KetMutate[v, ss],
    v:(_Ket|_Bra_) :> KetMutate[v, ss],
    v_Pauli :> KetMutate[v, ss] }
 ]

(**** </KetMutate> ****)


(**** <SimpleForm> ****)

$KetDelimiter::usage = "The charater delimiting values in a Ket."

$KetGroupDelimiter::usage = "The charater delimiting groups of values in a Ket."

$KetDelimiter = "\[VeryThinSpace]";
$KetGroupDelimiter = ";";
$KetProductDelimiter = "\[CircleTimes]";


SimpleForm::usage = "SimpleForm[expr] represents every Ket in expr in the simplest form dropping all subsystem indices.\nSimpleForm[expr, {S1, ..., {S2, S3, ...}, ...}] splits each Ket into the form Ket @ Row @ {S1, ..., Ket[S2, S3, ...], ...}."

SimpleForm[expr_, ss_List] :=
  SimpleForm[expr, FlavorNone @ ss] /; Not[FlavorNoneQ @ ss]

SimpleForm[expr_] := SimpleForm[expr, {}]

SimpleForm[expr_, {}] := Module[
  { ss },
  ss = Union @ Flatten @ Cases[
    {expr},
    (Ket|Bra)[a_Association] :> Keys[a],
    Infinity
   ];
  SimpleForm[expr, {ss}]
 ]

SimpleForm[expr_, S_?SpeciesQ] := SimpleForm[expr, S @ {$}]

SimpleForm[v:Ket[_Association], gg_List] :=
  Interpretation[theSimpleForm[v, gg], v]

SimpleForm[Bra[a_Association], gg_List] :=
  Interpretation[Dagger @ theSimpleForm[Ket @ a, gg], Bra @ a]

(* For some irreducible basis, e.g., from QubitAdd[] *)
SimpleForm[expr_Association, gg_List] :=
  Map[SimpleForm[#, gg]&, expr]
(* NOTE: Association needs to be handled carefully due to HoldAllComplete
   Attribute of Association. Otherwise, the result may be different from what
   you would expect.  *)

SimpleForm[expr_, gg_List] := expr /. {
  Interpretation[__, v_] :> SimpleForm[v, gg],
  a_Aggociation :> SimpleForm[a, gg],
  v_Ket :> SimpleForm[v, gg],
  v_Bra :> SimpleForm[v, gg]
 }


theSimpleForm::usage = "theSimpleForm[ket, {s1, s2, ...}] converts ket into a simple form."

theSimpleForm[vec:Ket[_Association], gg_List] := With[
  { ss = SequenceReplace[gg, {xx:Except[_List]..} -> {xx}] },
  Ket @ List @ Row[
    Map[Row[#, $KetDelimiter]&, Flatten /@ vec /@ ss],
    $KetGroupDelimiter
   ]
 ]

(**** </SimpleForm> ****)


(**** <ProductForm> ****)

ProductForm::usage = "ProductForm[expr] displays every Ket[...] in expr in the product form.\nProductForm[expr, {S1, ..., {S2,S3,...}, ...}] splits each Ket into the form Row[{Ket[S1], ..., Ket[S2,S3,...], ...}]."

ProductForm[expr_, ss_List] :=
  ProductForm[expr, FlavorNone @ ss] /; Not[FlavorNoneQ @ ss]

ProductForm[expr_] := ProductForm[expr, Agents @ expr]

ProductForm[expr_, S_?SpeciesQ] := SimpleForm[expr, S @ {$}]

ProductForm[vec:Ket[_Association], gg_List] :=
  Interpretation[theProductForm[vec, gg], vec]

ProductForm[Bra[a_Association], gg_List] :=
  Interpretation[Dagger @ theProductForm[Ket @a, gg], Bra[a]]

(* For some irreducible basis, e.g., from QubitAdd[] *)
ProductForm[expr_Association, gg_List] := Map[ProductForm[#, gg]&, expr]
(* NOTE: Association needs to be handled carefully due to HoldAllComplete
   Attribute of Association. Otherwise, the result may be different from what
   you would expect.  *)

ProductForm[ expr_, gg_List ] := expr /. {
  Interpretation[__, v_] :> ProductForm[v, gg],
  v_Aggociation :> ProductForm[v, gg],
  v_Ket :> ProductForm[v, gg],
  v_Bra :> ProductForm[v, gg]
 }


theProductForm::usage = "theProductForm[ket, {s1, s2, \[Ellipsis]}] converts ket into a product form."

theProductForm[vec:Ket[_Association], gg_List] := Row[
  Map[
    Ket @ List @ Row[#, $KetDelimiter]&,
    Flatten /@ List /@ vec /@ gg
   ],
  $KetProductDelimiter
 ]

(**** </ProductForm> ****)


(**** <SpinForm> ****)

SpinForm::usage = "SpinForm[expr, {s1, s2, ...}] converts the values to \[UpArrow] or \[DownArrow] in every Ket[<|...|>] appearing in expr.\nIf the Species is a Qubit, SpinForm converts 0 to \[UpArrow] and 1 to \[DownArrow].\nIf the Species is a Spin, SpinForm converts 1/2 to \[UpArrow] and -1/2 to \[DownArrow]."

SpinForm[expr_, a_List, b_List] :=
  SpinForm[expr, FlavorNone @ a, FlavorNone @ b] /;
  Not[FlavorNoneQ @ {a, b}]

SpinForm[expr_] := SpinForm[expr, Agents @ expr, {}]

SpinForm[expr_, s_?SpeciesQ, rest_] := SpinForm[expr, s @ {$}, rest]

SpinForm[expr_, qq_List, s_?SpeciesQ] := SpinForm[expr, qq, s @ {$}]

SpinForm[v_Ket, rest__] :=
  Interpretation[theSpinForm[v, rest], v]
  
SpinForm[Bra[spec___], rest___] :=
  Interpretation[Dagger @ theSpinForm[Ket[spec], rest], Bra[spec]]
  
SpinForm[expr_, qq_List] := SpinForm[ expr, FlavorNone @ qq,
  Complement[Agents @ expr, FlavorNone @ qq]
 ]

SpinForm[expr_Association, rest__] := Map[SpinForm[#, rest]&, expr]
  
SpinForm[expr:Except[_Ket|_Bra], rest__] := expr /. {
  Interpretation[__, v_] :> SpinForm[v, rest],
  a_Association :> Spinfrom[a, rest],
  v_Ket :> SpinForm[v, rest],
  v_Bra :> SpinForm[v, rest]
 }


theSpinForm[Ket[vv:(0|1)..], ___] := 
  Ket @ List @ Row[{vv} /. {0 -> "\[UpArrow]", 1 -> "\[DownArrow]"}]

theSpinForm[vec:Ket[a_Association], gg_List, kk_List] := Module[
  { ss = SequenceReplace[gg, {xx:Except[_List]..} -> {xx}],
    rr = Flatten @ kk,
    vv },
  vv = Join[
    (vec /@ ss) /. {(0|1/2) -> "\[UpArrow]", (1|-1/2) -> "\[DownArrow]"},
    {vec @ rr} /. {{} -> Nothing}
   ];
  Ket @ List @ Row[
    Map[Row[#, $KetDelimiter]&, Flatten /@ vv],
    $KetGroupDelimiter
   ]
 ]

(**** </SpinForm> ****)


(**** <KetCanonical> ****)

KetCanonical::usage = "KetCanonical[expr] returns the canonical form of ket expression expr."

SetAttributes[KetCanonical, Listable]

KetCanonical[expr_] := With[
  { v = First @ Union @ KetRegulate @ Cases[expr, _Ket, Infinity] },
  Garner[expr / (Dagger[v] ** expr)]
 ] /; Not @ FreeQ[expr, _Ket]

KetCanonical[any_] = any


NormalForm::usage = "NormalForm has been renamed KetCanonical."

NormalForm[args___] := (
  Message[Q3General::renamed, "NormalForm", "KetCanonical"];
  KetCanonical[args]
 )

(**** </KetCanonical> ****)


(**** <XBasisForm> ****)

XBasisForm::usage = "XBasisForm[expr, {q1,q2,\[Ellipsis]}] displays the quantum state in expression expr in the eigenbasis of the Pauli X operator for qubits q1, q2, \[Ellipsis]."

XBasisForm[expr_, q_?QubitQ] := XBasisForm[expr, q @ {$}] 

XBasisForm[expr_, qq:{__?QubitQ}] := 
  XBasisForm[expr, FlavorNone @ qq] /; Not[FlavorNoneQ @ qq]

XBasisForm[expr_, qq:{__?QubitQ}] :=
  Interpretation[Garner @ theXBasisForm[expr, qq], expr]

theXBasisForm[v_Ket, qq:{__?QubitQ}] := With[
  { op = Multiply @@ Through[qq[6]] },
  theXBasisLabel[op ** v, qq]
 ]

theXBasisForm[Bra[v_], qq:{__?QubitQ}] :=
  Dagger @ theXBasisForm[Ket[v], qq]

theXBasisForm[expr_, qq:{__?QubitQ}] :=
  ReplaceAll[ expr,
    { v_Ket :> theXBasisForm[v, qq], 
      v_Bra :> theXBasisForm[v, qq] }
   ]

theXBasisLabel[Ket[v_], qq:{__?QubitQ}] := 
  Ket @ Join[ v,
    AssociationThread[
      qq -> ReplaceAll[Lookup[v, qq], {0 -> "+", 1 -> "-"}]
     ]
   ]

theXBasisLabel[expr_, qq:{__?QubitQ}] :=
  ReplaceAll[ expr, v_Ket :> theXBasisLabel[v, qq] ]

(**** </XBasisForm> ****)


(**** <YBasisForm> ****)

YBasisForm::usage = "YBasisForm[expr, {q1,q2,\[Ellipsis]}] displays the quantum state in expression expr in the eigenbasis of the Pauli Y operator for qubits q1, q2, \[Ellipsis]."

YBasisForm[expr_, q_?QubitQ] := YBasisForm[expr, q @ {$}] 

YBasisForm[expr_, qq:{__?QubitQ}] := 
  YBasisForm[expr, FlavorNone @ qq] /; Not[FlavorNoneQ @ qq]

YBasisForm[expr_, qq:{__?QubitQ}] :=
  Interpretation[Garner @ theYBasisForm[expr, qq], expr]

theYBasisForm[v_Ket, qq:{__?QubitQ}] := With[
  { op = Multiply @@ Join[Through[qq[6]], Through[qq[7]]] },
  theYBasisLabel[op ** v, qq]
 ]

theYBasisForm[Bra[v_], qq:{__?QubitQ}] :=
  Dagger @ theYBasisForm[Ket[v], qq]

theYBasisForm[expr_, qq:{__?QubitQ}] :=
  ReplaceAll[ expr,
    { v_Ket :> theYBasisForm[v, qq], 
      v_Bra :> theYBasisForm[v, qq] }
   ]

theYBasisLabel[Ket[v_], qq:{__?QubitQ}] := 
  Ket @ Join[ v,
    AssociationThread[
      qq -> ReplaceAll[Lookup[v, qq], {0 -> "R", 1 -> "L"}]
     ]
   ]

theYBasisLabel[expr_, qq:{__?QubitQ}] :=
  ReplaceAll[ expr, v_Ket :> theYBasisLabel[v, qq] ]


(**** </YBasisForm> ****)


Affect::usage = "Affect[ket, op1, op2, ...] operates the operators op1, op2, ... (earlier operators first) on ket. Notice the order of the arguments. The result should be equivalent to Multiply[..., op2, op1, ket], but it is much faster than the counterpart for deep (the numer of operators is much bigger than the number of particles) expression. First first argument does not need to be a Ket, but otherwise Affect is not an advantage over Multiply."

SetAttributes[Affect, Listable]

Affect[ket_, op__] := Distribute[ theAffect @@ Garner[{ket, op}] ]

theAffect[ket_, a_, b__] := Fold[ theAffect, ket, {a, b} ]

theAffect[ket_, op_Multiply] := theAffect[ket, Sequence @@ Reverse[op]]

theAffect[ket_, op_] := Garner @ Multiply[op, ket]


fPauliKetQ::usage = "fPauliKetQ[expr] returns True if expr is a valid expression for a state vector of a system of unlabelled qubits.\nPauli[\[Ellipsis]] operates consistently on such an expression.";

HoldPattern @ fPauliKetQ[Ket[(0|1)..]] = True

HoldPattern @ fPauliKetQ[Multiply[__, Ket[(0|1)..]]] = True

HoldPattern @ fPauliKetQ[z_?CommutativeQ expr_] := fPauliKetQ[expr]

HoldPattern @ fPauliKetQ[Plus[terms__]] := TrueQ[
  And @@ fPauliKetQ /@ DeleteCases[ {terms}, (Complex[0., 0.] | 0.) ]
 ]
(* NOTE: 0. or Complex[0., 0.] can ocur in numerical evaluattions. *)

HoldPattern @ fPauliKetQ[expr_Times] := fPauliKetQ@Expand[expr]

HoldPattern @ fPauliKetQ[expr_] := False /; FreeQ[expr, Ket[(0 | 1) ..]]

HoldPattern @ fPauliKetQ[expr_] := False /;
  Not[Equal @@ Length /@ Cases[{expr}, _Ket, Infinity]]


fKetQ::usage = "fKetQ[expr] returns True if expr is a valid expression for a state vector of a system of labelled qubits.";

HoldPattern @ fKetQ[Ket[_Association]] = True

HoldPattern @ fKetQ[Multiply[__, Ket[_Association]]] = True

HoldPattern @ fKetQ[z_?CommutativeQ expr_] := fKetQ[expr]

HoldPattern @ fKetQ[Plus[terms__]] := TrueQ[
  And @@ fKetQ /@ DeleteCases[ {terms}, (Complex[0., 0.] | 0.) ]
 ]
(* NOTE: 0. or Complex[0., 0.] can ocur in numerical evaluattions. *)

HoldPattern @ fKetQ[expr_Times] := fKetQ @ Expand[expr]

HoldPattern @ fKetQ[expr_] := False /; FreeQ[expr, Ket[_Association]]


(**** <KetFormat> <BraFormat>****)

KetFormat::usage = "KetFormat[\[Ellipsis]] is a low-level function to display Ket[\[Ellipsis]]."

KetFormat[a_List] :=
  DisplayForm @ TemplateBox[List @ Row[theKetFormat /@ a, ","], "Ket"]

KetFormat[a_] :=
  DisplayForm @ TemplateBox[List @ Row[theKetFormat @ a, $KetDelimiter], "Ket"]

BraFormat[a_List] :=
  DisplayForm @ TemplateBox[List @ Row[theKetFormat /@ a, ","], "Bra"]

BraFormat[a_] :=
  DisplayForm @ TemplateBox[List @ Row[theKetFormat @ a, $KetDelimiter], "Bra"]


theKetFormat[Vacuum] = Any

theKetFormat[Association[]] = {Any}

theKetFormat[a_Association] := KeyValueMap[SpeciesBox[#2, {#1}, {}]&, a]


theKetFormatQ[_] = False

theKetFormat[v_] = v

(**** </KetFormat> </BraFormat> ****)


(**** <Ket & Bra> ****)

Ket::usage = "Ket represents a basis state of a system of Spins or similar systems.\nKet[0] and Ket[1] represent the two eigenvectors of the Pauli-Z matrix Pauli[3]. Ket[s$1, s$2, ...] represents the tensor product Ket[s$1] \[CircleTimes] Ket[s$2] \[CircleTimes] ....\nSee also Ket, TheKet, Bra, TheBra, State, TheState, Pauli, ThePauli, Operator, TheOperator."

Bra::usage = "Bra[expr] = Dagger[ Ket[expr] ].\nSee also Bra, TheBra, Ket, TheKet, Pauli, ThePauli."

SetAttributes[{Ket, Bra}, NHoldAll]
(* The integers in Ket[] and Bra[] should not be converted to real
   numbers by N[]. *)

If[ $VersionNumber > 13.2,
  SyntaxInformation[Ket] = {"ArgumentsPattern" -> {___}};
  SyntaxInformation[Bra] = {"ArgumentsPattern" -> {___}};
 ]


Format[Ket[v:(_List|_Association)]] := Interpretation[KetFormat[v], Ket[v]]

Format[Ket[v_]] := Interpretation[KetFormat @ {v}, Ket[v]]

Format[Ket[a_, b__]] := Interpretation[KetFormat @ {a, b}, Ket[a, b]]


Format[Bra[v:(_List|_Association)]] := Interpretation[BraFormat[v], Bra[v]]

Format[Bra[v_]] := Interpretation[BraFormat @ {v}, Bra[v]]

Format[Bra[a_, b__]] := Interpretation[BraFormat @ {a, b}, Bra[a, b]]


Ket /: NonCommutativeQ[ Ket[___] ] = True

Bra /: NonCommutativeQ[ Bra[___] ] = True

Ket /: MultiplyKind[ Ket[___] ] = Ket

Bra /: MultiplyKind[ Bra[___] ] = Bra

Ket /: MultiplyGenus[ Ket[___] ] = "Ket"

Bra /: MultiplyGenus[ Bra[___] ] = "Bra"

Ket /: Dagger[Ket[a___]] := Bra[a]

Bra /: Dagger[Bra[a___]] := Ket[a]

Ket /:
CircleTimes[a:Ket[_Association], b:Ket[_Association]..] :=
  KeySort /@ Join[a, b, 2]

Bra /:
CircleTimes[a:Bra[_Association], b:Bra[_Association]..] :=
  KeySort /@ Join[a, b, 2]

Ket /: CircleTimes[a_Ket, b__Ket] := Ket @@ Catenate[List @@@ {a, b}]

Bra /: CircleTimes[a_Bra, b__Bra] := Bra @@ Catenate[List @@@ {a, b}]


(* Ket[<|...|>] *)

Ket[] = Ket[ Association[] ]

Ket[ spec__Rule ] := Ket[ Ket[], spec ]

Ket[ Ket[a_Association], spec__Rule ] := Module[
  { rules = Flatten @ KetRule @ {spec},
    vec },
  vec = Ket @ KeySort @ Join[a, Association @ rules];
  If[FailureQ @ KetVerify @ vec, $Failed, vec]
 ]


Ket[ spec___Rule, ss:{__?AgentQ}] := KetRegulate[Ket[spec], ss]

Ket[ v_Ket, spec___Rule, ss:{__?AgentQ}] := KetRegulate[Ket[v, spec], ss]


(* operator form *)
Ket[a_Association][spec__Rule] := Ket[ Ket[a], spec ]

(* extracting the values *)
Ket[a_Association][ss_List] := Lookup[a, FlavorNone @ ss]

(* extracting a value *)
Ket[a_Association][s_] := a[FlavorNone @ s]


Bra[] = Bra[ Association[] ]

Bra[spec__Rule] := Dagger @ Ket[Ket[], spec]

Bra[v_Bra, spec__Rule] := Dagger @ Ket[Dagger @ v, spec]


Bra[ spec___Rule, ss:{__?SpeciesQ}] := KetRegulate[Bra[spec], ss]

Bra[ v_Bra, spec___Rule, s_?SpeciesQ] := KetRegulate[Bra[v, spec], {s}]

Bra[ v_Bra, spec___Rule, ss:{__?SpeciesQ}] := KetRegulate[Bra[v, spec], ss]


Bra[a_Association][spec__Rule] := Bra[ Bra[a], spec ]

Bra[a_Association][ss_List] := Lookup[a, FlavorNone @ ss]

Bra[a_Association][s_] := a[FlavorNone @ s]


KetRule::usage = "KetRule[rule] is a low-level function used when constructing Ket[<|\[Ellipsis]|>] to generate proper elementary rules from the compound rule specified in rule."

SetAttributes[KetRule, Listable]

KetRule[ r:Rule[_, _] ] := FlavorNone[r]

KetRule[ r:Rule[_List, _] ] := FlavorNone @ Thread[r]

KetRule[r_Rule] := r


KetVerify::usage = "KetVerify[ket] returns ket if ket is a valid Ket; $Failed otherwise.\nKetVerify[a, b] returns a->b if Ket[<|a->b|>] is a valid Ket; $Failed otherwise.\nKetVerify[expr] checks every Ket[<|...|>] in expr."

SetAttributes[KetVerify, Listable]

KetVerify[ expr_ ] := expr //. { v_Ket :> KetVerify[v] }

KetVerify[ Ket[a_Association] ] := With[
  { aa = KeyValueMap[KetVerify, a] },
  If[ AnyTrue[aa, FailureQ],
    $Failed,
    Ket @ Association @ aa,
    Ket @ Association @ aa
   ]
 ]

KetVerify[a_, b_] := Rule[a, b]


(**** <KetTrim> ****)

theKetTrim::usage = "KetTrim[assoc] removes from assoc the elements that are either irrelevant or associated with the default value."

theKetTrim[a_Association] := AssociationMap[theKetTrim, a]

theKetTrim[any_Rule] = any

theKetTrim[{} -> _] = Nothing (* a fallback *)

(* theKetTrim[Rule[_String, _]] = Nothing *)
(* an actual option *)


KetTrim::usage = "KetTrim[expr] converts every Ket[...] and Bra[...] in expr into the simplest form by dropping elements with default values.\nTo be compared with KetRegulate."

KetTrim[Ket[a_Association]] := Ket[theKetTrim @ a]

KetTrim[expr_] := expr /; FreeQ[expr, _Ket | _Bra]

KetTrim[expr_] := expr /. {
  a_OTimes -> a, (* NOTE *)
  HoldPattern[OSlash[v_Ket, new_]] :> OSlash[v, KetTrim @ new],
  Ket[a_Association] :> Ket[theKetTrim @ a],
  Bra[a_Association] :> Bra[theKetTrim @ a]
 }
(* NOTE: This line is necessary to prevent the Kets and Bras in OTimes from
   being affected. *)

DefaultForm[args__] := (
  Message[Q3General::obsolete, "DefaultForm", "KetTrim"];
  KetTrim[args]
 )

(**** </KetTrim> ****)


KetSpecies::usage = "KetSpecies[expr] returns the list of all species of Ket-like objects in expression expr."

KetSpecies[expr_] := Select[
  Union @ Catenate[
    Keys /@ Cases[{expr},
      (Ket|Bra|ProductState|CoherentState)[a_Association] -> a, Infinity]
   ],
  NonCommutativeQ
 ]


KetChop::usage = "KetChop[expr] removes approximate zeros, 0.` or 0.` + 0.`\[ImaginaryI], from expr, where the rest is a valid Ket expression."

SetAttributes[KetChop, Listable]

KetChop[0. + expr_] := expr /; Not @ FreeQ[expr, _Ket]

KetChop[Complex[0., 0.] + expr_] := expr /; Not @ FreeQ[expr, _Ket]

KetChop[expr_] := expr


KetDrop::usage = "KetDrop[v, {s1, s2, \[Ellipsis]}] returns Ket[<|\[Ellipsis]|>] with the species {s1, s2, \[Ellipsis]} removed from v.\nKetDrop[expr, {s1, s2, \[Ellipsis]}] removes {s1, s2, \[Ellipsis]} from every ket in expr.\nKetDrop[{s1,s2,\[Ellipsis]}] is an operator form of KetDrop."

KetDrop[Ket[a_Association], ss:{__?SpeciesQ}] :=
  Ket @ KeyDrop[a, FlavorNone @ ss]

KetDrop[assoc_Association, ss:{__?SpeciesQ}] := Map[KetDrop[ss], assoc]

KetDrop[expr_, ss:{__?SpeciesQ}] := expr /. {
  v:Ket[_Association] :> KetDrop[v, ss]
 }

KetDrop[any_, S_?SpeciesQ] := KetDrop[any, {S}]

KetDrop[S_?SpeciesQ][any_] := KetDrop[any, {S}]

KetDrop[ss:{__?SpeciesQ}][any_] := KetDrop[any, ss]


KetPurge::usage = "KetPurge[expr, test] puts every Ket[\[Ellipsis]] to zero if test holds true. Here, test is an inequality or equality in terms of species.\nKetPurge[test] represents an operator form of KetPurge."

KetPurge[test_][expr_] := KetPurge[expr, test]

KetPurge[Ket[asso_Association], test_] := Module[
  { cond },
  cond = ReleaseHold[
    test /. {
      S_?SpeciesQ[j___] :> Lookup[asso, S[j,$]],
      S_Symbol?SpeciesQ :> Lookup[asso, S[$]]
     }
   ];
  If[cond, 0, Ket[asso], Ket[asso]]
 ]

KetPurge[expr:(_List|_Association), test_] :=
  DeleteCases[KetPurge[test] /@ expr, 0|{}]

KetPurge[expr_, test_] := expr /. {
  v:Ket[_Association] :> KetPurge[v, test]
 }

KetUpdate::usage = "KetUpdate[ket, {s1->expr1, s2->expr2, \[Ellipsis]}] updates ket according to the rules specified by {s1->expr1, s2->expr2, \[Ellipsis]}.\nKetUpdate[expr, spec] converts every ket in expr."

KetUpdate[Ket[asso_Association], spec:{__Rule}] := Module[
  { new, kk, vv, qq },
  new = Map[
    ReleaseHold @ ReplaceAll[ #,
      { S_?SpeciesQ[j___] :> Lookup[asso, S[j,$]],
        S_Symbol?SpeciesQ :> Lookup[asso, S[$]] }
     ]&,
    Association @ spec
   ];
  Ket[Ket @ asso, Sequence @@ Normal[new, Association]]
 ]

KetUpdate[asso_Association, spec__] := KetUpdate[#, spec]& /@ asso

KetUpdate[expr_, spec:{__Rule}] :=
  expr /. { v_Ket :> KetUpdate[v, spec] }

KetUpdate[expr_, spec__Rule] := KetUpdate[expr, {spec}]


KetSort::usage = "KetSort[expr, {s1, s2, \[Ellipsis]}] sorts the logical values of species s1, s2, \[Ellipsis] in every Ket[<|\[Ellipsis]|>] appearing in expr.\nKetSort[expr] applies to all species involved in expr. When expr involves Ket[\[Ellipsis]] for unlabelled qubits, KetSort applies Sort[Ket[\[Ellipsis]]] to every Ket[\[Ellipsis]] in expr."

KetSort[vec:Ket[_Association], ss:{__?SpeciesQ}] := Module[
  { val = Sort @ vec[ss] },
  vec[ss -> val]
 ]

KetSort[vec:Ket[Except[_Association], ___]] := Sort[vec] (* Pauli Ket *)

KetSort[expr_] := KetSort[expr, Agents @ expr] /;
  Not @ FreeQ[expr, Ket[_Association]]

KetSort[expr_] := expr /. { v:Ket[__] :> KetSort[v] }

KetSort[expr_, ss:{__?SpeciesQ}] := expr /. {
  v:Ket[_Association] :> KetSort[v, ss]
 }

(**** </Ket & Bra> ****)


KetNorm::usage = "KetNorm[expr] returns the norm of Ket expression expr."

SetAttributes[KetNorm, Listable]

KetNorm[0] = 0

KetNorm[z_?CommutativeQ * any_Ket] := Abs[z]

KetNorm[expr_] := With[
  { spc = Agents[expr] },
  If[ Length[Garner @ expr] > Apply[Times, Dimension @ spc]/2 > Power[2, 3],
    Norm @ Matrix[expr, spc],
    Sqrt[Dagger[expr] ** expr]
   ]
 ] /; Not @ FreeQ[expr, _Ket]


KetNormalize::usage = "KetNormalize[expr] returns the normalized form of a ket expression expr.\nKetNormalize[expr, f] normalizes with respect to the norm function f."

KetNormalize[0] = 0

KetNormalize[expr_] := Garner[expr / KetNorm[expr]] /;
  Not @ FreeQ[expr, _Ket]

KetNormalize[expr_, func_] := Garner[expr / func[expr]] /;
  Not @ FreeQ[expr, _Ket]

KetNormalize[expr_, ___] = expr


KetOrthogonalize::usage = "KetOrthogonalize[vecs] orthgonalizes the vectors in vecs."

KetOrthogonalize[{}] := {}

KetOrthogonalize[vv:{__}] := Module[
  { ss = Agents[vv],
    bs, mm },
  bs = Basis[ss];
  mm = Matrix[vv, ss];
  DeleteCases[Garner[Orthogonalize[mm] . bs], 0]
 ] /; NoneTrue[vv, FreeQ[#, Ket[_Association]]&]

KetOrthogonalize[vv:{__}] := Module[
  { nn, bs, mm },
  nn = Length @ FirstCase[vv, _Ket, {}, Infinity];
  bs = Basis[nn];
  mm = Matrix[vv];
  DeleteCases[Garner[Orthogonalize[mm] . bs], 0]
 ] /; NoneTrue[vv, FreeQ[#, Ket[(0|1)..]]&]


(**** <KetFactor> ****)

KetFactor::usage = "KetFactor[expr] tries to factorize the ket expression expr, and if successful, it returns the result in terms of OTimes[\[Ellipsis]]. Otherwise it just throws expr out.\nKetFactor[expr, s] or KetFactor[expr, {s1, s2, \[Ellipsis]}] factors out the state concerning the specified species and returns the result in terms of OSlash[\[Ellipsis]]."

KetFactor[in_Association, qq:{__?SpeciesQ}] :=
  Map[KetFactor[#, qq]&, in]

KetFactor[in_List, qq:{__?SpeciesQ}] :=
  Map[KetFactor[#, qq]&, in]

KetFactor[Ket[a_Association], qq:{__?SpeciesQ}] := Module[
  { ss = FlavorNone[qq] },
  OSlash[ KetRegulate[Ket[KeyTake[a, ss]], ss], Ket[KeyDrop[a, ss]] ]
 ]

KetFactor[z_?CommutativeQ expr_ , qq:{__?SpeciesQ}] :=
  z KetFactor[expr, qq]

KetFactor[expr_, S_?SpeciesQ] := KetFactor[expr, {S}]

KetFactor[expr_Plus, qq:{__?SpeciesQ}] :=
  KetFactor @ Map[KetFactor[#, qq]&, expr]

KetFactor[expr_Plus, qq:{__?SpeciesQ}] := Module[
  { new },
  new = Factor[ketSplit @ KetRegulate[expr, qq]];
  ReplaceAll[new, Times -> OTimes]
 ] /; ContainsAll[FlavorNone @ qq, Agents @ expr]


KetFactor[v_Ket] := v

KetFactor[OSlash[vec_, expr_]] := OSlash[vec, KetFactor[expr]]

KetFactor[expr_Association] := Map[KetFactor, expr]

KetFactor[expr_List] := Map[KetFactor, expr]

KetFactor[expr_] := Module[
  { new },
  new = Factor[ketSplit @ expr];
  ReplaceAll[new, Times -> OTimes]
 ]


ketSplit[ Ket[] ] := Ket[]

ketSplit[ Ket[a_Association] ] := 
  Times @@ Map[ Ket @* Association, Normal @ a ] /;
  Length[a] > 0

ketSplit[ Bra[] ] := Bra[]

ketSplit[ Bra[a_Association] ] := 
  Times @@ Map[ Bra @* Association, Normal @ a ] /;
  Length[a] > 0

ketSplit[expr_] := KetRegulate[expr] /. {
  v_Ket :> ketSplit[v],
  v_Bra :> ketSplit[v]
 }

(**** </KetFactor> ****)


ReleaseTimes::usage = "ReleaseTimes[expr] replace OTimes and OSlash with CirlceTimes (\[CircleTimes]) to recover the standard expression."

ReleaseTimes[expr_] := KetRegulate[
  expr /. {OTimes -> CircleTimes, OSlash -> CircleTimes}
 ]


(**** <OTimes> ****)

OTimes::usage = "OTimes represents CircleTimes, but holds the arguments. Note that both OTimes and OSlash, two variants of CircleTimes, are intended for state vectors (but not gate operators)."
(* It is used, e.g., for KetFactor[]. *)

Format @ HoldPattern @ OTimes[a__] :=
  Interpretation[HoldForm @ CircleTimes @ a, OTimes @ a]

OTimes[a_] := a

OTimes[pre___, z_?CommutativeQ, post___] := z OTimes[pre, post]

OTimes[pre___, vv:Repeated[_Ket, {2, Infinity}], post___] :=
  OTimes[pre, CircleTimes[vv], post]

OTimes /:
Dagger[expr_OTimes] := Map[Dagger, expr]

(**** </OTimes> ****)


(**** <OSlash> ****)

OSlash::usage = "OSlash represents a special form of CircleTimes. It is useful, for example, to find the results of Measure[...] and to find the reduced Ket expressions. Note that both OTimes and OSlash, two variants of CircleTimes, are intended for state vectors (but not gate operators)."

Format @ HoldPattern @ OSlash[a:(_Ket|_Bra), b:Times[__]] :=
  Interpretation[
    CircleTimes[HoldForm @ a, Row @ {"(",b,")"}],
    OSlash[a, b]
   ]

Format @ OSlash[a:(_Ket|_Bra), b_] := Interpretation[
  CircleTimes[HoldForm @ a, HoldForm @ b],
  OSlash[a, b]
 ]

OSlash /: Times[z_, OSlash[a_Ket, b_]] := OSlash[a, Garner[z*b]]

OSlash /: OSlash[a_Ket, b_] + OSlash[a_Ket, c_] :=
  OSlash[a, b + c]

OSlash /: Dagger[expr_OSlash] := Map[Dagger, expr]

OSlash[any_] = any

OSlash[z_?CommutativeQ, rest__] := z * OSlash[rest]

OSlash[v_Ket, z_?CommutativeQ] := z * v

HoldPattern @ OSlash[vec_, OTimes[ff__]] := OTimes[vec, ff]

HoldPattern @ OSlash[vec_, z_?CommutativeQ OTimes[ff__]] :=
  z OTimes @@ Sort @ {vec, ff}
(* NOTE: This form occurs in KetFactor. *)


AddGarnerPatterns[_Pauli, _Dyad, _Ket, _Bra, _OTimes, _OSlash]

AddElaborationPatterns[_Pauli, _Dyad]

(**** </OSlash> ****)


(**** <Multiply> ****)

HoldPattern @ Multiply[ pre___,
  a:Ket[_Association], bb:Ket[_Association]..,
  Shortest[post___] ] :=
  Multiply[pre, CircleTimes[a, bb], post]

HoldPattern @ Multiply[ pre___,
  a:Bra[_Association], bb:Bra[_Association]..,
  Shortest[post___] ] :=
  Multiply[pre, CircleTimes[a, bb], post]

(*
HoldPattern @ Multiply[ pre___,
  Ket[a_Association], Bra[b_Association], post___] :=
  Multiply[pre, Dyad[a, b], post]
 *)
(* EXPERIMENTAL since v5.66 *)
(* NOTE (v5.85): This must come at the final stage and is moved to
   Einstein.wl. Otherwise, for example, Dagger[a[1]] ** Ket[] ** Bra[] ** a[1]
   results in Dagger[a[1]] ** Dyad[<||>,<|a[1]->1|>]. *)

HoldPattern @
  Multiply[ pre___, Bra[a_Association], Ket[b_Association], post___ ] :=
  BraKet[a, b] * Multiply[pre, post]

HoldPattern @
  Multiply[ pre___, Bra[a___], Ket[b___], post___ ] :=
  BraKet[{a}, {b}] * Multiply[pre, post]
(* Recall that Multiply has no Flat attribute. *)

HoldPattern @
  Multiply[Bra[u___], op__, Ket[v___], post__] :=
  Multiply[Bra[u], op, Ket[v]] Multiply[post]

HoldPattern @
  Multiply[pre__, Bra[u___], op__, Ket[v___], post___] :=
  Multiply[Bra[u], op, Ket[v]] Multiply[pre, post]
(* NOTE: Do not try to combine the above two definitions into one by using
   pre___ and post___. It will result in infinite loop. *)


Multiply /:
HoldPattern @ ComplexQ[ Multiply[Bra[___], ___, Ket[___]] ] = True
(* NOTE: Hence partial trace, for example, is not allowed. *)

Multiply /:
HoldPattern @ Conjugate[ Multiply[Bra[a___], op___, Ket[b___]] ] :=
  Multiply[Bra[b], Dagger @ Multiply[op], Ket[a]]

(**** </Multiply> ****)


(**** <MultiplyPower> ****)

HoldPattern @ MultiplyPower[expr_, n_] :=
  ExpressionFor @ MatrixPower[Matrix @ expr, n] /;
  Agents[expr] == {} /;
  Not @ FreeQ[expr, _Pauli]

HoldPattern @ MultiplyPower[op_, n_] := Module[
  { ss = Agents[op],
    mat },
  mat = MatrixPower[Matrix[op, ss], n]; 
  ExpressionFor[mat, ss]
 ]

(**** </MultiplyPower> ****)


State::usage = "State[{0, \[Theta], \[Phi]}] and Ket[{1, \[Theta], \[Phi]}] returns the eigenvectors of Pauli[3] in the (\[Theta], \[Phi])-rotated frame.\nState[{s$1, \[Theta]$1, \[Phi]$1}, {s$2, \[Theta]$2, \[Phi]$2}, ...] returns the tensor product State[{s$1, \[Theta]$1, \[Phi]$1}]\[CircleTimes] State[{s$2, \[Theta]$2, \[Phi]$2}, ...]\[CircleTimes]....\nState[{{s$1, s$2, ...}, \[Theta], \[Phi]}] = State[{s$1, \[Theta], \[Phi]}, {s$2, \[Theta], \[Phi]}, ...].\nSee also Ket, TheKet, TheState, Pauli, ThePauli, Operator, TheOperator."

State[ { (0|Up), theta:Except[_List], phi:Except[_List] } ] :=
  Exp[-I*phi/2]Cos[theta/2] * Ket[0] +
  Exp[+I*phi/2]Sin[theta/2] * Ket[1]

State[ { (1|Down), theta:Except[_List], phi:Except[_List] } ] :=
  -Exp[-I*phi/2]Sin[theta/2] * Ket[0] +
  +Exp[+I*phi/2]Cos[theta/2] * Ket[1]

State[ a:{ (0|1|Up|Down), Except[_List], Except[_List] }.. ] :=
  CircleTimes @@ Map[State,{a}]

State[ { m:{(0|1|Up|Down)..}, t:Except[_List], p:Except[_List] } ] :=
  CircleTimes @@ Map[State] @ Tuples[{m,{t},{p}}]


(**** <BraKet> ****)

BraKet::usage = "BraKet[{a}, {b}] represents the Hermitian product \[LeftAngleBracket]a|b\[RightAngleBracket] of the two states Ket[a] and Ket[b]."

SetAttributes[BraKet, NHoldAll]
(* The integers in BraKet[] should not be converted to real numbers by N[]. *)

Format @ BraKet[{}, b_List] :=
  Interpretation[BraKet[{Any}, b], BraKet[{}, b]]

Format @ BraKet[a_List, {}] :=
  Interpretation[BraKet[a, {Any}], BraKet[a, {}]]

Format @ BraKet[a:Except[_List|_Association], b:Except[_List|_Association]] :=
  Interpretation[BraKet[{a}, {b}], BraKet[a, b]]

BraKet /: ComplexQ[ BraKet[_List, _List] ] = True

BraKet /: Conjugate[ BraKet[a_List, b_List] ] := BraKet[b, a]

Dot[Bra[a___], Ket[b___]] := BraKet[{a}, {b}]
(* RECALL: Dot has Flat attribute. *)

(* General evaluation rules *)

(* for YoungRegularBasis, YoungFourierBasis, etc. *)
BraKet[{a_Cycles}, {b_Cycles}] := KroneckerDelta[First @ a, First @ b]

BraKet[a_List, b_List] := KroneckerDelta[a, b]

BraKet[a_Association, b_Association] := With[
  { qq = Union[Keys @ a, Keys @ b] },
  KroneckerDelta[ Lookup[a, qq], Lookup[b, qq] ]
 ]

(**** </BraKet> ****)

RaiseLower::usage = "RaiseLower[expr] converts expr by rewriting Pauli or Spin X and Y operators in terms of the raising and lowering operators."

RaiseLower[expr_] := Garner[expr //. $RaiseLowerRules]

$RaiseLowerRules = {
  Pauli[a___, 1, b___] :> (Pauli[a, 4, b] + Pauli[a, 5, b]),
  Pauli[a___, 2, b___] :> (Pauli[a, 4, b] - Pauli[a, 5, b]) / I
 }


Raise::usage = "Raise represents the raising operator."

SetAttributes[Raise, Listable]

Lower::usage = "Lower represents the lowering operator."

SetAttributes[Lower, Listable]

Hadamard::usage = "Hadamard represents the Hadamard gate."

SetAttributes[Hadamard, Listable]

Quadrant::usage = "Quadrant represents the phase gate with phase angle 2*\[Pi]/4."

SetAttributes[Quadrant, Listable]

Octant::usage = "Octant represents the phase gate with phase angle 2*\[Pi]/8."

SetAttributes[Octant, Listable]

Hexadecant::usage = "Hexadecant represents the phase gate with phase angle 2*\[Pi]/16."

SetAttributes[Hexadecant, Listable]


Pauli::usage = "Pauli[n] represents the Pauli operator (n=1,2,3). Pauli[0] represents the 2x2 identity operator, Pauli[4] the Pauli raising operator, Pauli[5] the Pauli lowering operator, and Pauli[6] the Hadamard operator.\nPauli[10] returns (Pauli[0]+Pauli[1])/2, the Projection to Ket[0].\nPauli[11] returns (Pauli[0]-Paui[1])/2, the projection to Ket[1].\nPauli[n1, n2, ...] represents the tensor product of the Pauli operators Pauil[n1], Pauli[n2], ... ."

SetAttributes[Pauli, {NHoldAll, Listable}]

Pauli /: MultiplyKind[ Pauli[___] ] = Pauli

Pauli /: MultiplyGenus[ Pauli[___] ] = "Singleton"

Pauli /: NonCommutativeQ[ Pauli[__] ] = True


Format @ Pauli[k__] := Interpretation[thePauliForm @ Pauli[k], Pauli[k]]


Raise[0] = Lower[0] = Hadamard[0] = Pauli[0]

Raise[1] = Lower[-1] = Pauli[Raise]

Lower[1] = Raise[-1] = Pauli[Lower]

Hadamard[1] = Hadamard[-1] = Pauli[Hadamard]


Pauli[1 -> 0] = Pauli[4]

Pauli[0 -> 1] = Pauli[5]

Pauli[0 -> 0] = Pauli[10]

Pauli[1 -> 1] = Pauli[11]

Pauli[Raise] = (Pauli[1] + I Pauli[2]) / 2

Pauli[Lower] = (Pauli[1] - I Pauli[2]) / 2

Pauli[Hadamard] = (Pauli[1] + Pauli[3])/Sqrt[2]

Pauli[Quadrant] = Pauli[0] (1+I)/2 + Pauli[3]*(1-I)/2

Pauli[Octant] = Pauli[0] (1+Exp[I Pi/4])/2 + Pauli[3]*(1-Exp[I Pi/4])/2

Pauli[Hexadecant] = Pauli[0] (1+Exp[I Pi/8])/2 + Pauli[3]*(1-Exp[I Pi/8])/2


Pauli[-1] = Pauli[1]

Pauli[-2] = Pauli[2]

Pauli[-3] = Pauli[3]

Pauli[-4] = Pauli[5]

Pauli[-5] = Pauli[4]

Pauli[-6] = Pauli[6]


Pauli @ C[n_Integer?NonNegative] = Pauli[0]

Pauli[-C[n_Integer?NonNegative]] = Pauli[0]


Pauli[a:{(0|1)..} -> b:{(0|1)..}] := Pauli @@ Thread[a -> b]

Pauli[kk__] := Pauli @@ ReplaceAll[
  { kk },
  { All -> {1, 2, 3},
    Full -> {0, 1, 2, 3} }
 ] /; ContainsAny[{kk}, {All, Full}]

Pauli[kk__] := Garner @ Apply[CircleTimes, Pauli /@ {kk}] /;
  ContainsAny[
    { kk },
    { Raise, Lower, Hadamard, Quadrant, Octant, Hexadecant }
   ]

(* Elaboration rules *)

Pauli /: HoldPattern @ Elaborate[ Pauli[a_, bc__] ] :=
  Garner @ Apply[CircleTimes, Elaborate[Pauli /@ {a, bc}]]

Pauli /: HoldPattern @ Elaborate[ op:Pauli[0|1|2|3] ] := op

Pauli /: HoldPattern @ Elaborate @ Pauli[10] := (Pauli[0] + Pauli[3]) / 2

Pauli /: HoldPattern @ Elaborate @ Pauli[11] := (Pauli[0] - Pauli[3]) / 2

Pauli /: HoldPattern @ Elaborate @ Pauli[4] := Pauli[Raise]

Pauli /: HoldPattern @ Elaborate @ Pauli[5] := Pauli[Lower]

Pauli /: HoldPattern @ Elaborate @ Pauli[6] := Pauli[Hadamard]

Pauli /: HoldPattern @ Elaborate @ Pauli[7] := Pauli[Quadrant]

Pauli /: HoldPattern @ Elaborate @ Pauli[8] := Pauli[Octant]

Pauli /: HoldPattern @ Elaborate @ Pauli[9] := Pauli[Hexadecant]

Pauli /: HoldPattern @ Elaborate @ Pauli[-7] := Dagger @ Pauli[Quadrant]

Pauli /: HoldPattern @ Elaborate @ Pauli[-8] := Dagger @ Pauli[Octant]

Pauli /: HoldPattern @ Elaborate @ Pauli[-9] := Dagger @ Pauli[Hexadecant]

Pauli /: HoldPattern @ Elaborate @ Pauli @ C[n_Integer] := With[
  { f = Exp[I*2*Pi*Power[2, n]] },
  Pauli[0]*(1+f)/2 + Pauli[3]*(1-f)/2
 ]

(* Dagger *)

Pauli /: Dagger[ Pauli[m:(0|1|2|3|6)] ] := Pauli[m]

Pauli /: Dagger[ Pauli[4] ] := Pauli[5]

Pauli /: Dagger[ Pauli[5] ] := Pauli[4]

Pauli /: Dagger[ Pauli[7] ] := Pauli[-7]

Pauli /: Dagger[ Pauli[8] ] := Pauli[-8]

Pauli /: Dagger[ Pauli[9] ] := Pauli[-9]

Pauli /: Dagger[ Pauli[-7] ] := Pauli[7]

Pauli /: Dagger[ Pauli[-8] ] := Pauli[8]

Pauli /: Dagger[ Pauli[-9] ] := Pauli[9]

Pauli /: Dagger @ Pauli @ C[n_Integer] := Pauli[-C[n]]

Pauli /: Dagger @ Pauli[-C[n_Integer]] := Pauli[C @ n]

Pauli /: Dagger @ Pauli[a_, bc__] :=
  Garner @ Apply[CircleTimes, Dagger /@ Pauli /@ {a, bc}]

(* Conjugate *)

Pauli /: Conjugate[ Pauli[2] ] = -Pauli[2]

Pauli /: Conjugate[ Pauli[7] ] := Pauli[-7]

Pauli /: Conjugate[ Pauli[8] ] := Pauli[-8]

Pauli /: Conjugate[ Pauli[9] ] := Pauli[-9]

Pauli /: Conjugate[ Pauli[-7] ] := Pauli[7]

Pauli /: Conjugate[ Pauli[-8] ] := Pauli[8]

Pauli /: Conjugate[ Pauli[-9] ] := Pauli[9]

Pauli /: Conjugate[ Pauli[m:(0|1|3|4|5|6)] ] := Pauli[m]

Pauli /: Conjugate[ Pauli[a_, bc__] ] := CircleTimes @@ Map[
  Conjugate @* Pauli, {a, bc}
 ]

  
Pauli /:
CircleTimes[a_Pauli, bc__Pauli] := Pauli @@ Catenate[List @@@ {a, bc}]


(**** <Pauli in Multiply> ****)

HoldPattern @ Multiply[pre___, op__Pauli, vec:Ket[(0|1)..], post___] :=
  Multiply[pre, Dot[op, vec], post]

HoldPattern @ Multiply[pre___, op_Pauli, more__Pauli, Shortest[post___]] :=
  Multiply[pre, Dot[op, more], post]

(**** </Pauli in Multiply> ****)


Operator::usage = "Operator[{k, th, ph}] returns the Pauli matrix in the rotated frame.\nOperator[{{k1,k2,...}, th, ph}] = Operator[{k1, th, ph}, {k2, th, ph}, ...]."

Operator[{0, theta_, phi_}] := Pauli[0]

Operator[{n:(1|2|3), theta_, phi_}] := Garner @
  { Pauli[1], Pauli[2], Pauli[3] } . EulerMatrix[{phi,theta,0}][[;;,n]]

Operator[{4|Raise, th_, ph_}] := ( Operator[{1,th,ph}] + I Operator[{2,th,ph}] ) / 2

Operator[{5|Lower, th_, ph_}] := ( Operator[{1,th,ph}] - I Operator[{2,th,ph}] ) / 2

Operator[{6|Hadamard, th_, ph_}] := ( Operator[{1,th,ph}] + Operator[{3,th,ph}] ) / Sqrt[2]

(* Short-hand interface for multi-spin system *)

Operator[ kk:{(0|1|2|3|4|5|6), _, _} .. ] := Garner[
  CircleTimes @@ Map[Operator] @ {kk}
 ]

Operator[ { kk:{(0|1|2|3|4|5|6|7|8)..},
    th:Except[_List], ph:Except[_List] } ] := 
  CircleTimes @@ Map[Operator] @ Tuples[{kk, {th}, {ph}}]
(* These are first expanded because they are not elementry. *)


(**** <ExpressionFor> ****)

ExpressionFor::usage = "ExpressionFor[mat] returns the operator expression corresponding to the matrix representation mat.\nExpressionFor[mat, {s1, s2, ...}] returns the operator expression corresponding to the matrix representation mat and acting on the systems in {s1, s2, ...}."

ExpressionFor::notls = "The matrix/vector `` is not representing an operator/state on a system of qubits."

ExpressionFor::incmpt = "The matrix/vector `` is not representing an operator/state on the systems ``."

(* Column vector to state vector *)

ExpressionFor[vec_?VectorQ] := Module[
  { n = Log[2, Length @ vec],
    bits, vals },
  If[ Not @ IntegerQ[n],
    Message[ExpressionFor::notls, vec];
    Return[Ket[0]]
   ];
  bits = Flatten @ Keys @ Most @ ArrayRules @ vec;
  vals = vec[[bits]];
  bits = Ket @@@ IntegerDigits[bits-1, 2, n];
  KetChop @ Garner @ Dot[vals, bits]
 ]


(* Matrix to operator for unlabeled qubits *)

ExpressionFor[mat_?MatrixQ] := Module[
  { n = Log[2, Length @ mat],
    tt, pp },
  n = Log[2, Length @ mat];
  If[ IntegerQ[n], Null,
    Message[ExpressionFor::notls, mat];
    Return[0];
   ];
  
  pp = Table[
    { {Pauli[0]/2 + Pauli[3]/2, Pauli[4]},
      {Pauli[5], Pauli[0]/2 - Pauli[3]/2} },
    { n }
   ];
  (* NOTE: This makes ExpressionFor to generate an operator expression in
     terms of the Pauli raising and lowering operators instead of the Pauli X
     and Y operators. Many evaluations are faster with the raising and
     lowering operators rather than X and Y operators. When an expression in
     terms of the X and Y operators are necessary, one can use Elaborate. *)

  pp = Outer[CircleTimes, Sequence @@ pp];

  tt = Tensorize[mat]; (* It must be Tensorize, not ArrayReshape. *)
  Garner @ Total @ Flatten[tt * pp]
 ]

ExpressionFor[expr:(_?VectorQ|_?MatrixQ), {}] := ExpressionFor[expr]


(* Column vector to state vector for labeled systems *)

ExpressionFor[vec_?VectorQ, S_?SpeciesQ] :=
  ExpressionFor[vec, {S}]

ExpressionFor[vec_?VectorQ, ss:{__?SpeciesQ}] := Module[
  { nL = Times @@ Dimension @ ss,
    bs = Basis @ ss },
  
  If[ nL == Length[vec], Null,
    Message[ExpressionFor::incmpt, vec, FlavorNone @ ss];
    Return[0];
   ];
  
  KetChop @ Garner[vec . bs]
 ]

(* Matrix to operator for labeled systems *)

ExpressionFor[mat_?MatrixQ, S_?SpeciesQ] :=
  ExpressionFor[mat, {S}]

ExpressionFor[mat_?MatrixQ, ss:{__?SpeciesQ}] := Module[
  { dd = Dimension @ ss,
    ff = Fermions @ ss,
    rr, qq, S, tsr, ops },
  If[ Times @@ dd == Length[mat], Null,
    Message[ExpressionFor::incmpt, mat, FlavorNone @ ss];
    Return[0]
   ];

  Let[Qubit, S];
  qq = S[Range @ Length @ ff, $];
  rr = ss /. Thread[ff -> qq];
  
  tsr = Tensorize[mat, Flatten @ Transpose @ {dd, dd}];
  ops = Outer[Multiply, Sequence @@ TheExpression /@ rr];
  ops = Garner @ Total @ Flatten[tsr * ops];
  JordanWignerTransform[ops, qq -> ff]
 ]


TheExpression::usage = "TheExpression[spc] returns the matrix of operators required to construct the operator expresion from the matrix representation involving the species spc.\nIt is a low-level function to be used internally.\nSee also TheMatrix, which serves similar purposes."

TheExpression[S_] := Table[
  S[j -> i],
  {i, LogicalValues @ S},
  {j, LogicalValues @ S}
 ]
(* NOTE: This method is also used for Elaborate[Dyad[...]]. However, to
   optimize ExpressionFor independently of Dyad, TheExpression can be
   redefined for specific Species S. *)

(**** </ExpressionFor> ****)


(**** <ExpressionIn> ****)

ExpressionIn::usage = "ExpressionIn[mat, bs] returns the operator that is reperesented by matrix mat in basis bs.\nExpressionIn[mat,aa,bb] returns the operator that is represented by matrix mat in bases aa and bb for the rows and columns, respectively.\nExpressionIn[vec,bs] is equivalent to Dot[bs,vec]."

ExpressionIn::vector = "Vector `` incompatible with basis ``."

ExpressionIn::matrix = "Matrix `` incompatible with basis `` and/or ``."

SyntaxInformation[ExpressionIn] = {"ArgumentsPattern" -> {_, __}}

ExpressionIn[vec_?VectorQ, bs_List] := bs . vec /; Length[bs] == Length[vec]

ExpressionIn[vec_?VectorQ, bs_List] :=
  (Message[ExpressionIn::vector, vec, bs]; First @ bs)


ExpressionIn[mat_?MatrixQ, bs_List] := ExpressionIn[mat, bs, bs]

ExpressionIn[mat_?MatrixQ, aa_List, bb_List] := Module[
  { spc = Agents @ Join[aa, bb],
    obs },
  obs = Dyad[#1, #2, spc]& @@@ Tuples[{aa, bb}];
  obs . Flatten[mat]
 ] /; And @ Thread[Dimensions[mat] == {Length @ aa, Length @ bb}]

ExpressionIn[mat_?VectorQ, aa_List, bb_List] :=
  (Message[ExpressionIn::matrix, mat, aa, bb]; 0)


ExpressionIn[mat_Association, bs_Association] := Module[
  { kk = Keys @ mat,
    bb, mm },
  bb = KeyTake[bs, kk];
  Garner @ Total @ MapThread[ExpressionIn, {mat, bs}]
 ] /; ContainsAll[Keys @ bs, Keys @ mat]

ExpressionIn[mat:Association[(_->_?MatrixQ)..],
  aa_Association, bb_Association] := Garner @ Total[
    KeyValueMap[ExpressionIn[#2, aa[First @ #1], bb[Last @ #1]]&, mat]
   ] /; And[
     ContainsOnly[Length /@ Keys[mat], {2}],
     ContainsAll[Keys @ aa, First /@ Keys[mat]],
     ContainsAll[Keys @ bb, Last /@ Keys[mat]]
    ]

(**** </ExpressionIn> ****)


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


BlochVector::usage = "BlochSphere[{c0, c1}] returns the point on the Bloch sphere corresponding to the pure state Ket[0]*c0 + Ket[1]*c1.\nBlochVector[\[Rho]] returns the point in the Bloch sphere corresponding to the mixed state \[Rho]."

BlochVector[rho_?MatrixQ] := Simplify[2 * PauliVector[rho]] /;
  Dimensions[rho] == {2, 2}

BlochVector[cc_?VectorQ] := Module[
  { dd = Normalize[cc] },
  Simplify @ {
    Conjugate[dd] . ThePauli[1] . dd,
    Conjugate[dd] . ThePauli[2] . dd,
    Conjugate[dd] . ThePauli[3] . dd
   }
 ] /; Length[cc] == 2


BlochVector[Ket[]] := BlochVector @ {1, 0}

BlochVector[_?CommutativeQ Ket[]] := BlochVector @ {1, 0}

BlochVector[expr_, q_?SpeciesQ] := Module[
  { ss = Agents[expr] },
  If[ Length[ss] > 1,
    BlochVector @ ReducedMatrix[expr, FlavorNone @ {q}],
    BlochVector @ Matrix[expr, FlavorNone @ {q}]
   ]
 ]

BlochVector[expr_] := {0, 0, 0} /;
  FreeQ[expr, _Pauli | _Ket | _?NonCommutativeQ]

BlochVector[expr_] := BlochVector[expr, 1] /;
  Not @ FreeQ[expr, _Pauli | _Ket | _?NonCommutativeQ]

BlochVector[expr_, j_Integer] := Module[
  { mat = Matrix[expr],
    n },
  n = Log[2, Length @ mat];
  If[ n > 1,
    BlochVector @ ReducedMatrix[mat, {j}],
    BlochVector @ mat
   ]
 ] /; Not @ FreeQ[expr, _Pauli | _Ket | _?NonCommutativeQ]


BlochSphere::usage = "BlochSphere[primitives, options] returns Graphics3D containing the Bloch sphere as well as primitives.\nIt accepts all Graphics3D primitives and, in addition, BlochPoint.\nBlochSphere[options] just displays the Bloch sphere."

Options[BlochSphere] = {
  "Opacity" -> 0.8,
  "PointSize" -> 0.03,
  SphericalRegion -> True,
  PlotRange -> 1.3,
  PlotRegion -> {{-0.5, 1.5}, {-0.5, 1.5}},
  ViewVertical -> {0, 0, 1},
  ImageSize -> 400,
  Ticks -> None,
  Axes -> False,
  Boxed -> False
 }

BlochSphere[opts___?OptionQ] := BlochSphere[Nothing, opts]
  
BlochSphere[primitives_, opts___?OptionQ] := Block[ (* Block NOT Module *)
  { BlochPoint, rr },
  rr = "PointSize" /. {opts} /. Options[BlochSphere];
  
  BlochPoint[pnt_, r_:rr] := Sphere[pnt, r];
  
  Graphics3D[
    { theBlochSphere[opts], primitives },
    Sequence @@ FilterRules[
      Join[{opts}, Options @ BlochSphere],
      Options @ Graphics3D
     ]
   ]
 ]

theBlochSphere[opts___?OptionQ] := Module[
  { dd },
  dd = "Opacity" /. {opts} /. Options[BlochSphere];
  { { Opacity[dd], Cyan, Sphere[] },
    { Thick, GrayLevel[0.4],
      Line @ {
        1.1 {{-1,0,0}, {1,0,0}},
        1.1 {{0,-1,0}, {0,1,0}},
        1.1 {{0,0,-1}, {0,0,1}}
       },
      Line @ {
        Table[{0, Cos[t Pi], Sin[t Pi]}, {t, 0, 2, 0.01}],
        Table[{Cos[t Pi], 0, Sin[t Pi]}, {t, 0, 2, 0.01}],
        Table[{Cos[t Pi], Sin[t Pi], 0}, {t, 0, 2, 0.01}] }
     }
   }
 ]


(**** <Basis> ****)

Basis::usage = "Basis[n] constructs the standard tensor-product basis of a system of n unlabelled qubits.\nBasis[{dim1, dim2, ..., dimn}] constructs the standard tensor-product basis of a total of n unlabelled systems with the Hilbert space dimensions dim1, dim2, ..., respectively.\nBasis[q1, q2, ...] constructs the tensor product basis for the system consising of Species q1, q2, ...\nBasis[q1, {q2, q3}, ...] is equivalent to Basis[q1, q2, q3, ...].\nBasis[expr] finds the relevant systems from the expression expr and constructs the basis."

Basis[n_Integer] := Ket @@@ Tuples[{0, 1}, n]

Basis[dim:{__Integer}] := Ket @@@ Tuples[Range[0,#-1]& /@ dim]


Basis[] := { Ket @ Association[] } (* fallback *)

Basis[a_?SpeciesQ, b__?SpeciesQ] := Basis @ {a, b}

Basis[ss:{__?SpeciesQ}] := CircleTimes @@@ Tuples[Basis /@ ss]

Basis[
  a:Alternatives[_?SpeciesQ, {__?SpeciesQ}],
  b:Alternatives[_?SpeciesQ, {__?SpeciesQ}].. ] :=
  Basis @ Flatten @ {a, b}


Basis[ expr:Except[_?SpeciesQ] ] := Basis @@ Agents[expr] /;
  FreeQ[expr, _Pauli | Ket[(0|1)..] | Bra[(0|1)..] ]

Basis[ expr:Except[_?SpeciesQ] ] := With[
  { pp = Length /@ Cases[{expr}, _Pauli|Ket[(0|1)..]|Bra[(0|1)..], Infinity] },
  Basis @ First[pp] /; Equal @@ pp
 ]

(**** </Basis> ****)


(**** <TheMatrix> ****)

TheMatrix::usage = "TheMatrix[op] returns the matrix representation of op. Here, op is an elementary operators.\nThis function is a low-level function intended for internal use.\nSee also TheExpression, which serves for similar purposes."

HoldPattern @ TheMatrix[ Dagger[op_] ] := Topple @ TheMatrix[op]

(* For Ket/Bra of unlabelled qubits *)

TheMatrix @ Ket[args__] := TheKet[args]

TheMatrix @ Bra[args__] := TheKet[args]


TheMatrix[rr:Rule[_?SpeciesQ, _]] := TheMatrix @ Ket @ Association @ rr

TheMatrix @ Association[aa:Rule[_?SpeciesQ, _]..] := TheMatrix /@ {aa}


(* For Pauli operators of unlabelled qubits *)

TheMatrix @ Pauli[args__] := ThePauli[args]

(**** </TheMatrix> ****)


(**** <Matrix> ****)

Matrix::usage = "Matrix[expr, {a1, a2, ...}] constructs the matrix representation of the expression expr on the total system consisting of a1, a2, ....\nMatrix[expr] feagures out the subsystems involved in expr."

Matrix::rmndr = "There remain some elements, ``, that are not specified for matrix representation."

(* General Code *)

Matrix[ expr_ ] := Matrix[expr, Agents @ expr]

Matrix[ expr_, S_?SpeciesQ ] := Matrix[expr, S @ {$}]

Matrix[ expr_, S_?SpeciesQ, tt_ ] := Matrix[expr, S @ {$}, tt]

Matrix[ expr_, ss_, T_?SpeciesQ ] := Matrix[expr, ss, T @ {$}]

Matrix[ expr_, ss:{__?SpeciesQ} ] := Matrix[expr, FlavorNone @ ss] /;
  Not[FlavorNoneQ @ ss]

Matrix[ expr_, ss:{__?SpeciesQ}, tt:{__?SpeciesQ} ] :=
  Matrix[expr, FlavorNone @ ss, FlavorNone @ tt] /;
  Not[FlavorNoneQ @ {ss, tt}]

Matrix[ expr_Plus, qq:{___?SpeciesQ}.. ] :=
  TrigToExp @ ExpToTrig @ Map[Matrix[#, qq]&, KetChop @ expr]
(* NOTE: TrigToExp @ ExpToTrig helps simplify in many cases. *)
(* NOTE: KetChop is required here because "0. + Ket[...]" may happen. *)

Matrix[ z_?CommutativeQ op_, qq:{___?SpeciesQ}.. ] := z * Matrix[op, qq]

Matrix[ z_?CommutativeQ, {} ] := z * One[2]

Matrix[ z_?CommutativeQ, qq:{__?SpeciesQ} ] :=
  z * One[Times @@ Dimension @ qq]

Matrix[ z_?CommutativeQ, ss:{__?SpeciesQ}, tt:{__?SpeciesQ} ] :=
  z * One[Times @@ Dimension @ ss, Times @@ Dimension @ tt]

(* Dagger *)

HoldPattern @ Matrix[ Dagger[a_?NonCommutativeQ] ] := Topple @ Matrix[a]
(* NOTE: Matrix[a] may still include some operators; and hence Topple instead
   of ConjugateTranspose. *)


(* Arrays *)

HoldPattern @
  Matrix[expr:(_List|_Association), {}] := Module[
    { dim, mat },
    dim = Power[2, FirstCase[expr, op_Pauli :> Length[op], 0, Infinity]];
    mat = Zero @ {dim, dim};
    Replace[
      expr,
      {0 -> mat, else_ :> Matrix[else]},
      {1}
     ]
   ] /; And[Not @ FreeQ[expr, _Pauli], MemberQ[expr, 0]]

HoldPattern @
  Matrix[expr_Association, ss:{___?SpeciesQ}..] := Map[Matrix[#, ss]&, expr]

HoldPattern @
  Matrix[expr_List, ss:{___?SpeciesQ}..] := Map[Matrix[#, ss]&, expr]
(* NOTE: {SparseArray[...], SparseArray[...], ...} may not take full advantage
   of sparse array, and we may add SparseArray at the end. But I decided not
   to do it as one usually expect {...} as the output. One should handle the
   output as he prefers. *)


(* For Ket/Bra of unlabelled qubits *)

Matrix[ vec:Ket[__], {___} ] := TheMatrix[vec]

Matrix[ vec:Bra[__], {___} ] := TheMatrix[vec]


(* For Ket/Bra of labelled qubits *)

Matrix[Ket[<||>], {}] := 0

Matrix[Ket[a_Association], ss:{__?SpeciesQ}] :=
  CircleTimes @@ Map[TheMatrix, Thread[ss -> Lookup[a, ss]]]

Matrix[Ket[Vacuum], ss:{__?SpeciesQ}] := Matrix[Ket[<||>], ss]

Matrix[Bra[<||>], {}] := 0

Matrix[Bra[a_Association]] := Matrix[Bra[a], Keys @ a] /; Length[a] > 1

Matrix[Bra[v_Association], ss:{__?SpeciesQ}] :=
  Conjugate @ Matrix[Ket[v], ss]

Matrix[Bra[Vacuum], ss:{__?SpeciesQ}] := Matrix[Bra[<||>], ss]

(* For Pauli[...] *)

Matrix[ op:Pauli[__], {___} ] := TheMatrix[op]


(* For Fermions *)

Matrix[op_?AnyFermionQ, qq:{__?SpeciesQ}] := Module[
  { mm = TheMatrix @ op,
    sp = FlavorMute @ Peel @ op,
    id, rr, ss },
  id = First @ FirstPosition[qq, sp];
  rr = qq[[ ;; id - 1]];
  ss = qq[[id + 1 ;; ]];

  rr = fermionOne /@ rr;
  ss = One /@ Dimension[ss];
  CircleTimes @@ Join[rr, {mm}, ss]
 ] /; MemberQ[FlavorNone @ qq, FlavorMute @ Peel @ op]

fermionOne[f_?FermionQ] := ThePauli[3]

fermionOne[s_] := One[Dimension @ s]


(* For Species *)

Matrix[op_?AnySpeciesQ, ss:{__?SpeciesQ}] := Module[
  { mm = TheMatrix @ op,
    sp = FlavorMute @ Peel @ op,
    rr },
  rr = One /@ Dimension[ss];
  rr = Association @ Join[ Thread[ss -> rr], {sp -> mm} ];
  CircleTimes @@ rr
 ] /; MemberQ[ss, FlavorMute @ Peel @ op]

Matrix[op_?AnySpeciesQ, qq:{__?SpeciesQ}] := (
  Message[Matrix::rmndr, op];
  op * Matrix[1, qq]
 )


(* For Dyad-like (but not Dyad) expression *)
Matrix[
  HoldPattern @ Multiply[pre___, ket_Ket, bra_Bra, post___],
  qq:{___?SpeciesQ}
 ] := Dyad[
   Matrix[pre ** ket, qq],
   Dagger @ Matrix[bra ** post, qq]
  ]
(* NOTE: Dagger (not Conjugate) here. *)

(* For MultiplyExp *)
HoldPattern @ Matrix[ MultiplyExp[op_], qq:{__?SpeciesQ} ] :=
  MatrixExp @ Matrix @ op

(* For Multiply[...] *)
Matrix[HoldPattern @ Multiply[ops__], qq:{___?SpeciesQ}] :=
  Dot @@ Map[Matrix[#, qq]&, {ops}]

(**** </Matrix> ****)


(**** <MatrixIn> ****)

MatrixIn::ussage = "MatrixIn[op, bs] returns the matrix representation of operator op in basis bs. The basis bs may be a list of kets or an association of such lists.\nMatrixIn[bs] provides the operator form of MatrixIn."

MatrixIn::nullv = "`` includes the null vector (0 or 0.)."

MatrixIn::notbs = "`` does not look like a valid basis."

SyntaxInformation[MatrixIn] = {
  "ArgumentsPattern" -> {_, __}
 }

MatrixIn[op_, bs_List] := (
  Message[MatrixIn::nullv, bs];
  Garner @ Outer[Multiply, Dagger[bs], Garner[op ** bs]]
 ) /; ContainsAny[bs, {0, 0.}]
(* NOTE: This may happen numerically or in a illdefined basis. *)

MatrixIn[op_, bs_List] := (
  Message[MatrixIn::notbs, bs];
  Zero[Length @ bs, Length @ bs]
 ) /; AnyTrue[bs, FreeQ[#, _Ket]&]

MatrixIn[expr:(_List|_Association), spec:(__List|__Association)] :=
  Map[MatrixIn[#, spec]&, expr]

(* MatrixIn[bs:(_List|_Association)][op_] := MatrixIn[op, bs] *)
(* NOTE; Dangerous? *)

MatrixIn[vec_, bs_List] := SparseArray @ Multiply[Dagger[bs], vec] /;
  And[
    Not @ FreeQ[vec, Ket[_Association]],
    FreeQ[vec, _Multiply] (* Ket[...] ** Bra[...] *)
   ]

MatrixIn[bra_, bs_List] := SparseArray @ Multiply[bra, bs] /;
  And[
    Not @ FreeQ[bra, Bra[_Association]],
    FreeQ[bra, _Multiply] (* Ket[...] ** Bra[...] *)
   ]

MatrixIn[op_, bs_List] :=
  SparseArray @ Outer[Multiply, Dagger[bs], Garner[op ** bs]]

MatrixIn[op_, aa_List, bb_List] :=
  SparseArray @ Outer[Multiply, Dagger[aa], Garner[op ** bb]]

MatrixIn[op_, bs_Association] := Map[MatrixIn[op, #]&, bs]

MatrixIn[op_, aa_Association, bb_Association] := Module[
  { kk = Tuples @ {Keys @ aa, Keys @ bb},
    mat },
  mat = Outer[MatrixIn[op, #1, #2]&, Values @ aa, Values @ bb, 1];
  AssociationThread[kk -> Flatten[mat,1] ]
 ]

(**** </MatrixIn> ****)


ProperSystem::usage = "ProperSystem[expr] returns a list of {values, vectors} of the eigenvalues and eigenstates of expr.\nProperSystsem[expr, {s1, s2, ...}] regards expr acting on the system consisting of the Species {s1, s2, ...}.\nThe operator expression may be in terms of either (but not both) Pauli[...] for unlabelled qubits or other labelled operators on Species."

ProperSystem::mixed = "The operator `` contains the Pauli operators of unlabelled qubits as well as other labelled operators for Species."

ProperSystem::incon = "Inconsistent Pauli operators in ``."

ProperSystem::eigsysno = "Could not get the eigenvalues and eigenvectors of ``."

ProperSystem[expr_] := Module[
  { ss = Agents[expr],
    pp = Cases[{expr}, _Pauli, Infinity],
    nn, mat, res, val, vec },

  If[ ss == {}, Null,
    Messsage[ProperSystem::mixed, expr];
    Return[$Failed]
   ];

  nn = Length /@ pp;
  If[ Equal @@ nn,
    nn = First[nn],
    Message[ProperSystem::incon, expr];
    Return[$Failed]
   ];
  
  mat = Matrix[expr];
  res = Eigensystem[mat];
  If[ ListQ @ res,
    val = First[res];
    vec = Last[res] . Basis[nn],
    Message[ProperSystem::eigsysno, expr];
    Return[$Failed]
   ];
  
  {val, vec}
 ] /; Not @ FreeQ[expr, _Pauli]


ProperSystem[expr_] := ProperSystem[expr, {}] /; FreeQ[expr, _Pauli]

ProperSystem[expr_, qq:{___?SpeciesQ}] := Module[
  { ss = Agents[expr],
    rr, mat, res, val, vec },

  mat = Matrix[expr, ss];
  res = Eigensystem[mat];
  If[ ListQ @ res,
    val = First[res];
    vec = Last[res] . Basis[ss],
    Message[ProperSystem::eigsysno, expr];
    Return[$Failed]
   ];
  
  rr = Complement[FlavorNone @ qq, ss];
  If[ rr == {}, Null,
    val = Flatten @ Transpose @ ConstantArray[val, Times @@ Dimension[rr]];
    vec = Flatten @ Outer[CircleTimes, vec, Basis[rr]]
   ];
  {val, vec}
 ]


ProperStates::usage = "ProperStates[expr] returns a list of the eigenstates of expr.\nProperSystsem[expr, {s1, s2, ...}] regards expr acting on the system consisting of the Species {s1, s2, ...}.\nThe operator expression may be in terms of either (but not both) Pauli[...] for unlabelled qubits or other labelled operators on Species."

ProperStates::mixed = "The operator `` contains the Pauli operators of unlabelled qubits as well as other labelled operators for Species."

ProperStates::incon = "Inconsistent Pauli operators in ``."

ProperStates::eigsysno = "Could not get the eigenvalues and eigenvectors of ``."

ProperStates[expr_] := Module[
  { ss = Agents[expr],
    pp = Cases[{expr}, _Pauli, Infinity],
    nn, mat, vec },

  If[ ss == {}, Null,
    Messsage[ProperStates::mixed, expr];
    Return[$Failed]
   ];

  nn = Length /@ pp;
  If[ Equal @@ nn,
    nn = First[nn],
    Message[ProperStates::incon, expr];
    Return[$Failed]
   ];
  
  mat = Matrix[expr];
  vec = Eigenvectors[mat];
  If[ ListQ @ vec,
    Return[vec . Basis[nn]],
    Message[ProperStates::eigsysno, expr];
    Return[$Failed]
   ];
 ] /; Not @ FreeQ[expr, _Pauli]


ProperStates[expr_] := ProperStates[expr, {}] /; FreeQ[expr, _Pauli]

ProperStates[expr_, qq:{___?SpeciesQ}] := Module[
  { ss = Agents[expr],
    rr, mat, vec },
  
  mat = Matrix[expr, ss];
  vec = Eigenvectors[mat];
  If[ ListQ @ vec,
    vec = vec . Basis[ss],
    Message[ProperStates::eigsysno, expr];
    Return[$Failed]
   ];
  
  rr = Complement[FlavorNone @ qq, ss];
  If[ rr == {},
    Return @ vec,
    Return @ Flatten @ Outer[CircleTimes, vec, Basis[rr]]
   ];
 ]


ProperValues::usage = "ProperValues[expr] returns a list of the eigenvalues of expr.\nProperSystsem[expr, {s1, s2, ...}] regards expr acting on the system consisting of the Species {s1, s2, ...}.\nThe operator expression may be in terms of either (but not both) Pauli[...] for unlabelled qubits or other labelled operators on Species."

ProperValues::mixed = "The operator `` contains the Pauli operators of unlabelled qubits as well as other labelled operators for Species."

ProperValues::incon = "Inconsistent Pauli operators in ``."

ProperValues::eigsysno = "Could not get the eigenvalues and eigenvectors of ``."

ProperValues[expr_] := Module[
  { ss = Agents[expr],
    pp = Cases[{expr}, _Pauli, Infinity],
    nn, mat, val },

  If[ ss == {}, Null,
    Messsage[ProperValues::mixed, expr];
    Return[$Failed]
   ];

  nn = Length /@ pp;
  If[ Equal @@ nn,
    nn = First[nn],
    Message[ProperValues::incon, expr];
    Return[$Failed]
   ];
  
  mat = Matrix[expr];
  val = Eigenvalues[mat];
  If[ ListQ @ val,
    Return[val],
    Message[ProperValues::eigsysno, expr];
    Return[$Failed]
   ];
 ] /; Not @ FreeQ[expr, _Pauli]


ProperValues[expr_] := ProperValues[expr, {}] /; FreeQ[expr, _Pauli]

ProperValues[expr_, qq:{___?SpeciesQ}] := Module[
  { ss = Agents[expr],
    rr, mat, val },
  
  mat = Matrix[expr, ss];
  val = Eigenvalues[mat];
  If[ ListQ @ val, Null,
    Message[ProperValues::eigsysno, expr];
    Return[$Failed]
   ];
  
  rr = Complement[FlavorNone @ qq, ss];
  If[ rr == {},
    Return[val],
    Return @ Flatten @ Transpose @ ConstantArray[val, Times @@ Dimension[rr]]
   ];
 ]


(**** <CommonEigensystem> ****)

CommonEigensystem::usage = "CommonEigensystem[{m1, m2, ...}] finds the simultaneous eigenvectors and corresponding eigenvales of the mutually commuting square matrices."

CommonEigenvectors::usage = "CommonEigenvectors[{m1, m2, ...}] finds the simultaneous eigenvectors of the mutually commuting square matrices."

CommonEigenvalues::usage = "CommonEigenvalues[{m1, m2, ...}] finds the simultaneous eigenvalues of the mutually commuting square matrices."

CommonEigensystem[mm:{__?MatrixQ}] := Module[
  { id = IdentityMatrix[Length @ First @ mm],
    val, vec },
  { val, vec } = Transpose @ FoldPairList[blockEigensystem, {id}, mm, Identity];
  { Transpose @ val, Catenate @ Last @ vec }
 ]

CommonEigenvalues[mm:{__?MatrixQ}] := Module[
  { id = IdentityMatrix[Length @ First @ mm] },
  Transpose @ FoldPairList[blockEigensystem, {id}, mm]
 ]

CommonEigenvectors[mm:{__?MatrixQ}] := Module[
  { id = IdentityMatrix[Length @ First @ mm] },
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
  sys = Transpose @ Eigensystem[Conjugate[bs].mat.Transpose[bs]];
  {val, vec} = Transpose[GatherBy[sys, First], {2, 3, 1}];
  vec = Map[Normalize, vec, {2}] . bs;
  {val, vec}
 ]
(* The basis in bs is assumed to be orthonormal. *)

(**** </CommonEigensystem> ****)


(**** <Parity> ****)

Parity::usage = "Parity[op] represents the parity operator of the species op. For a particle (Boson or Fermion) op, it refers to the even-odd parity of the occupation number. For a Qubit, it refers to the Pauli-Z.\nParity[{a, b, ...}] representts the overall parity of species a, b, ...."

AddElaborationPatterns[_Parity]


Parity /: Peel[ Parity[a_] ] := a (* for Matrix[] *)

Parity /: MultiplyKind[ Parity[a_] ] := MultiplyKind[a] (* for Multiply[] *)

Parity /: MultiplyGenus[ Parity[_] ] := "Singleton" (* for Multiply *)

Parity /: AnySpeciesQ[ Parity[a_] ] := AnySpeciesQ[a] (* for Multiply[] *)

Parity /:
NonCommutativeQ[ Parity[a_] ] := NonCommutativeQ[a] (* for Multiply[] *)

Parity /:
Dagger[op:Parity[___]] := op

Parity[a_?SpeciesQ, b__?SpeciesQ] := Multiply @@ Parity /@ {a, b}

Parity[{op__?SpeciesQ}] := Multiply @@ Parity /@ {op}

HoldPattern @ Multiply[pre___, a_Parity, a_Parity, post___] :=
  Multiply[pre, post]

HoldPattern @ Multiply[pre___, a_Parity, b_Parity, post___] :=
  Multiply[pre, b, a, post] /; Not @ OrderedQ @ {a, b}


ParityValue::usage = "ParityValue[state, {a, b, ...}] returns the parity eigenvalue \[PlusMinus]1 if state is a parity eigenstate of species {a,b,\[Ellipsis]} and 0 otherwise.\nParityValue[{a,b,\[Ellipsis]}] represents the operator form of ParityValue."

ParityValue[ S_?SpeciesQ ][ expr_ ] := ParityValue[expr, {S}]

ParityValue[ ss:{__?SpeciesQ} ][ expr_ ] := ParityValue[expr, ss]


ParityValue[ expr_Association, ss:{__?SpeciesQ} ] :=
  Map[ ParityValue[ss], expr ]

ParityValue[ expr_List, ss:{__?SpeciesQ} ] :=
  Map[ ParityValue[ss], expr ] /;
  Not @ FreeQ[expr, _Ket]

ParityValue[ z_?CommutativeQ expr_, ss:{__?SpeciesQ} ] :=
  ParityValue[expr, ss] /;
  Not @ FreeQ[expr, _Ket]

ParityValue[ expr_Plus, ss:{__?SpeciesQ} ] := With[
  { vv = ParityValue[Cases[expr, _Ket, Infinity], ss] },
  If[Equal @@ vv, First @ vv, 0]
 ] /; Not @ FreeQ[expr, _Ket]

ParityValue[ v_Ket, ss:{__?SpeciesQ} ] :=
  Multiply @@ Map[ParityValue[v, #]&, FlavorNone @ ss]

ParityValue[ Ket[<||>], {} ] := True


ParityEvenQ::usage = "ParityEvenQ[state_, {a, b, ...}] returns True if state (in a Ket expression) has a definite Even parity with respect to the systems a, b, .... Otherwise, False is returned.\nParityEvenQ[state] first finds all systems involved and tests the parity."

ParityOddQ::usage = "ParityOddQ[state_, {a, b, ...}] returns True if state (in a Ket expression) has a definite Odd parity. Otherwise, False is returned.ParityOddQ[state] first finds all systems involved and tests the parity."

ParityEvenQ[ S_?SpeciesQ ][ expr_ ] := ParityEvenQ[expr, {S}]

ParityOddQ[ S_?SpeciesQ ][ expr_ ] := ParityOddQ[expr, {S}]


ParityEvenQ[ ss:{__?SpeciesQ} ][ expr_ ] := ParityEvenQ[expr, ss]

ParityOddQ[ ss:{__?SpeciesQ} ][ expr_ ] := ParityOddQ[expr, ss]


ParityEvenQ[ expr_Association, ss:{__?SpeciesQ} ] :=
  Map[ ParityEvenQ[ss], expr ]

ParityOddQ[ expr_Association, ss:{__?SpeciesQ} ] :=
  Map[ ParityOddQ[ss], expr ]


ParityEvenQ[ expr_List, ss:{__?SpeciesQ} ] :=
  Map[ ParityEvenQ[ss], expr ] /;
  Not @ FreeQ[expr, _Ket]

ParityOddQ[ expr_List, ss:{__?SpeciesQ} ] :=
  Map[ ParityOddQ[ss], expr ] /;
  Not @ FreeQ[expr, _Ket]


ParityEvenQ[ z_?CommutativeQ expr_, ss:{__?SpeciesQ} ] :=
  ParityEvenQ[expr, ss] /;
  Not @ FreeQ[expr, _Ket]

ParityOddQ[ z_?CommutativeQ expr_, ss:{__?SpeciesQ} ] :=
  ParityOddQ[expr, ss] /;
  Not @ FreeQ[expr, _Ket]


ParityEvenQ[ expr_Plus, ss:{__?SpeciesQ} ] :=
  And @@ ParityEvenQ[Cases[expr, _Ket, Infinity], ss] /;
  Not @ FreeQ[expr, _Ket]

ParityOddQ[ expr_Plus, ss:{__?SpeciesQ} ] :=
  And @@ ParityOddQ[Cases[expr, _Ket, Infinity], ss] /;
  Not @ FreeQ[expr, _Ket]


ParityEvenQ[ Ket[<||>], {} ] := True

ParityOddQ[ Ket[<||>], {} ] := False


ParityEvenQ[ v_Ket, ss:{__?SpeciesQ} ] :=
  Not[ Xor @@ Map[ParityOddQ[v,#]&, FlavorNone @ ss] ]

ParityOddQ[ v_Ket, ss:{__?SpeciesQ} ] :=
  Xor @@ Map[ParityOddQ[v,#]&, FlavorNone @ ss]

(**** </Parity> ****)


(**** <RotationSystem> ****)

RotationSystem::usage = "RotationSystem[mat] returns the rotation angle and axis in the form {angle, {x, y, z}} that the matrix mat represents.\nFor rotations in the three-dimensional space of real vectors, mat is a 3\[Times]3 real orthogonal matrix. In this case, the returned angle is in the range from -\[Pi] to \[Pi].\nFor rotations in the Bloch space, mat is a 2\[Times]2 unitary matrix. Angle is in the range from -2\[\Pi] to 2\[Pi].\nIn either case, the axis vector always points to the upper hemisphere."

RotationSystem::notuni = "Matrix `` is not a unitary matrix; its determinant is ``."

RotationSystem::notorth = "Matrix `` is not an orthogonal matrix; its determinant is ``."

RotationSystem[Rotation[a_, v:{_, _, _}, (_?SpinQ|_?QubitQ), ___]] := {a, v}

RotationSystem[mat_?MatrixQ] := Module[
  { ang, vec },
  If[ Not @ UnitaryMatrixQ @ mat,
    Message[RotationSystem::notuni, Normal @ mat, Chop @ Det @ mat]
   ];
  
  ang = Tr[mat / Sqrt[Det @ mat]] / 2;
  ang = Simplify @ ExpToTrig @ ang;
  ang = Chop[2 * ArcCos[Chop @ ang]];

  vec = I * PauliVector[mat / Sqrt[Det @ mat]];
  vec = Simplify @ ExpToTrig @ vec;
  If[ Chop[Norm @ vec] == 0,
    Return @ {0, {0, 0, 1}},
    vec = Chop[Normalize @ vec]
   ];
  
  Which[
    vec[[3]] < 0,
    ang = -ang;
    vec = -vec,
    vec[[3]] == 0,
    Which[
      vec[[2]] < 0,
      ang = -ang;
      vec = -vec,
      vec[[2]] == 0,
      Which[
        vec[[1]] < 0,
        ang = -ang;
        vec = -vec,
        vec[[1]] == 0,
        ang = 0
       ]
     ]
   ];
  Chop @ {ang, vec}
 ] /; Dimensions[mat] == {2, 2}


RotationSystem[mat_?MatrixQ] := Module[
  { new = Det[mat] * mat,
    ang, vec },
  If[ Not @ OrthogonalMatrixQ[mat],
    Message[RotationSystem::notorth, Normal @ mat];
    Return[{0, {0, 0, 1}}]
   ];
  ang = ArcCos[(Tr[new] - 1) / 2];
  vec = - {
    new[[2,3]] - new[[3,2]],
    new[[3,1]] - new[[1,3]],
    new[[1,2]] - new[[2,1]]
   } / 2;
  vec = Chop[Normalize @ vec];
  Which[
    vec[[3]] < 0,
    ang = -ang;
    vec = -vec,
    vec[[3]] == 0,
    Which[
      vec[[2]] < 0,
      ang = -ang;
      vec = -vec,
      vec[[2]] == 0,
      Which[
        vec[[1]] < 0,
        ang = -ang;
        vec = -vec,
        vec[[1]] == 0,
        ang = 0
       ]
     ]
   ];
  Chop @ {ang, vec}
 ] /; Dimensions[mat] == {3, 3}


RotationAxis::usage = "RotationAxis[mat] returns the vector pointing along the rotation axis that the matrix mat represents. The axis vector always points to the upper hemisphere."

RotationAxis[Rotation[_, v:{_, _, _}, (_?SpinQ|_?QubitQ), ___]] = v

RotationAxis[mat_?MatrixQ] := Last @ RotationSystem[mat] /;
  Dimensions[mat] == {2, 2} || Dimensions[mat] == {3, 3}


RotationAngle::usage = "RotationAngle[mat] returns the rotation angle that the matrix mat describes. The angle is in the range from -2\[Pi] to 2\[Pi] for a 2\[Times]2 unitary matrix mat, and in the range from -\[Pi] to \[Pi] for a 3\[Times]3 orthogonal matrix mat."

RotationAngle[Rotation[a_, {_, _, _}, (_?SpinQ|_?QubitQ), ___]] = a

RotationAngle[mat_?MatrixQ] := First @ RotationSystem[mat] /;
  Dimensions[mat] == {2, 2} || Dimensions[mat] == {3, 3}

(**** </RotationSystem> ****)


(**** <TheEulerAngles> ****)

TheEulerAngles::usage = "TheEulerAngles[U] gives the Euler angles {\[Alpha],\[Beta],\[Gamma]} of the SU(2) matrix U, where -\[Pi] < \[Alpha],\[Gamma] \[LessEqual] \[Pi] and 0 \[LessEqual] \[Beta] \[LessEqual] \[Pi]. TheEulerRotation[TheEulerAngles[U]] == U.\nTheEulerAngles[expr] gives the Euler angles {\[Alpha],\[Beta],\[Gamma]} of the single-qubit unitary operator given by expr in terms of Pauli operators."

TheEulerAngles::su = "Matrix `` is not a 2x2 special unitary matrix; its determinant is ``."

TheEulerAngles[U_?MatrixQ] := Module[
  { arg = Arg[U],
    ang = {0, 0, 0} },
  
  If[ UnitaryMatrixQ[U],
    If[Chop[Det @ U] != 1, Message[TheEulerAngles::su, U, Det @ U]],
    Message[TheEulerAngles::su, U, Chop @ Det @ U]
   ];
  
  ang[[1]] = -arg[[1, 1]] + arg[[2, 1]];
  ang[[3]] = -arg[[1, 1]] - arg[[2, 1]];
  ang[[2]] = 2 ArcSin[ Abs[U[[2, 1]]] ];
  ang
 ]


TheEulerAngles::notOp = "`` is not a single-qubit operation."

TheEulerAngles[1] = {0, 0, 0}

TheEulerAngles[expr_] := Module[
  { U = Matrix[expr] },
  If[ Dimensions[U] != {2,2},
    Message[EulerAngles::notOp, expr]
   ];
    
  TheEulerAngles[U]
 ] /; Not @ FreeQ[expr, _Pauli]

(**** </TheEulerAngles> ****)


(**** <TheRotation> ****)

TheRotation::usage = "TheRotation[\[Phi], 1], TheRotation[\[Phi], 2], TheRotation[\[Phi], 3] give the 2x2 matrix representing the rotation by angle \[Phi] around the x, y, and z axis, respective in the two-dimensional Hilbert  space.\nTheRotation[{x1, n1,}, {x2, n2,}, \[Ellipsis]] = TheRotation[x1, n1] \[CircleTimes] Rotation[x2, n2] \[CircleTimes] \[Ellipsis].\nTheRotation[\[Phi], {J, 1}], TheRotation[\[Phi], {J, 2}], TheRotation[\[Phi], {J, 3}] give the rotation matrices by angle \[Phi] around the x, y, and z axis, respective, for Spin = J."

TheRotation[_, 0] := ThePauli[0]

TheRotation[ph_, n:(1|2|3)] :=
  Cos[ph/2] * ThePauli[0] - I*Sin[ph/2] * ThePauli[n]

TheRotation[{ph_, n:(0|1|2|3)}] := TheRotation[ph, n]

TheRotation[a:{_, (0|1|2|3)}, b:{_, (0|1|2|3)}..] :=
  Apply[CircleTimes, TheRotation @@@ {a, b}]


TheRotation[{ph_, v:{_, _, _}}] := TheRotation[ph, v]

TheRotation[ph_, v:{_, _, _}] := One[2] /; Chop[Norm @ v] == 0

TheRotation[ph_, v:{_, _, _}] := Cos[ph/2] * ThePauli[0] -
  I*Sin[ph/2] * Normalize[v] . {ThePauli[1], ThePauli[2], ThePauli[3]}

TheRotation[a:{_, {_, _, _}}, b:{_, {_, _, _}}..] :=
  Apply[CircleTimes, TheRotation @@@ {a, b}]

(**** </TheRotation> ****)


(**** <TheEulerRotation> ****)

TheEulerRotation::usage = "TheEulerRotation[{a,b,c}] = TheRotation[a,3].TheRotation[b,2].TheRotation[c,3] and TheEulerRotation[{a,b}]=TheEulerRotation[{a,b,0}] return the matrices corresponding to the Euler rotations in SU(2) space.\nTheEulerRotation[{a, b, c}, J] gives the Euler rotation matrix in the angular momentum J representation."

TheEulerRotation[ {phi_, theta_, chi_} ] := {
  {Cos[theta/2]*Exp[-I*(phi+chi)/2], -Sin[theta/2]*Exp[-I*(phi-chi)/2]},
  {Sin[theta/2]*Exp[+I*(phi-chi)/2],  Cos[theta/2]*Exp[+I*(phi+chi)/2]}
 }

TheEulerRotation[ {phi_,theta_} ] := TheEulerRotation[ {phi, theta, 0} ]

TheEulerRotation[a:{_, _, _}, b:{_, _, _}..] :=
  CircleTimes @@ Map[TheEulerRotation, {a, b}]

(**** </TheEulerRotation> ****)


(**** <Rotation> ****)

Rotation::usage = "Rotation[\[Phi], 1], Rotation[\[Phi], 2], and Rotation[\[Phi], 3] returns an operator corresponding to the rotations by angle \[Phi] around the x, y, and z axis, respective, in a two-dimensioinal Hilbert space.\nRotation[{a1, n1}, {a2, n2}, ...] = Rotation[a1, n1] \[CircleTimes] Rotation[a2, n2] \[CircleTimes] ...\nRotation[a, {x, y, z}] returns an operator corresponding the rotation by angle a around the axis along the vector {x, y, z}.\nRotation[\[Phi], S[j, ..., k]] represents the rotation by angle \[Phi] around the axis k on the qubit S[j, ..., $]."

Rotation[_, 0] := Pauli[0]

Rotation[phi_, n:(1|2|3)] := Cos[phi/2]*Pauli[0]-I*Sin[phi/2]*Pauli[n]

Rotation[{phi_, n:(0|1|2|3)}] := Rotation[phi, n]

Rotation[a:{_, (0|1|2|3)}, b:{_, (0|1|2|3)}..] :=
  CircleTimes @@ Map[Rotation, {a, b}]


Rotation[{ph_, v:{_, _, _}}] := Rotation[ph, v]

Rotation[ph_, v:{Repeated[Except[_?QubitQ|_?SpinQ], {3}]}] :=
  Cos[ph/2] Pauli[0] -
  I Sin[ph/2] * Normalize[v] . {Pauli[1], Pauli[2], Pauli[3]}

Rotation[a:{_, {_, _, _}}, b:{_, {_, _, _}}..] :=
  Apply[CircleTimes, Rotation @@@ {a, b}]


(* Rotation on Qubit and Spin *)

Rotation::axis = "The axis in `` is not proper."

Options[Rotation] = { "Label" -> Automatic }

Rotation[phi_, S:(_?SpinQ|_?QubitQ), opts___?OptionQ] := (
  Message[Rotation::axis, S];
  Rotation[0, {0, 0, 1}, S[$], opts]
 ) /; Not @ MemberQ[{1, 2, 3}, FlavorLast @ S]

Rotation[aa_List, qq:{(_?SpinQ|_?QubitQ)..}, rest___] :=
  MapThread[Rotation[#1, #2, rest]&, {aa, qq}]

Rotation[aa_List, S:(_?SpinQ|_?QubitQ), rest___] :=
  Map[Rotation[#, S, rest]&, aa]

Rotation[phi_, qq:{(_?SpinQ|_?QubitQ)..}, rest___] :=
  Map[Rotation[phi, #, rest]&, qq]

Rotation[phi_, S:(_?SpinQ|_?QubitQ), opts___?OptionQ] :=
  Rotation[phi, UnitVector[3, FlavorLast @ S], FlavorMute @ S, opts]


Rotation::real = "The vector `` must be real to specify a rotation axis."

Rotation[phi_, v:{_, _, _}, S:(_?SpinQ|_?QubitQ), rest___] := (
  Message[Rotation::real, v];
  Rotation[phi, Re @ v, S, rest]
 ) /; Not @ AllTrue[v, RealQ]

Rotation[phi_, v:{_, _, _}, S:(_?SpinQ|_?QubitQ), rest___] :=
  Rotation[phi, v, S[$], rest] /;
  Not[FlavorNoneQ @ S]

Rotation[phi_, v:{_, _, _}, ss:{(_?SpinQ|_?QubitQ)..}, rest___] :=
  Map[Rotation[phi, v, #, rest]&, ss]


Rotation /:
Multiply[pre___, op_Rotation, post___] :=
  Multiply[pre, Elaborate[op], post]

Rotation /:
Dagger[ Rotation[ang_, v:{_, _, _}, S:(_?SpinQ|_?QubitQ), rest___] ] :=
  Rotation[-Conjugate[ang], v, S, rest]


Rotation /:
Matrix[op_Rotation, rest___] := Matrix[Elaborate @ op, rest]


Rotation[phi_, S:(_?QubitQ|_?SpinQ), v:{_, _, _}, opts___?OptionQ] := (
  Message[Q3General::changed, Rotation,
    "The vector must come before species specification."];
  Rotation[phi, v, S, opts]
 )

Rotation[S:(_?QubitQ|_?SpinQ), ang_, rest___] := (
  Message[Q3General::angle, Rotation];
  Rotation[ang, S, rest]
 )

Rotation[qq:{(_?QubitQ|_?SpinQ)..}, ang_, rest___] := (
  Message[Q3General::angle, Rotation];
  Rotation[ang, qq, rest]
 )

(**** </Rotation> ****)


(**** <EulerRotation> ****)

EulerRotation::usage = "EulerRotation[{a, b, c}] = Rotation[a, 3].Rotation[b, 2].Rotation[c, 3] represent the Euler rotation by angles a, b, c in a two-dimensional Hilbert space."

EulerRotation[ {a_, b_, c_} ] :=
  Rotation[a, 3].Rotation[b, 2].Rotation[c, 3]

EulerRotation[a:{_, _, _}, b:{_, _, _}..] :=
  CircleTimes @@ Map[EulerRotation, {a, b}]


(* Rotation on Qubit and Spin *)

Options[EulerRotation] = { "Label" -> Automatic }


EulerRotation[aa:{_, _, _}, ss:{(_?SpinQ|_?QubitQ)..}, rest___] :=
  Map[EulerRotation[aa, #, rest]&, FlavorNone @ ss]

EulerRotation[aa:{_, _, _}, G:(_?SpinQ|_?QubitQ), rest___] :=
  EulerRotation[aa, G[$], rest] /; Not[FlavorNoneQ @ G]


EulerRotation /:
Multiply[pre___, op_EulerRotation, post___ ] :=
  Multiply[pre, Elaborate @ op, post]


EulerRotation /:
Matrix[op_EulerRotation, rest___] := Matrix[Elaborate @ op, rest]


EulerRotation /:
Elaborate @ EulerRotation[{a_, b_, c_}, S:(_?SpinQ|_?QubitQ), ___] :=
  Garner @ Multiply[
    Elaborate @ Rotation[a, S[3]],
    Elaborate @ Rotation[b, S[2]],
    Elaborate @ Rotation[c, S[3]]
   ]


EulerRotation[S:(_?SpinQ|_?QubitQ), ang_, rest___] := (
  Message[Q3General::angle, EulerRotation];
  EulerRotation[ang, S, rest]
 )

EulerRotation[ss:{(_?SpinQ|_?QubitQ)..}, ang_, rest___] := (
  Message[Q3General::angle, EulerRotation];
  EulerRotation[ang, ss, rest]
 )

(**** </EulerRotation> ****)


(* *********************************************************************** *)
(*     <Dot for Pauli and Bra/Ket>                                         *)
(* *********************************************************************** *)

(* Recall that Dot has attributes Flat and OneIdentity. *)
Dot[a_ + b_, c_] := Dot[a, c] + Dot[b, c]

Dot[c_, a_ + b_] := Dot[c, a] + Dot[c, b]

Dot[ a_ b_, c_] := a Dot[b, c] /; FreeQ[a, _Dot|_Pauli|_Ket|_Bra]

Dot[ a_, b_ c_] := b Dot[a, c] /; FreeQ[b, _Dot|_Pauli|_Ket|_Bra]


(* Pauli operating on Ket and Bra *)

Pauli /: Dot[ Pauli[0], a_Ket ] := a

Pauli /: Dot[ a_Bra, Pauli[0] ] := a

Pauli /:
Dot[ Pauli[n:(1|2|3|4|5|6|7|8)], Ket[0|Up] ] :=
  Dot[ {Ket[0],Ket[1]}, ThePauli[n][[;;,1]] ]

Pauli /:
Dot[ Pauli[n:(1|2|3|4|5|6|7|8)], Ket[1|Down] ] :=
  Dot[ {Ket[0],Ket[1]}, ThePauli[n][[;;,2]] ]

Pauli /:
Dot[ Bra[0|Up], Pauli[n:(1|2|3|4|5|6|7|8)] ] :=
  Dot[ ThePauli[n][[1,;;]], {Bra[0],Bra[1]} ]

Pauli /:
Dot[ Bra[1|Down], Pauli[n:(1|2|3|4|5|6|7|8)] ] :=
  Dot[ ThePauli[n][[2,;;]], {Bra[0],Bra[1]} ]

Pauli /:
Dot[ z_?CommutativeQ, op_Pauli ] := z * op

Pauli /:
Dot[ op_Pauli, z_?CommutativeQ ] := z * op

Pauli /:
Dot[ Pauli[0], Pauli[n_] ] := Pauli[n]

Pauli /:
Dot[ Pauli[n_], Pauli[0] ] := Pauli[n]

Pauli /:
Dot[ Pauli[n:(0|1|2|3)], Pauli[n:(0|1|2|3)] ] := Pauli[0]

Pauli /:
Dot[ Pauli[m_], Pauli[n_] ] := Pauli[0] /; m == -n

Pauli /:
Dot[ Pauli[7], Pauli[7] ] := Pauli[3]

Pauli /:
Dot[ Pauli[8], Pauli[8] ] := Pauli[7]

Pauli /:
Dot[ Pauli[n:(4|5)], Pauli[n:(4|5)] ] := 0

Pauli /:
Dot[ Pauli[1], Pauli[2] ] := I Pauli[3]

Pauli /:
Dot[ Pauli[2], Pauli[3] ] := I Pauli[1]

Pauli /:
Dot[ Pauli[3], Pauli[1] ] := I Pauli[2]

Pauli /:
Dot[ Pauli[2], Pauli[1] ] := -I Pauli[3]

Pauli /:
Dot[ Pauli[3], Pauli[2] ] := -I Pauli[1]

Pauli /:
Dot[ Pauli[1], Pauli[3] ] := -I Pauli[2]

(* general rules *)

Pauli /:
Dot[ Pauli[m_], Pauli[n_] ] :=
  Garner @ Dot[Elaborate @ Pauli @ m, Elaborate @ Pauli @ n]

Pauli /:
Dot[ Pauli[a_, b__], Pauli[c_, d__] ] :=
  CircleTimes @@ Dot @@@ Transpose[{ Pauli /@ {a, b}, Pauli /@ {c, d} }]
  
Pauli /:
Dot[ Pauli[a_, b__], Ket[c_, d__] ] := CircleTimes @@
  Dot @@@ Transpose[{ Pauli /@ {a,b}, Ket /@ {c,d} }]

Pauli /:
Dot[ Bra[c_, d__], Pauli[a_, b__] ] := CircleTimes @@
  Dot @@@ Transpose[{ Bra /@ {c,d}, Pauli /@ {a,b} }]

(* *********************************************************************** *)
(*     </Dot for Pauli and Bra/Ket>                                        *)
(* *********************************************************************** *)


(**** <CircleTimes> ****)

CircleTimes::usage = "CircleTimes[a,b,c] or a \[CircleTimes] b \[CircleTimes] c represents the tensor product of (abstract) algebraic tensors a, b, c, ....\nWhen a, b, c, ... are vectors or matrices, it returns the matrix direct product of them.\nCirlceTimes is a built-in symbol with context System`, and has been extended in Q3.\nSee \!\(\*TemplateBox[{\"Q3/ref/CircleTimes\", \"paclet:Q3/ref/CircleTimes\"}, \"RefLink\", BaseStyle->\"InlineFunctionSans\"]\) for more details."

SetAttributes[CircleTimes, ReadProtected]

CircleTimes[] = 1 (* See also Times[]. *)

CircleTimes[a_] := a (* See also Times[]. *)

(* NOTE: DO NOT set the Flat and OneIdentity attributes for
   Cirlcetimes. Otherwise, the following definitions cause infinite loops. *)

HoldPattern @ CircleTimes[args__] := Garner @ ReleaseHold[
  Distribute @ Hold[CircleTimes][args]
 ] /; DistributableQ[args]

CircleTimes[pre___, z_?CommutativeQ op_, post___] :=
  z * CircleTimes[pre, op, post]

CircleTimes[___, 0, ___] = 0
(* This happens when some vectors or operators are null. *)

HoldPattern @ CircleTimes[ pre___,
  op:Multiply[Ket[__], Bra[__]],
  more:(Multiply[Ket[__], Bra[__]]..),
  Shortest[post___] ] := CircleTimes[ pre,
    Apply[Multiply, CircleTimes @@@ Transpose[List @@@ {op, more}]],
    post ]

(* On matrices, it operates the same as KroneckerProduct[]. *)
CircleTimes[mats__?MatrixQ] := KroneckerProduct[mats]

(* For vectors, our CircleTimes[] is different from KroneckerProduct[]. *)
CircleTimes[vecs__?VectorQ] := Flatten @ TensorProduct[vecs]

(*
CircleTimes /:
Multiply[pre___, HoldPattern @ CircleTimes[aa__], Ket[bb__], post___] :=
  Multiply[pre, CircleTimes @@ Multiply[{aa}, Ket /@ {bb}], post]
 *)

(**** </CircleTimes> ****)


(**** <CirclePlus> ****)

(* BlockDiagonalMatrix (experimental) is now included in Mathematica since v13.1. *)

If[ $VersionNumber < 13.1,
  BlockDiagonalMatrix::usage = "BlockDiagonalMatrix[{a,b,c,...}] returns a matrix with the matrices a, b, c, ... as its blocks. BlockDiagonalMatrix[a,b,c,...] is the same.";

  BlockDiagonalMatrix[mm:({}|_?MatrixQ)..] := BlockDiagonalMatrix @ {mm};

  BlockDiagonalMatrix[mm:{({}|_?MatrixQ)..}] := Module[
    { new = DeleteCases[mm, {}],
      x, y },
    { x, y } = Transpose @ Map[Dimensions] @ new;
    x = Range[Accumulate @ Most @ Prepend[x, 1], Accumulate @ x];
    y = Range[Accumulate @ Most @ Prepend[y, 1], Accumulate @ y];
    x = Catenate @ Map[Tuples] @ Transpose @ {x, y};
    SparseArray @ Thread[x -> Flatten @ new]
   ];
 ]

CirclePlus::usage = "a \[CirclePlus] b \[CirclePlus] c or CirclePlus[a,b,c]
returns the direct sum of the matrices a, b, and c."

CirclePlus[pre___, {}, post___] := CirclePlus[pre, post]

CirclePlus[mm__?MatrixQ] := BlockDiagonalMatrix[{mm}]

CirclePlus[vv__?VectorQ] := Join[vv]

(**** </CirclePlus> ****)


(**** <Dyad> ****)

Dyad::usage = "Dyad[a, b] for two vectors a and b return the dyad (a tensor of order 2 and rank 1) corresponding to the dyadic product of two vectors.\nDyad[a, b, qq] for two associations a and b and for a list qq of Species represents the dyadic product of Ket[a] and Ket[b], i.e., Ket[a]**Bra[b], operating on the systems in qq."

Dyad::one = "Dyad explicitly requires a pair of vectors now."

Dyad::two = "Dyad now requires an explicit specification of the species to apply the operator on."

Dyad::extra = "Some elements in `` are not included in ``."

Dyad::mtrx = "Matrix representation of Dyad of the form `` is not supported."

(* For Kets associated with species *)

Format @ Dyad[a_Association, b_Association] :=
  Interpretation[Row @ {Ket[a], Bra[b]}, Dyad[a, b]]

Dyad /: NonCommutativeQ[ Dyad[___] ] = True

Dyad /:
MultiplyKind @ Dyad[a_Association, b_Association] :=
  First @ MultiplyKind @ Union[Keys @ a, Keys @ b]

Dyad /:
MultiplyGenus @ Dyad[___] := "Singleton"

Dyad /:
Dagger[op_Dyad] := Conjugate[op] (* fallback *)

Dyad /:
Dagger @ Dyad[a_Association, b_Association] = Dyad[b, a]

Dyad /:
Elaborate[op_Dyad] = op (* fallback *)

Dyad /:
Elaborate @ Dyad[a_Association, b_Association] := Module[
  { ss = Intersection[Keys[a], Keys[b]],
    op },
  op = Construct @@@ Thread @ {ss, Thread[Lookup[b, ss] -> Lookup[a, ss]]};
  Garner @ Multiply[
    Elaborate[Multiply @@ op],
    Dyad[KeyDrop[a, ss], KeyDrop[b, ss]]
   ]
 ]


Dyad /: (* fallback *)
Matrix[op_Dyad, ss_List, tt_List] := Zero[Length @ ss, Length @ tt]
  
Dyad /:
Matrix[op_Dyad, ss:{__?SpeciesQ}, tt:{__?SpeciesQ}] :=
  Matrix[op, FlavorNone @ ss, FlavorNone @ tt] /;
  Not[FlavorNoneQ @ {ss, tt}]

Dyad /:
Matrix[ Dyad[a_Association, b_Association],
  ss:{__?SpeciesQ}, tt:{__?SpeciesQ} ] := Module[
    { sa = Complement[ss, Keys @ a],
      tb = Complement[tt, Keys @ b],
      aa, bb },
    If[sa != tb,
      Message[Dyad::mtrx, Row @ {ss, Keys @ a, Keys @ b, tt}];
      Return @ Zero[Length @ ss, Length @ tt]
     ];
    aa = Map[TheMatrix] @ Map[KeyTake[ss]] @ Map[Join[a, #]&] @
      Map[AssociationThread[sa -> #]&] @ Tuples[LogicalValues @ sa];
    bb = Map[TheMatrix] @ Map[KeyTake[tt]] @ Map[Join[b, #]&] @
      Map[AssociationThread[tb -> #]&] @ Tuples[LogicalValues @ tb];
    Total @ MapThread[ Dyad, {CircleTimes @@@ aa, CircleTimes @@@ bb}]
   ]


Dyad /: (* fallback *)
Matrix[op_Dyad, ss_List] := Zero[Length @ ss, Length @ ss]
  
Dyad /:
Matrix[op_Dyad, ss:{__?SpeciesQ}] := Matrix[op, FlavorNone @ ss] /;
  Not[FlavorNoneQ @ ss]

Dyad /:
Matrix[op:Dyad[a_Association, b_Association], ss:{__?SpeciesQ}] :=
  With[
    { rest = Dyad[KeyDrop[a, ss], KeyDrop[b, ss]] },
    Message[Matrix::rmndr, rest];
    rest * Matrix[Dyad[KeyTake[a, ss], KeyTake[b, ss]], ss]
   ] /; Not @ ContainsAll[ss, Union[Keys @ a, Keys @ b]]

Dyad /:
Matrix[op:Dyad[a_Association, b_Association], ss:{__?SpeciesQ}] :=
  ( Message[Dyad::mtrx, InputForm @ op];
    One[Times @@ Dimension[ss]]
   ) /; Keys[a] != Keys[b]

Dyad /:
Matrix[op:Dyad[a_Association, b_Association], ss:{__?SpeciesQ}] :=
  Module[
    { rr = One /@ Dimension[ss] },
    rr = Join[AssociationThread[ss -> rr], splitDyad[op]];
    CircleTimes @@ rr
   ]

Dyad /:
splitDyad @ Dyad[a_Association, b_Association] :=
  AssociationThread[
    Keys[a] -> MapThread[Dyad, {TheMatrix @ a, TheMatrix @ b}]
   ]


Dyad[a_] := Module[
  { qq = Agents[a] },
  Message[Dyad::one];
  Dyad[a, a, qq]
 ] /; Not @ FreeQ[a, _Ket]

Dyad[a_, b_] := Module[
  { qq = Agents @ {a, b} },
  Message[Dyad::two];
  Dyad[a, b, qq]
 ] /; Not @ FreeQ[{a, b}, Ket[_Association]]


(* Direct constuction of Dyad *)
Dyad[{aa___Rule, ss:{__?SpeciesQ}...}, {bb___Rule, tt:{__?SpeciesQ}...}] :=
  With[
    { sss = Union @ FlavorNone @ Join[ss],
      ttt = Union @ FlavorNone @ Join[tt] },
    Dyad[
      KeySort @ Join[
        AssociationThread[sss -> Lookup[<||>, sss]],
        Association @ KetRule @ {aa} ],
      KeySort @ Join[
        AssociationThread[ttt -> Lookup[<||>, ttt]],
        Association @ KetRule @ {bb} ]
     ]
   ]


Dyad[<||>, <||>] = 1

Dyad[0, _, __List] = 0

Dyad[_, 0, __List] = 0


Dyad[S_?SpeciesQ] := Dyad[FlavorNone @ {S}]

Dyad[ss:{__?SpeciesQ}] := Dyad[FlavorNone @ ss] /; Not[FlavorNoneQ @ ss]

Dyad[ss:{__?SpeciesQ}][a_, b_] := Dyad[a, b, ss]


Dyad[a_, b_, ss_] := Dyad[a, b, ss, ss]

Dyad[a_, b_, S_?SpeciesQ, tt_] := Dyad[a, b, S @ {$}, tt]

Dyad[a_, b_, ss_, T_?SpeciesQ] := Dyad[a, b, ss, T @ {$}]

Dyad[a_, b_, ss:{__?SpeciesQ}, tt:{__?SpeciesQ}] :=
  Dyad[a, b, FlavorNone @ ss, FlavorNone @ tt] /;
  Not[FlavorNoneQ @ {ss, tt}]

Dyad[Ket[a_Association], Ket[b_Association], ss:{__?SpeciesQ}] :=
  Dyad[Ket[a], Ket[b], ss, ss]

Dyad[Ket[a_Association], Ket[b_Association],
  ss:{__?SpeciesQ}, tt:{__?SpeciesQ}] := Dyad[
    AssociationThread[ss -> Lookup[a, ss]],
    AssociationThread[tt -> Lookup[b, tt]]
   ]

Dyad[a_Association, b_Association] := Module[
  { ss = GroupBy[Union[Keys @ a, Keys @ b], MultiplyKind] },
  Multiply @@ Map[Dyad[KeyTake[a, #], KeyTake[b, #]]&, Values @ ss]
 ] /; Length[Union @ MultiplyKind @ Flatten @ {Keys @ a, Keys @ b}] > 1


Dyad[a_Plus, b_, qq___] := Garner @ Map[Dyad[#, b, qq]&, a]

Dyad[a_, b_Plus, qq___] := Garner @ Map[Dyad[a, #, qq]&, b]

Dyad[z_?CommutativeQ a_, b_, qq___] := Garner[z * Dyad[a, b, qq]]

Dyad[a_, z_?CommutativeQ b_, qq___] := Garner[Conjugate[z] * Dyad[a, b, qq]]


HoldPattern @ Multiply[
  pre___,
  xx:Dyad[a_Association, b_Association],
  yy:Dyad[c_Association, d_Association],
  post___
 ] := Module[
   { bb = Complement[Keys @ b, Keys @ c],
     cc = Complement[Keys @ c, Keys @ b],
     bc = Intersection[Keys @ b, Keys @ c] },
   Dyad[
     KeySort @ CheckJoin[a, KeyTake[c, cc]],
     KeySort @ CheckJoin[d, KeyTake[b, bb]]
    ] * BraKet[KeyTake[b, bc], KeyTake[c, bc]]
  ] /; MultiplyKind[xx] == MultiplyKind[yy]

HoldPattern @ Multiply[
  pre___,
  op_?AnySpeciesQ, Dyad[a_Association, b_Association],
  post___
 ] := Multiply[
   pre,
   Dyad[op ** Ket[a], Ket[b], Keys @ a, Keys @ b],
   post
  ] /; MemberQ[Keys @ a, FlavorMute @ Peel @ op]

HoldPattern @ Multiply[
  pre___,
  Dyad[a_Association, b_Association], op_?AnySpeciesQ,
  post___
 ] := Multiply[
   pre,
   Dyad[Ket[a], Dagger[op] ** Ket[b], Keys @ a, Keys @ b],
   post
  ] /; MemberQ[Keys @ b, FlavorMute @ Peel @ op]


HoldPattern @ Multiply[
  pre___,
  op_?AnySpeciesQ, Dyad[a_Association, b_Association],
  post___
 ] := Multiply[pre, Dyad[a, b], op, post] /;
  With[
    { sp = FlavorMute @ Peel @ op },
    And[
      MultiplyKind[Dyad[a, b]] == MultiplyKind[op],
      Not @ MemberQ[Union[Keys @ a, Keys @ b], sp],
      Not @ OrderedQ @ {sp, First @ Keys @ a}
     ]
   ]

HoldPattern @ Multiply[
  pre___,
  Dyad[a_Association, b_Association], op_?AnySpeciesQ,
  post___
 ] := Multiply[pre, op, Dyad[a, b], post] /; With[
   { sp = FlavorMute @ Peel @ op },
   And[
     MultiplyKind[Dyad[a, b]] == MultiplyKind[op],
     Not @ MemberQ[Union[Keys @ a, Keys @ b], sp],
     Not @ OrderedQ @ {First @ Keys @ b, sp}
    ]
  ]


HoldPattern @ Multiply[
  pre___,
  Bra[v_Association],
  Dyad[a_Association, b_Association],
  post___
 ] := Garner @ With[
   { w = KeyDrop[v, Keys @ a],
     u = KeyTake[v, Keys @ a] },
   BraKet[u, a] * Multiply[pre, Bra[w], Bra[b], post]
  ]

HoldPattern @ Multiply[
  pre___,
  Dyad[a_Association, b_Association],
  Ket[v_Association],
  post___
 ] := Garner @ With[
   { w = KeyDrop[v, Keys @ b],
     u = KeyTake[v, Keys @ b] },
   BraKet[b, u] * Multiply[pre, Ket[a], Ket[w], post]
  ]

(* For Pauli Kets *)

Dyad[Ket[a:(0|1)..], Ket[b:(0|1)..], ___] := Pauli[{b} -> {a}]

(* For general kets for unlabelled systems *)

Dyad[a_Ket, b_Ket, ___] := Multiply[a, Dagger @ b]


(* For simple column vectors *)

Dyad[a_?VectorQ] := ( Message[Dyad::one]; Dyad[a, a] ) /; FreeQ[a, _?SpeciesQ]

Dyad[a_?VectorQ, b_?VectorQ] := KroneckerProduct[a, Dagger @ b]
(* NOTE: Dagger -- not Conjugate -- in the above two definitions. *)

(**** </Dyad> ****)


(**** <DyadForm> ****)

DyadForm::usage = "DyadForm[expr,{s1,s2,..}] converts the operator expression expr to the form in terms of Dyad acting on the systems s1, s2, .... If the systems are not specified, then they are extracted from expr.\nDyadForm[mat,{s1,s2,...}] converts the matrix representation into an operator expresion in terms of Dyad acting on the systems s1, s2, ...."

DyadForm[expr_] := RaiseLower[expr] /; Not @ FreeQ[expr, _Pauli]
(* NOTE: DyaForm is pointless for Pauli expressions. *)

DyadForm[expr_] := DyadForm[expr, Agents @ expr]

DyadForm[expr_, q_?SpeciesQ] := DyadForm[expr, q @ {$}]

DyadForm[expr_, qq:{__?SpeciesQ}] := DyadForm[Matrix[expr, qq], qq]

DyadForm[expr_, qq:{__?SpeciesQ}] := DyadForm[expr, FlavorNone @ qq] /;
  Not[FlavorNoneQ @ qq]


DyadForm[mat_?MatrixQ] := Module[
  { n = Log[2, Length @ mat],
    tsr },
  tsr = ArrayReshape[mat, ConstantArray[2, 2*n]];
  tsr = Association @ Most @ ArrayRules @ tsr;
  Garner @ Total @ KeyValueMap[theDyadForm[#1, n] * #2&, tsr]
 ] /; IntegerQ[Log[2, Length @ mat]]

theDyadForm[val:{__}, n_Integer] := Module[
  {a, b},
  {a, b} = ArrayReshape[val-1, {2, n}];
  Thread @ Pauli[b -> a]
 ]


DyadForm[mat_?MatrixQ, qq:{__?SpeciesQ}] := Module[
  { dim = Dimension @ qq,
    spc = FlavorNone @ qq,
    tsr },
  tsr = ArrayReshape[mat, Join[dim, dim]];
  tsr = Association @ Most @ ArrayRules @ tsr;
  Garner @ Total @ KeyValueMap[theDyadForm[#1, spc] * #2&, tsr]
 ]

theDyadForm[val:{__}, spc:{__?SpeciesQ}] := Module[
  {a, b},
  {a, b} = ArrayReshape[val, {2, Length @ spc}];
  a = MapThread[Part, {LogicalValues @ spc, a}];
  b = MapThread[Part, {LogicalValues @ spc, b}];
  Dyad[AssociationThread[spc -> a], AssociationThread[spc -> b]]
 ]


DyadExpression::usage = "DyadExpression has been renamed DyadForm."

DyadExpression[args__] := (
  Message[Q3General::renamed, "DyadExpression", "DyadForm"];
  DyadForm[args]
 )

(**** </DyadForm> ****)


(**** <Zero> ****)

Zero::usage = "Zero[n] return an array of length n with all elements zero.\nZero[m, n, ...] \[Congruent] Zero[{m, n, ...}] returns an m x n x ... tensor with all elements zero."

Zero[mn__Integer] := SparseArray[{}, {mn}]

Zero[{mn__Integer}] := SparseArray[{}, {mn}]

(**** </Zero> ****)


(**** <One> ****)

One::usage = "One[n] \[Congruent] One[{n}] is almost the same as IdentityMatrix[n], but returns the identity matrix in a sparse array.\nOne[m, n, ...] \[Congruent] One[{m, n}, ...] returns the m \[Times] n \[Times] ... pseudo-identity tensor, i.e., the tensor where the main diagonal elements are 1 and the other elements are all zero.\nOne[{m, n}, k] returns an m \[Times] n matrix with the elements on the \*SuperscriptBox[k,th] diagonal being 1 and zero elsewhere."

One[] := One @ {2, 2}

One[n_Integer] := One @ {n, n}

One[m_Integer, n__Integer] := One @ {m, n}

One[{n_Integer}] := One @ {n, n}

One[{m_Integer, n__Integer}] :=
  SparseArray[ ConstantArray[j_, Length @ {m, n}] -> 1, {m, n} ]

One[{n_Integer}, p_Integer] := One[{n, n}, p]

One[{m_Integer, n_Integer}, p_Integer] := 
  SparseArray[ {i_, j_} :> 1 /; j == i + p, {m, n} ]

(**** </One> ****)


(**** <PauliDecompose> ****)

PauliDecompose::usage = "PauliDecompose[mat] gives an Association of coefficients in the Pauli decomposition of 2^n\[Times]2^n matrix mat."

PauliDecompose::dim = "The dimensions `` of matrix `` is not integer powers of 2."

PauliDecompose[mat_?SquareMatrixQ] := Module[
  { n = Log[2, Length @ mat],
    trs },
  If[ Not[IntegerQ @ n],
    Message[PauliDecompose::dim, Dimensions @ mat, mat];
    Return[<||>]
   ];
  trs = SparseArray @ {
    {1, 0,  0,  1},
    {0, 1,  1,  0},
    {0, I, -I,  0},
    {1, 0,  0, -1}
   } / 2;
  trs = CircleTimes @@ Table[trs, n];
  KeyMap[(#-1)&] @ Association @ Most @ ArrayRules @ Chop @
    ArrayReshape[trs . Flatten[Tensorize @ mat], Table[4, n]]
 ]

PauliCompose::usage = "PauliCompose[assc] reconstructs the matrix using the Pauli decomposition coefficients given in Association assc."

PauliCompose[aa_Association] :=
  Total @ KeyValueMap[((ThePauli @@ #1) * #2)&, aa]


PauliVector::usage = "PauliVector[mat] returns the Pauli decomposition coefficients of 2\[Times]2 matrix mat."

PauliVector::dim = "`` is not a 2\[Times]2 matrix."

PauliVector @ {{a_, b_}, {c_, d_}} := {b+c, I*(b-c), a-d} / 2

PauliVector[mat_SparseArray] := PauliVector[Normal @ mat] /;
  Dimensions[mat] == {2, 2}

PauliVector[mat_] := (
  Message[PauliVector::dim, mat];
  {0, 0, 0}
 )

(**** </PauliDecompose> ****)


(**** <PauliDecomposeOld> ****)

PauliDecomposeOld::usage = "PauliDecomposeOld[m] gives the coefficients in the Pauli decomposition of m as a tensor of rank n, where m is a 2^n x 2^n matrix."

PauliDecomposeOld::dim = "The argument M of PauliDecomposeOld[M] should be a matrix of size 2^n*2^n."

PauliDecomposeOld[dd:(0|1|2|3)..][m_?MatrixQ] := PauliDecomposeOld[m, {dd}]

PauliDecomposeOld[dd:{(0|1|2|3)..}][m_?MatrixQ] := PauliDecomposeOld[m, dd]


PauliDecomposeOld[m_?MatrixQ, d:(0|1|2|3)] := PauliDecomposeOld[m, {d}]

PauliDecomposeOld[m_?MatrixQ, idx:{(0|1|2|3)..}] :=
  Tr @ Dot[m, CircleTimes @@ ThePauli /@ idx] / Length[m]


PauliDecomposeOld[mat_?SquareMatrixQ] := Module[
  { n = Log[2, Length @ mat],
    idx },
  If [ Not @ IntegerQ[n],
    Message[PauliDecomposeOld::dim];
    Return[0]
   ];
  idx = Tuples[{0, 1, 2, 3}, n];
  ArrayReshape[PauliDecomposeOld[mat, #]& /@ idx, Table[4, n]]
 ]


PauliComposeOld::usage = "PauliComposeOld[coeff] constructs a 2^n x 2^n matrix using the coefficients specified in the tensor coeff.\nIt is an inverse of PauliDecomposeOld and coeff is usually the tensor returned by it."

PauliComposeOld[c_?TensorQ] := Module[
  { n = TensorRank[c],
    indextable, indexlist, result = 0 },
  indextable = Table[ {{0},{1},{2},{3}}, {n} ];
  indexlist = Outer[ Join, Sequence @@ indextable, 1 ];
  indexlist = Flatten[ indexlist, TensorRank[indexlist]-2 ];
  For[ i=1, i<=Length[indexlist], i++,
    result += c[[ Sequence @@ (indexlist[[i]]+1) ]] *
      CircleTimes @@ ThePauli /@ indexlist[[i]]
   ];
  Return[result]
 ]

(**** </PauliDecomposeOld> ****)


(**** </PauliDecomposeRL> ****)

PauliDecomposeRL::usage = "PauliDecomposeRL[M], where M is a matrix of size 2^n*2^n, gives the coefficients of a Pauli decomposition of M as a tensor of rank n."

PauliDecomposeRL::badarg = "The argument M of PauliDecomposeRL[M] should be a matrix of size 2^n*2^n."

PauliDecomposeRL[dd:(0|3|4|5)..][m_?MatrixQ] := PauliDecomposeRL[m, {dd}]

PauliDecomposeRL[{dd:(0|3|4|5)..}][m_?MatrixQ] := PauliDecomposeRL[m, {dd}]


PauliDecomposeRL[M_?MatrixQ, n:(0|3|4|5)] := PauliDecomposeRL[M, {n}]

PauliDecomposeRL[M_?MatrixQ, idx:{(0|3|4|5)..}] := Module[
  { T },
  T[0] = ThePauli[0];
  T[3] = ThePauli[3];
  T[4] = ThePauli[5] * 2;
  T[5] = ThePauli[4] * 2;
  Tr @ Dot[ M, CircleTimes @@ T /@ idx ] / Length[M]
 ]


PauliDecomposeRL[mat_?MatrixQ] := Module[
  { n = Log[2, Length @ mat],
    idx },
  If [ !IntegerQ[n],
    Message[PauliDecompose::dim];
    Return[0]
   ];
  idx = Tuples[{0, 3, 4, 5}, n];
  ArrayReshape[PauliDecomposeRL[mat, #]& /@ idx, Table[4, n]]
 ]


PauliComposeRL::usage = "PauliComposeRL[coeff], where coeff is a tensor of rank n, gives a Pauli composed matrix of size 2^n*2^n with coefficients coeff."

PauliComposeRL[c_?TensorQ] := Module[
  { tiefe = TensorRank[c],
    indextable, indexlist, result = 0, T },
  indextable = Table[{{0}, {1}, {2}, {3}}, {tiefe}];
  indexlist = Outer[Join,Sequence@@indextable,1];
  indexlist = Flatten[indexlist,TensorRank[indexlist]-2];
  
  T[0] = ThePauli[0];
  T[1] = ThePauli[3];
  T[2] = ThePauli[4];
  T[3] = ThePauli[5];
  
  For[ i=1, i<=Length[indexlist], i++,
    result += c[[Sequence @@ (indexlist[[i]]+1)]] *
      CircleTimes @@ T /@ indexlist[[i]]
   ];
  result
 ]

(**** </PauliDecomposeRL> ****)


(**** <SchmidtDecomposition> ****)

SchmidtDecomposition::usage = "SchmidtDecomposition[v, {m, n}] returns the Schmidt decomposition of the pure state vector v of a bipartite system of dimensions m and n.\nSchmidtDecomposition[v, {d1, d2, ...}, {i1, i2, ...}, {j1, j2, ...}] returns the Schmidt decomposition of a pure state vector v for a system of multiple subsystems of dimensions d1, d2, .... The i1th, i2th, ... systems are grouped into one part and the j1th, j2th, ... subsystems are grouped into the other part."

SchmidtDecomposition::baddim = "Incompatible dimensions `1` x `2` for a vector of length `3`."

SchmidtDecomposition::badspec = "The specifications `2` and `3` for partitioning is not compatible with the expression `1` for a state vector of unlabelled qubits."

SchmidtDecomposition[v_?VectorQ] :=
  SchmidtDecomposition[v, {Length[v]/2, 2}]

SchmidtDecomposition[v_?VectorQ, n_Integer] :=
  SchmidtDecomposition[v, {Length[v]/n, n}]

SchmidtDecomposition[v_?VectorQ, {n_Integer, Automatic}] :=
  SchmidtDecomposition[v, {n, Length[v]/n}]

SchmidtDecomposition[vec_?VectorQ, {m_Integer, n_Integer}] := Module[
  { mn = Min[m, n],
    uu, ww, vv },
  { uu, ww, vv } = SingularValueDecomposition @ Partition[vec, n];
  { Diagonal @ ww,
    Take[ Transpose @ uu, mn ],
    Take[ ConjugateTranspose @ vv, mn ]
   }
 ] /; Length[vec] == m*n

SchmidtDecomposition[vec_?VectorQ, {m_Integer, n_Integer}] := (
  Message[SchmidtDecomposition::baddim, m, n, Length @ v];
  {{1}, vec, {1}}
 )

SchmidtDecomposition[v_?VectorQ, ii:{__Integer}, jj:{__Integer}] :=
  SchmidtDecomposition[v, ConstantArray[2, Length[ii]+Length[jj]], ii, jj]

SchmidtDecomposition[
  v_?VectorQ, dd:{__Integer}, ii:{__Integer}, jj:{__Integer}
 ] := Module[
   { mat = Tensorize[v, dd],
     tsr },
   tsr = Flatten @ Transpose[mat, Ordering @ Join[ii, jj]];
   SchmidtDecomposition[ tsr, Times @@@ { Part[dd, ii], Part[dd, jj] } ]
  ]


SchmidtDecomposition[expr_, aa:{__Integer}, bb:{__Integer}] := Module[
  { nn = Length @ First @ Cases[{expr}, _Ket, Infinity],
    ww, uu, vv },
  If[ nn == Length[aa] + Length[bb], Null,
    Message[SchmidtDecomposition::badspec, expr, aa, bb];
    Return @ {{1}, expr, {1}}
   ];
  
  {ww, uu, vv} = SchmidtDecomposition[
    Matrix[expr],
    ConstantArray[2, Length[aa] + Length[bb]],
    aa, bb
   ];
  { ww, ExpressionFor /@ uu, ExpressionFor /@ vv }
 ] /; fPauliKetQ[expr]


SchmidtDecomposition[expr_, a_?SpeciesQ, b_?SpeciesQ] := 
  SchmidtDecomposition[expr, {a}, {b}]

SchmidtDecomposition[expr_, a_?SpeciesQ, bb:{__?SpeciesQ}] := 
  SchmidtDecomposition[expr, {a}, bb]

SchmidtDecomposition[expr_, aa:{__?SpeciesQ}, b_?SpeciesQ] :=
  SchmidtDecomposition[expr, aa, {b}]

SchmidtDecomposition[expr_, aa:{__?SpeciesQ}, bb:{__?SpeciesQ}] := Module[
  { ab = FlavorNone @ Join[aa, bb],
    ww, uu, vv },
  { ww, uu, vv } = SchmidtDecomposition[
    Matrix[expr, ab],
    { Times @@ Dimension[aa], Times @@ Dimension[bb] }
   ];
  { ww, uu . Basis[aa], vv . Basis[bb] }
 ] /; fKetQ[expr]


SchmidtForm::usage = "SchmidtForm[\[Ellipsis]] is formally equivalent to SchmidtDecomposition[\[Ellipsis]], but returns the result in the form s1 Ket[u1]\[CircleTimes]Ket[v1] + s2 Ket[u2]\[CircleTimes]Ket[v2] + \[Ellipsis] keeping \[CircleTimes] unevaluated.\nSchmidtForm is for a quick overview of the Schmidt decomposition of the vector in question. For a more thorough analysis of the result, use SchmidtDecomposition."

SchmidtForm[vec_?VectorQ] :=
  SchmidtForm[vec, {Length[vec]/2, 2}]

SchmidtForm[vec_?VectorQ, n_Integer] :=
  SchmidtForm[vec, {Length[vec]/n, n}]

SchmidtForm[vec_?VectorQ, {n_Integer, Automatic}] :=
  SchmidtForm[vec, {n, Length[vec]/n}]

SchmidtForm[vec_?VectorQ, {m_Integer, n_Integer}] := Module[
  { ww, uu, vv },
  { ww, uu, vv } = SchmidtDecomposition[vec, {m, n}];
  ww . MapThread[OTimes, {uu . Basis @ {m}, vv . Basis @ {n}}]
 ]

SchmidtForm[vec_?VectorQ, ii:{__Integer}, jj:{__Integer}] :=
  SchmidtForm[vec, ConstantArray[2, Length[ii]+Length[jj]], ii, jj]

SchmidtForm[
  vec_?VectorQ, dd:{__Integer}, ii:{__Integer}, jj:{__Integer}
 ] := Module[
   { ww, uu, vv },
   { ww, uu, vv } = SchmidtDecomposition[vec, dd, ii, jj];
   ww . MapThread[
     OTimes,
     { uu . Basis @ Part[dd, ii],
       vv . Basis @ Part[dd, jj]
      }
    ]
  ]

SchmidtForm[expr_, aa:{__Integer}, bb:{__Integer}] := Module[
  { ww, uu, vv },
  { ww, uu, vv } = SchmidtDecomposition[expr, aa, bb];
  ww . MapThread[OTimes, {uu, vv}]
 ] /; fPauliKetQ[expr]


SchmidtForm[expr_, a_?SpeciesQ, b_?SpeciesQ] := 
  SchmidtForm[expr, {a}, {b}]

SchmidtForm[expr_, a_?SpeciesQ, bb:{__?SpeciesQ}] := 
  SchmidtForm[expr, {a}, bb]

SchmidtForm[expr_, aa:{__?SpeciesQ}, b_?SpeciesQ] :=
  SchmidtForm[expr, aa, {b}]

SchmidtForm[expr_, aa:{__?SpeciesQ}, bb:{__?SpeciesQ}] := Module[
  { ww, uu, vv },
  { ww, uu, vv } = SchmidtDecomposition[expr, aa, bb];
  ww . MapThread[ OTimes, {KetRegulate[uu, aa], KetRegulate[vv, bb]} ]
 ] /; fKetQ[expr]

(**** </SchmidtDecomposition> ****)


(**** <Tensorize> ****)

TensorFlatten::usage = "TensorFlatten[tsr] flattens out the given tensor tsr to a matrix and returns it.\nIt generalizes ArrayFlatten and operates on tensors of any rank.\nTo flatten out a tensor to a vector (rather than a matrix), just use Flatten."

TensorFlatten[t_?TensorQ] := With[
  { r = TensorRank[t] },
  Flatten[t, {Range[1,r,2], Range[2,r,2]}]
 ]

TensorFlatten[c:Except[_List]] := c


Tensorize::usage = "Tensorize[m] gives the tensor product form of the matrix m. The matrix m is supposed to be the matrix representation of a multi-qubit system and hence a square matrix of size 2^n, where n is the number of qubits.\nTensorize[v] gives the tensor product form of the vector v. The vector v is supposed to be the matrix representation of a multi-qubit system and hence a column vector of size 2^n.\nTensorize[m, dim] and Tensor[v, dim] are the same but for general subsystems of dimensions dim.\nNotice the difference between TensorProduct and CircleTimes. While TensorProduct preseves the tensor product form (in blocks), CircleTimes gives the matrix direct product with component blocks flattened. In fact, CircleTimes = Flatten @ TensorProdut for vectors and CircleTimes = TensorFlatten @ TensorProduct for matrices. Tensorize recovers the tensor product form from the matrix direct product form."

Tensorize::badShape = "The dimenion(s) `` of the matrix is (are) not compatible with the subdimensions ``."

Tensorize::notQubit = "The input array should be either a (2^n)\[Times](2^n) square matrix or a vector of length 2^n."

Tensorize[m_?MatrixQ, dim:{__Integer}] := Module[
  { r = Length[dim],
    oo = dim[[1;; ;;2]],
    ee = dim[[2;; ;;2]],
    ll = Dimensions[m], ii },
  If[ ll != {Times @@ oo, Times @@ ee},
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
  If[ l != Times @@ dim,
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


(**** <PartialTranspose> ****)

PartialTranspose::usage = "PartialTranspose[mat, {i, j, \[Ellipsis]}] returns the partial transposition of the matrix mat with respect to the ith, jth, \[Ellipsis] qubits.\nPartialTranspose[mat, {m, n, \[Ellipsis]}, {i, j, \[Ellipsis]}] assumes subsystems of dimensions m, n, \[Ellipsis].\nPartialTranspose[expr, {s1, s2, \[Ellipsis]}] considers subsystems for the species {s1, s2, \[Ellipsis]}."

PartialTranspose[vec_?VectorQ, dd:{__Integer}, jj:{___Integer}] :=
  PartialTranspose[Dyad[vec, vec], dd, jj]

PartialTranspose[mat_?MatrixQ, dd:{__Integer}, jj:{___Integer}] := Module[
  { tns = Tensorize[mat, Flatten @ Transpose @ {dd, dd}],
    cyc = Cycles @ Transpose @ {2*jj-1, 2*jj} },
  TensorFlatten @ Transpose[tns, cyc]
 ]

PartialTranspose[rho:(_?VectorQ|_?MatrixQ), jj:{___Integer}] :=
  PartialTranspose[rho, ConstantArray[2, Log[2, Length @ rho]], jj]


PartialTranspose[expr_, jj:{__Integer}] :=
  ExpressionFor @ PartialTranspose[Matrix @ expr, jj] /;
  Or[fPauliKetQ[rho], Not @ FreeQ[expr, _Pauli]]


PartialTranspose[expr_, S_?SpeciesQ] := PartialTranspose[expr, {S}]

PartialTranspose[expr_, qq:{__?SpeciesQ}] := Module[
  { rr = FlavorNone @ Cases[qq, _?NonCommutativeQ],
    ss = Agents[expr],
    dd, jj, mm },
  ss = Union[ss, rr];
  dd = Dimension[ss];
  jj = Flatten @ Map[FirstPosition[ss, #]&, rr];
  mm = PartialTranspose[Matrix[expr, ss], dd, jj];
  ExpressionFor[mm, ss]
 ]

(**** </PartialTranspose> ****)


(**** <Negativity> ****)

Negativity::usage = "Negativity[rho, spec] returns the negativity of quantum state rho.\nFor specification spec of the rest of the arguments, see PartialTranspose."

Negativity::norm = "`` is not properly normalized: trace = ``."

Negativity[vec_?VectorQ, spec__] := (
  If[ Rationalize[Norm @ vec] != 1,
    Message[Negativity::norm, vec, Rationalize @ Norm @ vec]
   ];
  (NormPT[vec, spec] - 1) / 2
 )

Negativity[mat_?MatrixQ, spec__] := (
  If[ Rationalize[Tr @ mat] != 1,
    Message[Negativity::norm, mat, Rationalize @ Tr @ mat]
   ];
  (NormPT[mat, spec] - 1) / 2
 )

Negativity[rho_, spec_] := (NormPT[rho, spec] - 1) / 2


Negativity[rho_, aa:{__?SpeciesQ}, bb:{__?SpeciesQ}] := Module[
  { all, mat, pos },
  all = Union @ FlavorNone @ Join[aa, bb];
  pos = Flatten @ Map[FirstPosition[all, #]&, FlavorNone @ bb];

  mat = Matrix[rho, all];
  Negativity[mat, Dimension @ all, pos]
 ]

Negativity[rho_, S_?SpeciesQ, bb:{__?SpeciesQ}] :=
  Negativity[rho, {S}, bb]

Negativity[rho_, aa:{__?SpeciesQ}, T_?SpeciesQ] :=
  Negativity[rho, aa, {T}]

Negativity[rho_, S_?SpeciesQ, T_?SpeciesQ] :=
  Negativity[rho, {S}, {T}]

(**** </Negativity> ****)


(**** <LogarithmicNegativity> ****)

LogarithmicNegativity::usage = "LogarithmicNegativity[rho, spec] returns the logarithmic negativity of quantum state rho.\nFor specification spec of the rest of the arguments, see PartialTranspose."

LogarithmicNegativity::norm = "`` is not properly normalized: trace = ``."

LogarithmicNegativity[vec_?VectorQ, spec__] := (
  If[ Rationalize[Norm @ vec] != 1,
    Message[LogarithmicNegativity::norm, vec, Rationalize @ Norm @ vec]
   ];
  Log2 @ NormPT[vec, spec]
 )

LogarithmicNegativity[mat_?MatrixQ, spec__] := (
  If[ Rationalize[Tr @ mat] != 1,
    Message[LogarithmicNegativity::norm, mat, Rationalize @ Tr @ mat]
   ];
  Log2 @ NormPT[mat, spec]
 )

LogarithmicNegativity[rho_, spec_] := Log2 @ NormPT[rho, spec]


LogarithmicNegativity[rho_, aa:{__?SpeciesQ}, bb:{__?SpeciesQ}] := Module[
  { all, mat, pos },
  all = Union @ FlavorNone @ Join[aa, bb];
  pos = Flatten @ Map[FirstPosition[all, #]&, FlavorNone @ bb];

  mat = Matrix[rho, all];
  LogarithmicNegativity[mat, Dimension @ all, pos]
 ]

LogarithmicNegativity[rho_, S_?SpeciesQ, bb:{__?SpeciesQ}] :=
  LogarithmicNegativity[rho, {S}, bb]

LogarithmicNegativity[rho_, aa:{__?SpeciesQ}, T_?SpeciesQ] :=
  LogarithmicNegativity[rho, aa, {T}]

LogarithmicNegativity[rho_, S_?SpeciesQ, T_?SpeciesQ] :=
  LogarithmicNegativity[rho, {S}, {T}]

(**** </LogarithmicNegativity> ****)


(**** <NormPT> ****)

NormPT::usage = "NormPT[rho, spec] returns the trace norm of the partial transpose of rho, where the partial transposition is specified by spec (see PartialTranspose)."

NormPT::traceless = "`` is traceless."

NormPT[vec_?VectorQ, spec__] := TraceNorm @ PartialTranspose[vec, spec]

NormPT[mat_?MatrixQ, spec__] := TraceNorm @ PartialTranspose[mat, spec]


NormPT[rho_, jj:{__Integer}] := NormPT[Matrix @ rho, jj] /;
  Or[fPauliKetQ[rho], Not @ FreeQ[expr, _Pauli]]


NormPT[rho_, qq:{__?SpeciesQ}] := Module[
  { rr = FlavorNone @ Cases[qq, _?NonCommutativeQ],
    ss = Agents[rho],
    all, pos, mat, trm },
  all = Union @ FlavorNone @ Join[rr, ss];
  pos = Flatten @ Map[FirstPosition[all, #]&, FlavorNone @ rr];
  mat = Matrix[rho, all];

  trm = If[MatrixQ[mat], Tr[mat], Norm[mat]^2];
  If[Chop[trm] == 0, Message[NormPT::traceless, rho]; Return[1]];
  
  NormPT[mat, Dimension @ all, pos] / trm
 ]
(* NOTE: rho is assumed to be properly normalized; and hence the factor ofr
   1/trm in the code. *)


NormPT[rho_, aa:{__?SpeciesQ}, bb:{__?SpeciesQ}] := Module[
  { all, pos, mat },
  all = Union @ FlavorNone @ Join[aa, bb];
  pos = Flatten @ Map[FirstPosition[all, #]&, FlavorNone @ bb];

  mat = Matrix[rho, all];
  NormPT[mat, Dimension @ all, pos]
 ]
(* NOTE 1: For PartialTransposition, argument aa is not necessary. However, it
   is necessary for proper normalization. For example, consider rho = I x I /
   4. Without aa, it may be regarded as I / 4, which leads to a wrong value of
   the logarithmic negativity. *)
(* NOTE 2: rho may refer to a pure state; i.e., mat may be a vector. *)

NormPT[rho_, S_?SpeciesQ] := NormPT[rho, {S}]

NormPT[rho_, S_?SpeciesQ, bb:{__?SpeciesQ}] := NormPT[rho, {S}, bb]

NormPT[rho_, aa:{__?SpeciesQ}, T_?SpeciesQ] := NormPT[rho, aa, {T}]

NormPT[rho_, S_?SpeciesQ, T_?SpeciesQ] := NormPT[rho, {S}, {T}]

(**** </NormPT> ****)


(**** <PartialTrace> ****)

PartialTrace::usage = "PartialTrace[m, {i,j,...}] takes the partial trace over the qubits i, j, ... and returns the resulting reduced matrix.\nPartialTrace[m, {m,n,...}, {i,j,...}] assumes a system of dimensions m, n, ..., takes the partial trace over the subsystems i, j, ..., and returns the resulting reduced matrix.\nPartialTrace[v, {i,j,...}] and PartialTrace[v, {m,n,...}, {i,j,...}] are the same but operate on the column vector v. Note that the result is a square matrix, i.e., the reduced density matrix, not a pure-state column vector any longer."

PartialTrace::nosubsys = "Some element of `` is not a subsystem."

PartialTrace[m_?MatrixQ, dd:{__Integer}, jj:{___Integer}] := Module[
  { M = Tensorize[m, Flatten @ Transpose @ {dd, dd}] },
  If[ !ContainsOnly[jj, Range @ Length[dd]],
    Message[PartialTrace::nosubsys, jj];
    Return[m]
   ];
  TensorFlatten @ TensorContract[ M, Transpose @ {2jj-1, 2jj} ]
 ]

PartialTrace[m_?MatrixQ, jj:{___Integer}] :=
  PartialTrace[m, ConstantArray[2, Log[2, Length[m]]], jj]

PartialTrace[v_?VectorQ, dd:{__Integer}, {}] :=
  KroneckerProduct[v, Conjugate[v]]

PartialTrace[v_?VectorQ, dd:{__Integer}, jj:{__Integer}] := Module[
  { nn = Range @ Length @ dd,
    ii },
  If[ Not @ ContainsOnly[jj, nn],
    Message[PartialTrace::nosubsys, jj];
    Return @ Dyad[v, v]
   ];
  ii = Supplement[nn, jj];
  If[ ii == {},
    Norm[v]^2,
    Total @ Map[Dyad[#, #]&, Flatten[Tensorize[v, dd], {jj, ii}]]
   ]
 ]
(* REMARK: In many cases, handling density matrix is computationally
   inefficient. In this sense, returning the list of states involved in the
   mixed state may provide the user with more flexibility. *)

PartialTrace[v_?VectorQ, {}] := KroneckerProduct[v, Conjugate[v]]

PartialTrace[v_?VectorQ, jj:{__Integer}] :=
  PartialTrace[v, ConstantArray[2, Log[2, Length @ v]], jj]


(* For unlabelled qubits *)
PartialTrace[expr_, jj:{___Integer}] := Module[
  { vec = Matrix[expr] },
  ExpressionFor @ PartialTrace[vec, jj]
 ] /; Or[fPauliKetQ @ expr, Not @ FreeQ[expr, _Pauli]]


PartialTrace[expr_, S_?SpeciesQ] := PartialTrace[expr, {S}]

PartialTrace[expr_, ss:{__?SpeciesQ}] := With[
  { tt = FlavorNone[ss] },
  PartialTrace[expr, Union[Agents @ expr, tt], tt]
 ]

PartialTrace[expr_, qq:{__?SpeciesQ}, S_?SpeciesQ] :=
  PartialTrace[expr, qq, {S}]

PartialTrace[expr_, qq:{__?SpeciesQ}, ss:{__?SpeciesQ}] := Module[
  { bb = FlavorNone @ Cases[ss, _?NonCommutativeQ],
    aa, dd, jj, mm },
  aa = Agents @ {expr, FlavorNone @ qq};
  If[Not @ ContainsOnly[bb, aa], Message[PartialTrace::nosubsys, bb]];
  dd = Dimension[aa];
  jj = Flatten @ Map[FirstPosition[aa, #]&, bb];
  mm = PartialTrace[Matrix[expr, aa], dd, jj];
  aa = Complement[aa, bb];
  If[ aa == {},
    Return[mm],
    ExpressionFor[mm, aa]
   ]
 ]
(* NOTE: This form is essential, e.g., for
   PartialTrace[Ket[], S@{1,2}, S@{2}] *)

(**** </PartialTrace> ****)


(**** <ReducedMatrix> ****)

ReducedMatrix::usage = "ReducedMatrix[vec|mat, {d1, d2, \[Ellipsis]}, {k1, k2, \[Ellipsis]}] returns the reduced matrix from 'vec' or 'mat' after tracing out the subsystems other than k1, k2, \[Ellipsis]. The subsystems are assumed to be associated with the Hilbert spaces with dimensions d1, d2, \[Ellipsis].\nReducedMatrix[vec|mat, {k1, k2, \[Ellipsis]}] assumes that the subsystems are qubits.\nReducedMatrix[expr, {k1, k2, \[Ellipsis]}] assumes that 'expr' is an ket or operator expression for unlabelled qubits k1, k2, \[Ellipsis].\nReducedMatrix[expr, {s1, s2, \[Ellipsis]}] assumes subsystems specified by the species {s1, s2, \[Ellipsis]}."

ReducedMatrix::noqubit = "`` does not seem to be a vector or matrix for qubits."

ReducedMatrix[rho:(_?VectorQ|_?MatrixQ), dd:{__Integer}, jj:{__Integer}] :=
  PartialTrace[rho, dd, Complement[Range[Length @ dd], jj]]

ReducedMatrix[rho:(_?VectorQ|_?MatrixQ), jj:{__Integer}] := (
  Message[ReducedMatrix::noqubit, rho];
  rho
 ) /; Not @ IntegerQ @ Log[2, Length @ rho]

ReducedMatrix[rho:(_?VectorQ|_?MatrixQ), jj:{__Integer}] :=
  ReducedMatrix[rho, ConstantArray[2, Log[2, Length @ rho]], jj]


ReducedMatrix[expr_, S_?SpeciesQ] := ReducedMatrix[expr, {S}]

ReducedMatrix[expr_, ss:{__?SpeciesQ}] := Module[
  { qq = Agents[expr],
    rr = FlavorNone @ Select[ss, NonCommutativeQ],
    jj },
  qq = Union[qq, rr];
  jj = Flatten @ Map[FirstPosition[qq, #]&, Complement[qq, rr]];
  PartialTrace[Matrix[expr, qq], Dimension[qq], jj]
 ]


ReducedMatrix[expr_, jj:{__Integer}] := Module[
  { nn = Length @ FirstCase[expr, _Ket, Infinity] },
  PartialTrace[Matrix[expr], Complement[Range @ nn, jj]]
 ] /; fPauliKetQ[expr]

ReducedMatrix[expr_, jj:{__Integer}] := Module[
  { nn = Length @ FirstCase[expr, _Pauli, Infinity] },
  PartialTrace[Matrix[expr], Complement[Range @ nn, jj]]
 ] /; Not @ FreeQ[expr, _Pauli]


Reduced::usage = "Reduced[vec|mat, \[Ellipsis]] is equivalent to ReducedMatrix[vec|mat, \[Ellipsis]].\nReduced[expr, {k1, k2, \[Ellipsis]}] returns the reduced operator in terms of the Pauli operators on unlabelled qubits {k1, k2, \[Ellipsis]}.\nReduced[expr, {s1, s2, \[Ellipsis]}] returns the reduced operator acting on the species {s1, s2, \[Ellipsis]}."

Reduced[rho:(_?VectorQ|_?MatrixQ), rest__] := ReducedMatrix[rho, rest]


Reduced[expr_, S_?SpeciesQ] := Reduced[expr, {S}]

Reduced[expr_, ss:{__?SpeciesQ}] :=
  ExpressionFor[ReducedMatrix[expr, ss], Select[ss, NonCommutativeQ]]


Reduced[expr_, jj:{__Integer}] := 
  ExpressionFor[ReducedMatrix[expr, jj]] /;
  Or[fPauliKetQ @ expr, Not @ FreeQ[expr, _Pauli]]

(**** </ReducedMatrix> ****)


(**** <Purification> ****)

Purification::usage = "Purification[m] returns the purification of the mixed state m."

Purification[mat_?MatrixQ] := Module[
  {val, vec},
  {val, vec} = Eigensystem[mat];
  If[ AllTrue[Flatten @ vec, NumericQ] && Not[UnitaryMatrixQ @ vec],
    vec = Orthogonalize[vec]
   ];
  Sqrt[val] . MapThread[CircleTimes, {vec, One @ Dimensions @ mat}]
 ]
(* NOTE: mat is supposed to be Hermitian. *)
(* NOTE: Normalize is necessary because Eigensystem does not give the
   normalized eigenvectors for a matrix of exact numbers. *)

Purification[rho_, ss:{__?SpeciesQ}, rr:{__?SpeciesQ}] :=
  ExpressionFor[Purification @ Matrix[rho, ss], Join[ss, rr]]

Purification[rho_, S_?SpeciesQ, rr:{__?SpeciesQ}] :=
  Purification[rho, {S}, rr]

Purification[rho_, ss:{__?SpeciesQ}, R_?SpeciesQ] :=
  Purification[rho, ss, {R}]

Purification[rho_, S_?SpeciesQ, R_?SpeciesQ] :=
  Purification[rho, {S}, {R}]

Purification[rho_, ss:{__?SpeciesQ}] := Purification @ Matrix[rho, ss]

Purification[rho_, S_?SpeciesQ] := Purification[rho, FlavorNone @ {S}]

Purification[rho_] := With[
  { ss = Agents[rho] },
  Purification[rho, ss]
 ] /; FreeQ[rho, _Pauli]

Purification[rho_] := ExpressionFor @ Purification @ Matrix[rho] /;
  Not @ FreeQ[rho, _Pauli]

Purification[z_?CommutativeQ] := ExpressionFor @ Purification[z*One[2]]
(* NOTE: Single qubit is assumed. *)

(**** </Purification> ****)


Snapping::usage = "Snapping[m] returns the pure state closest to the mixed state m.\nIt is different from purification."

Snapping[m_?MatrixQ] := Module[
  {val, vec},
  {val, vec} = Eigensystem[m]; (* m is suppposed to be Hermitian. *)
  {val, vec} = Last @ Sort @ Transpose @ {val, vec};
  (* returns the eigenvector belonging to the largest eigenvalue *)
  vec
 ]


(**** <MatrixEmbed> ****)

MatrixEmbed::usage = "MatrixEmbed[mat, {s1,s2,\[Ellipsis]}, {t1,t2,\[Ellipsis]}] returns the fully-expanded form of matrix mat that acts on the entire tensor-product space of species {t1,t2,\[Ellipsis]}, where mat represents a linear operator on the Hilbert space of species {s1,s2,\[Ellipsis]}\[Subset]{t1,t2,\[Ellipsis]}."

MatrixEmbed::rmdr = "`` is not entirely contained in ``."

MatrixEmbed[mat_?MatrixQ, ss:{__?SpeciesQ}, tt:{__?SpeciesQ}] :=
  MatrixEmbed[mat, FlavorNone @ ss, FlavorNone @ tt] /;
  Not[FlavorNoneQ @ Join[ss, tt]]

MatrixEmbed[mat_?MatrixQ, ss:{__?SpeciesQ}, tt:{__?SpeciesQ}] := Module[
  { rmd = Complement[tt, ss],
    new, jdx },
  new = CircleTimes[mat, One[Times @@ Dimension @ rmd]];
  jdx = PermutationList @ FindPermutation[Join[ss, rmd], tt];
  TensorFlatten @ Transpose[
    Tensorize[new, Riffle @@ Table[Dimension @ Join[ss, rmd], 2]],
    Riffle[2*jdx - 1, 2*jdx]
   ]
 ] /; ContainsAll[tt, ss]

MatrixEmbed[mat_?MatrixQ, ss:{__?SpeciesQ}, tt:{__?SpeciesQ}] :=
  Message[MatrixEmbed::rmdr, ss, tt]


MatrixEmbed[mat_?MatrixQ, kk:{__Integer}, n_Integer] :=
  MatrixEmbed[mat, kk, Table[2, n]]

MatrixEmbed[mat_?MatrixQ, kk:{__Integer}, dd:{__Integer}] := Module[
  { all = Range @ Length @ dd,
    rmd, new, jdx },
  rmd = Complement[all, kk];
  new = CircleTimes[mat, One[Times @@ Part[dd, rmd]]];
  jdx = PermutationList @ FindPermutation[Join[kk, rmd], all];
  TensorFlatten @ Transpose[
    Tensorize[new, Riffle @@ Table[Part[dd, Join[kk, rmd]], 2]],
    Riffle[2*jdx - 1, 2*jdx]
   ]
 ] /; And @@ Thread[kk <= Length[dd]]


PauliEmbed::usage = "PauliEmbed is obsolete; instead, use MatrixEmbed."

PauliEmbed[args___] := (
  Message[Q3General::obsolete, "PauliEmbed", "MatrixEmbed"];
  MatrixEmbed[args]
 )

PauliApply[args___] := Message[Q3General::excised, "PauliApply"]
  
(**** </MatrixEmbed> ****)


RandomVector::usage = "RandomVector is a shortcut to RandomComplex.\nRandomVector[] gives a two-dimensional random vector.\nRanbdomVector[n] gives an n-dimensional random vector.\nRandomVector[range, n] \[Congruent] RandomComplex[range, n]."

RandomVector[] := RandomComplex[(1+I){-1, 1}, 2]

RandomVector[n_Integer] := RandomComplex[(1+I){-1, 1}, n]

RandomVector[range_, n_Integer] := RandomComplex[range, n]


RandomMatrix::usage = "RandomMatrix is a shortcut to RandomComplex.\nRandomMatrix[] returns a randomly generated 2\[Times]2 matrix.\nRanbdomMatrix[n] returns an n\[Times]n random matrix.\nRandomMatrix[range, n] \[Congruent] RandomComplex[range, {n, n}].\nRandomMatrix[range, {m, n}] \[Congruent] RandomComplex[range, {m, n}]."

RandomMatrix[] := RandomComplex[(1+I){-1, 1}, {2, 2}]

RandomMatrix[n_Integer] := RandomComplex[(1+I){-1, 1}, {n, n}]

RandomMatrix[mn:{_Integer, _Integer}] := RandomComplex[(1+I){-1, 1}, mn]

RandomMatrix[range_, n_Integer] := RandomComplex[range, {n, n}]

RandomMatrix[range_, mn:{_Integer, _Integer}] := RandomComplex[range, mn]


RandomHermitian::usage = "RandomHermitian[n] gives a randomly generated n\[Times]n Hermitian matrix with each element in the range between -(1+I) and (1+I).\nRandomHermitian[] assumes n=2.\nRandomHermitian[range, n] gives a randomly generated n\[Times]n Hermitian matrix. The range specifies the range (see RandomComplex) of the elements."

RandomHermitian[] := RandomHermitian[(1+I){-1, 1}, 2]

RandomHermitian[n_Integer] := RandomHermitian[(1+I){-1, 1}, n]

RandomHermitian[range_, n_Integer] := With[
  { m = RandomComplex[range, {n, n}] },
  ( m + ConjugateTranspose[m] ) / 2
 ]

RandomPositive::usage = "RandomPositive[n] gives a randomly generated n\[Times]n positive matrix with each element in the range between -(1+I) and (1+I).\nRandomPositive[] assumes n=2.\nRandomPositive[range, n] gives a random  positive matrix with each element in the specified 'range' (see RandomComplex for the details of the specification of range)."

RandomPositive[] := RandomPositive[(1+I){-1, 1}, 2]

RandomPositive[n_Integer] := RandomPositive[(1+I){-1, 1}, n]

RandomPositive[range_, n_Integer] := With[
  { m = RandomMatrix[range, {n, n}] },
  Topple[m].m
 ]

RandomUnitary::usage = "RandomUnitary[n] gives a randomly generated n x n Unitary matrix. The range specifies the range (see RandomComplex) of the elements."

RandomUnitary[] := RandomUnitary[2]

RandomUnitary[n_Integer] := With[
  { H = RandomHermitian[(1+I){-1,1}, n] (2 Pi / Sqrt[2]) },
  MatrixExp[-I H]
 ]


(**** <BasisComplement> *****)

svdBasisComplement::usage = "svdBasisComplement[{v1,v2,\[Ellipsis]}, {w1,w2,\[Ellipsis]}] returns a new basis of the subspace W\[UpTee]\[Subset]\[ScriptCapitalV] that is orgohtonal to \[ScriptCapitalW], where \[ScriptCapitalV] is the vector space spanned by the basis {v1,v2,\[Ellipsis]}, and \[ScriptCapitalW] is a subspace of \[ScriptCapitalV] spanned by the basis {w1,w2,\[Ellipsis]}."

svdBasisComplement[aa_?MatrixQ, bb_?MatrixQ] := Module[
  { aaa = SparseArray @ aa,
    mat = Orthogonalize[SparseArray @ bb],
    any, val, new },
  new = aaa - aaa.Topple[mat].mat;
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
  
  new = aaa - aaa.Topple[mat].mat;
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


WignerFunction::usage = "WignerFunction is now obsolete; use the build-in WignerD function."

WignerFunction[j_, m_, n_, z_] := (
  Message[Q3General::obsolete, WignerFunction, WignerD];
  WignerD[{j, m, n}, z]
 )


(**** <HilbertSchmidtNorm> *****)

FrobeniusNorm::usage = "FrobeniusNorm is an alias to HilbertSchmidtNorm."

FrobeniusNorm = HilbertSchmidtNorm

HilbertSchmidtNorm::usage = "HilbertSchmidtNorm[a] gives the Hilbert-Schmidt norm (i.e., Frobenius norm) of a complex matrix a.\nIf a is a vector, it is regarded as Dyad[a,a].\nSee also TraceNorm."

Format[ HilbertSchmidtNorm[a_] ] :=
  Interpretation[Sqrt @ AngleBracket[a, a], HilbertSchmidtNorm @ a]

HilbertSchmidtNorm[a_?VectorQ] := Norm[a]^2

HilbertSchmidtNorm[a_?MatrixQ] := Norm[a, "Frobenius"]

HilbertSchmidtNorm[rho_] := HilbertSchmidtNorm @ Matrix[rho]

HilbertSchmidtNorm[rho_, q_?SpeciesQ] := HilbertSchmidtNorm[rho, {q}]

HilbertSchmidtNorm[rho_, qq:{__?SpeciesQ}] :=
  HilbertSchmidtNorm @ Matrix[rho, qq]


HilbertSchmidtDistance::usage = "HilbertSchmidtDistance[a, b] returns the Hilbert-Schmidt distance of two (pure or mixed) states a and b. It is equivalent to HilbertSchmidtNorm[a-b]."

HilbertSchmidtDistance[a_, b_] := HilbertSchmidtNorm[a - b]


FrobeniusProduct::usage = "FrobeniusProduct is an alias to HilbertSchmidtProduct."

FrobeniusProduct = HilbertSchmidtProduct

HilbertSchmidtProduct::usage = "HilbertSchmidtProduct[a, b] returns the Hilbert-Schmidt (or Frobenius) inner product of two matrices a and b, that is, Tr[ConjugateTranspose[a].b].\nIf a is a vector, it is regarded as Dyad[a,a], and similary for b."

HilbertSchmidtProduct::incmp = "Two matrix `1` and `2` are not compatible for the Hilbert-Schmidt inner product."

HilbertSchmidtProduct[a_?MatrixQ, b_?MatrixQ] := (
  Message[HilbertSchmidtProduct::incmp, a, b];
  Return[0]
 )

HilbertSchmidtProduct[a_?MatrixQ, b_?MatrixQ] := Tr[Topple[a].b] /;
  ArrayQ[{a, b}]

HilbertSchmidtProduct[a_?VectorQ, b_?MatrixQ] := Conjugate[a].b.a

HilbertSchmidtProduct[a_?MatrixQ, b_?VectorQ] := Conjugate[a].Topple[b].a

HilbertSchmidtProduct[a_?VectorQ, b_?VectorQ] := Abs[Conjugate[a].b]^2


HilbertSchmidtProduct[a_, b_] := With[
  { ss = Agents @ {a, b} },
  HilbertSchmidtProduct[a, b, ss]
 ]


HilbertSchmidtProduct[S_?SpeciesQ] :=
  HilbertSchmidtProduct[FlavorNone @ {S}]

HilbertSchmidtProduct[ss:{___?SpeciesQ}] :=
  HilbertSchmidtProduct[FlavorNone @ ss] /; Not[FlavorNoneQ @ ss]

HilbertSchmidtProduct[ss:{___?SpeciesQ}][a_, b_] :=
  HilbertSchmidtProduct[a, b, ss]

HilbertSchmidtProduct[a_, b_, ss:{___?SpeciesQ}] :=
  HilbertSchmidtProduct[Matrix[a, ss], Matrix[b, ss]]

(**** </HilbertSchmidtNorm> *****)


(**** <TraceNorm> *****)

TraceNorm::usage = "TraceNorm[m] returns the trace norm of the matrix m, that is, Tr @ Sqrt[Dagger[m] ** m].\nTraceNorm[v] gives TraceNorm[v.Transepose[v]].\nTraceNorma[expr, {s1, s2, \[Ellipsis]}] returns the trace norm of operator expression expr acting on species s1, s2, \[Ellipsis]."

TraceNorm[m_?MatrixQ] := Total @ SingularValueList[m]

TraceNorm[v_?VectorQ] := Norm[v]^2


TraceNorm[rho_] := TraceNorm @ Matrix[rho]

TraceNorm[rho_, q_?SpeciesQ] := TraceNorm[rho, {q}]

TraceNorm[rho_, qq:{__?SpeciesQ}] := TraceNorm @ Matrix[rho, qq]


TraceDistance::usage = "TraceDistance[a, b] returns the trace distance of the two square matrices a and b, which equals to TraceNorm[a - b]."

TraceDistance[a_?MatrixQ, b_?MatrixQ] := TraceNorm[a-b]

TraceDistance[a_?VectorQ, b_?MatrixQ] := TraceNorm[Dyad[a, a] - b]

TraceDistance[a_?MatrixQ, b_?VectorQ] := TraceNorm[a - Dyad[b, b]]

TraceDistance[a_?VectorQ, b_?VectorQ] := TraceNorm[Dyad[a, a] - Dyad[b, b]]

TraceDistance[a_, b_] := TraceDistance[a, b, Agents @ {a, b}]

TraceDistance[a_, b_, ss:{___?SpeciesQ}] :=
  TraceDistance[Matrix[a, ss], Matrix[b, ss]]

(**** </TraceNorm> *****)


(**** <Fidelity> *****)

Fidelity::usage = "Fidelity[\[Rho],\[Sigma]] returns the fidelity of the states \[Rho] and \[Sigma]. \[Rho] and \[Sigma] can take a vector (pure state), matrix (mixed state), ket expression (pure state), or opertor expression (mixed state).\nSee also ClassicalFidelity."

Fidelity[a_?MatrixQ, b_?MatrixQ] := With[
  {c = MatrixPower[a, 1/2]},
  Tr @ MatrixPower[c.b.c, 1/2]
 ]

Fidelity[v_?VectorQ, m_?MatrixQ] := Chop @ Sqrt[Conjugate[v].m.v]

Fidelity[m_?MatrixQ, v_?VectorQ] := Fidelity[v, m]

Fidelity[a_?VectorQ, b_?VectorQ] := Abs[Conjugate[a].b]


Fidelity[rho_, sgm_] := Fidelity @@ Matrix @ {rho, sgm} /;
  And[FreeQ[rho, _Ket], FreeQ[sgm, _Ket]]

Fidelity[vec_, rho_] := Chop @ Sqrt[Dagger[vec] ** rho ** vec] /;
  And[Not @ FreeQ[vec, _Ket], FreeQ[rho, _Ket]]

Fidelity[rho_, vec_] := Chop @ Sqrt[Dagger[vec] ** rho ** vec] /;
  And[Not @ FreeQ[vec, _Ket], FreeQ[rho, _Ket]]

Fidelity[vec_, wec_] := Abs[Dagger[vec] ** wec] /;
  And[Not @ FreeQ[vec, _Ket], Not @ FreeQ[wec, _Ket]]


ClassicalFidelity::usage = "ClassicalFidelity[{p1,p2,\[Ellipsis]}, {q1,q2,\[Ellipsis]}] returns the classical fidelity between two probability distributions {p1,p2,\[Ellipsis]} and {q1,q2,\[Ellipsis]}.\nSee also Fidelity."

ClassicalFidelity::noprb = "`` is not a probability distribution."

ClassicalFidelity::incmp = "Probability distributions `1` and `2` cannot describe the same random variable."

ClassicalFidelity[p:{__?NumericQ}, q:{__?NumericQ}] := Which[
  Not @ probabilityQ[p],
  Message[ClassicalFidelity::noprb, p],
  Not @ probabilityQ[q],
  Message[ClassicalFidelity::noprb, q],
  Not @ ArrayQ @ {p, q},
  Message[ClassicalFidelity::incmp, p, q],
  True, Total @ Sqrt[p * q]
 ]

ClassicalFidelity[p_List, q_List] := Total @ Sqrt[p * q] /; ArrayQ[{p, q}]


probabilityQ[p:{__?NonNegative}] := Chop[Total @ p] == 1

probabilityQ[_] = False

(**** </Fidelity> *****)


(* ***************************************************************** *)
(*     <GraphForm>                                                   *)
(* ***************************************************************** *)

Vertex::usage = "Vertex[a, b, ...] represents an interaction vertex.\nNot to be confused with Vertices in Graph or related functions."


VertexLabelFunction::usage = "VertexLabelFunction is an option for GraphForm and ChiralGraphForm that specifies the function to generate primities for redering each vertex label.\nSee also VertexLabels."


EdgeLabelFunction::usage = "EdgeLabelFunction is an option for GraphForm and ChiralGraphForm that speicifes the function to generate primities for redering each edge label.\nSee also EdgeLabels."

defaultEdgeLabelFunction[ Rule[edge_, $] ] := Nothing

defaultEdgeLabelFunction[ Rule[edge_, lbl_] ] := Rule[
  edge,
  Framed[lbl, FrameStyle -> None, Background -> White]
 ]

defaultEdgeLabelFunction[ RuleDelayed[edge_, cnd_Condition] ] := With[
  { lbl = First @ cnd,
    tst = Last @ cnd },
  RuleDelayed @@ List[
    edge,
    Condition[
      Framed[lbl, FrameStyle -> None, Background -> White],
      tst
     ]
   ]
 ]
(* NOTE: This includes dirty tricks to overcome the restrictions put by
   the HoldRest attribute of RuleDelayed. *)

defaultEdgeLabelFunction[ RuleDelayed[edge_, lbl_] ] := RuleDelayed[
  edge,
  Framed[lbl, FrameStyle -> None, Background -> White]
 ]


GraphForm::usage = "GraphForm[A] converts the matrix A to a graph revealing the connectivity, assuming that the matrix is a linear map on one vector space.\nGraphForm allows the same options as Graph, but their specifications may be slightly different.\nGraphForm is a variation of the built-in function GraphPlot.\nGraphForm[expr] returns a graph visualizing the connectivity of different particles in the expression.\nGraphForm allows all options of Graph.\nSee also ChiralGraphForm, GraphPlot, AdjacencyGraph, IncidenceGraph."

Options[GraphForm] = {
  "HideSelfLinks" -> True, (* Not implemented yet. *)
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
      UndirectedEdge[_, _, "Pairing"] -> Directive[Red, Thick],
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
      EdgeLabels, Join[ {opts}, edges, Options[GraphForm], Options[Graph]]
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
       EdgeLabels, Join[ {opts}, Options[GraphForm], Options[Graph]]
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

(* ***************************************************************** *)
(*     </GraphForm>                                                  *)
(* ***************************************************************** *)


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


Protect[ Evaluate @ $symbs ]

End[]

EndPackage[]
