(* -*- mode: math; -*- *)

(****
  Mahn-Soo Choi (Korea Univ, mahnsoo.choi@gmail.com)
  $Date: 2021-02-25 11:16:21+09 $
  $Revision: 2.66 $
  ****)

BeginPackage[ "Q3`Pauli`", { "Q3`Cauchy`", "Q3`" } ]

Unprotect[Evaluate[$Context<>"*"]]

Begin["`Private`"]
`Version = StringJoin[
  $Input, " v",
  StringSplit["$Revision: 2.66 $"][[2]], " (",
  StringSplit["$Date: 2021-02-25 11:16:21+09 $"][[2]], ") ",
  "Mahn-Soo Choi"
 ];
End[]

{ Spin, SpinNumberQ };

{ State, TheKet, TheBra, TheState };

{ KetRule, KetTrim, VerifyKet };

{ DefaultForm, LogicalForm, ProductForm, SimpleForm };

{ BraKet };

{ Basis, Matrix, BuildMatrix, $RepresentableTests };

{ HermitianProduct, HermitianNorm };

{ BlochSphere, BlochVector };

{ Affect };

{ Pauli, Raise, Lower, Hadamard, Quadrant, Octant,
  ThePauli, TheRaise, TheLower, TheHadamard };
{ Operator, TheOperator };

{ OTimes, OSlash, ReleaseTimes };

{ RaiseLower, $RaiseLowerRules };

{ PauliExpression, PauliExpressionRL };

{ PauliInner };

{ Rotation, EulerRotation,
  TheRotation, TheEulerRotation,
  EulerAngles, TheEulerAngles };

{ WignerFunction };

{ RandomVector, RandomMatrix, RandomHermitian, RandomUnitary };

{ BasisComplement };

{ KetPermute, KetSymmetrize };

{ PermutationMatrix };

{ CircleTimes, CirclePlus, BlockDiagonalMatrix };

{ Dyad, DyadExpression };

{ Zero, One };

{ Parity, ParityEvenQ, ParityOddQ };

{ TensorFlatten, Tensorize, PartialTrace, PartialTranspose };

{ PauliDecompose, PauliCompose };
{ PauliDecomposeRL, PauliComposeRL };
{ PauliEmbed, PauliApply };

{ SchmidtDecomposition };

{ TraceNorm, TraceDistance, Fidelity };

{ Purification, Purge };

{ GraphForm, ChiralGraphForm,
  Vertex, VertexLabelFunction, EdgeLabelFunction };

{ PauliExtract, PauliExtractRL }; (* obsolete *)
{ PauliExpand }; (* OBSOLETE *)

Begin["`Private`"]

$symbs = Unprotect[
  Multiply, CircleTimes, CirclePlus,
  $GarnerHeads, $GarnerTests,
  $ElaborationRules, $ElaborationHeads,
  Dot, Ket, Bra, BraKet
 ]

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

TheKet[a:(0 | 1 | Up | Down) ..] := Module[
  { bits = {a} /. {Up -> 0, Down -> 1},
    j },
  j = 1 + FromDigits[bits, 2];
  SparseArray[ {j -> 1}, 2^Length[bits] ]
 ]

(* TheKet[ a:(0|1|Up|Down).. ] := CircleTimes @@ Map[TheKet,{a}] *)
(* It takes quite for bit strings longer than 10. *)


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

SetAttributes[ThePauli, {NHoldAll, ReadProtected}]

ThePauli[0] = SparseArray[{{1, 1} -> 1, {2, 2} -> 1}, {2, 2}]

ThePauli[1] = SparseArray[{{1, 2} -> 1, {2, 1} -> 1}, {2, 2}]

ThePauli[2] = SparseArray[{{1, 2} ->-I, {2, 1} -> I}, {2, 2}]

ThePauli[3] = SparseArray[{{1, 1} -> 1, {2, 2} ->-1}, {2, 2}]


ThePauli[4] = TheRaise[] = TheRaise[1] = SparseArray[{{1, 2} -> 1}, {2, 2}]

ThePauli[5] = TheLower[] = TheLower[1] = SparseArray[{{2, 1} -> 1}, {2, 2}]

ThePauli[6] = TheHadamard[] = TheHadamard[1] = {{1,1},{1,-1}}/Sqrt[2]

ThePauli[7] = TheQuadrant[] = TheQuadrant[1] =
  SparseArray[{{1, 1} -> 1, {2, 2} -> I}, {2, 2}]

ThePauli[8] = TheOctant[] = TheOctant[1] =
  SparseArray[{{1, 1} -> 1, {2, 2} -> Exp[I Pi/4]}, {2, 2}]


ThePauli[10] = SparseArray[{{1,1} -> 1}, {2,2}]

ThePauli[11] = SparseArray[{{2,2} -> 1}, {2,2}]


ThePauli[Raise] := ThePauli[4]

ThePauli[Lower] := ThePauli[5]

ThePauli[Hadamard] := ThePauli[6]

ThePauli[Quadrant] := ThePauli[7]

ThePauli[Octant] := ThePauli[8]

TheRaise[0] = TheLower[0] = TheHadamard[0] = TheQuadrant[0] = ThePauli[0]


(* These are for Matrix[Dyad[...]]. *)
ThePauli[1 -> 0] := ThePauli[4]

ThePauli[0 -> 1] := ThePauli[5]

ThePauli[0 -> 0] := ThePauli[10]

ThePauli[1 -> 1] := ThePauli[11]


ThePauli[ nn:(0|1|2|3|4|5|6|7|8|_Rule).. ] :=
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


(* ************************************************************************** *)

DefaultForm::usage = "DefaultForm[expr] converts every Ket[...] and Bra[...] in expr into the simplest form by dropping elements with default values.\nTo be compared with LogicalForm."

DefaultForm[ expr_ ] := expr /;
  FreeQ[ expr, _Ket | _Bra | _Dyad ]

DefaultForm[ expr_ ] := expr /. {
  a_OTimes -> a, (* NOTE *)
  OSlash[v_Ket, expre_] :> OSlash[v, DefaultForm @ expre],
  Ket[a_Association] :> Ket @ KetTrim @ a,
  Bra[a_Association] :> Bra @ KetTrim @ a,
  Dyad[a_Association, b_Association, qq_List] :>
    Dyad[KetTrim @ a, KetTrim @ b, qq]
 }
(* NOTE: This line is necessary to prevent the Kets and Bras in OTimes from
   being affected. *)


LogicalForm::usage = "LogicalForm[expr] converts every Ket[...] and Bra[...] in expr into the fully logical form without dropping any element.\nLogicalForm[expr, {S1, S2, ...}] assumes that expr involves systems labeled by S1, S2, ....\nLogicalForm[expr, S] is quivalent to LogicalForm[expr, {S}].\nSee also DefaultForm."

LogicalForm[ expr_ ] := LogicalForm[ expr, {} ]

LogicalForm[ expr_, S_ ] := LogicalForm[ expr, {S} ]

LogicalForm[ expr_, _List ] := expr /;
  FreeQ[ expr, Ket[_Association] | Bra[_Association] | _Dyad ]

LogicalForm[ Ket[a_Association], gg_List ] := Module[
  { ss = Union[Keys @ a, FlavorNone @ gg] },
  Ket @ Association @ Thread[ ss -> Lookup[a, ss] ]
 ]

LogicalForm[ Bra[a_Association], gg_List ] :=
  Dagger @ LogicalForm[Ket[a], gg]

LogicalForm[ Dyad[a_Association, b_Association, All], gg_List ] := Module[
  { ss = Union[Keys @ a, Keys @ b, FlavorNone @ gg] },
  Dyad[
    Association @ Thread[ ss -> Lookup[a, ss] ],
    Association @ Thread[ ss -> Lookup[b, ss] ],
    All
   ]
 ]

(* For some irreducible basis, e.g., from QuissoAdd[] *)
LogicalForm[ expr_Association, gg_List ] :=
  Map[ LogicalForm[#,gg]&, expr ]
(* NOTE: Association needs to be handled carefully due to HoldAllComplete
   Attribute of Association. Otherwise, the result may be different from what
   you would expect.  *)

LogicalForm[ expr_, gg_List ] := Module[
  { ss = NonCommutativeSpecies @ expr },
  ss = Union[ ss, FlavorNone @ gg ];
  expr /. {
    ot_OTimes -> ot, (* NOTE 1 *)
    OSlash[v_Ket, ex_ ] :> OSlash[ v, LogicalForm[ex, gg] ],
    v_Ket :> LogicalForm[v, ss],
    v_Bra :> LogicalForm[v, ss],
    d_Dyad :> LogicalForm[d, ss],
    a_Association :> LogicalForm[a, ss] (* NOTE 3 *)
   }
 ]
(* NOTE 1: This line is necessary to prevent the Kets and Bras in OTimes from
   being affected. *)
(* NOTE 2: This implementation works when Missing["KeyAbsent", S] is properly
   defined. *)
(* NOTE 3: See the NOTE for LogicalForm[_Association, ...] *)

$KetDelimiter::usage = "The charater delimiting values in a Ket."

$KetGroupDelimiter::usage = "The charater delimiting groups of values in a Ket."

Once[
  $KetDelimiter = Nothing;
  $KetGroupDelimiter = ";";
 ]

SimpleForm::usage = "SimpleForm[expr] represents every Ket in expr in the simplest form dropping all subsystem indices.\nSimpleForm[expr, {S1, ..., {S2, S3, ...}, ...}] splits each Ket into the form Ket @ Row @ {S1, ..., Ket[S2, S3, ...], ...}."

SimpleForm[ expr_ ] := SimpleForm[ expr, {} ]

SimpleForm[ expr_, {} ] := Module[
  { ss },
  ss = Union @ Flatten @ Cases[
    {expr},
    (Ket|Bra)[a_Association] :> Keys[a],
    Infinity
   ];
  SimpleForm[ expr, {ss}]
 ]

SimpleForm[ expr_, S_?SpeciesQ ] := SimpleForm[ expr, {S} ]

SimpleForm[ v:Ket[_Association], gg_List ] := Ket @ Row @ Riffle[
  v /@ gg, $KetDelimiter
 ] /; FreeQ[gg, _List, 1]

SimpleForm[ v:Ket[_Association], gg_List ] := Ket @ Row @ Riffle[
  Map[ Row @ Riffle[#, $KetDelimiter]&, Flatten /@ List /@ v /@ gg ],
  $KetGroupDelimiter
 ]

SimpleForm[ v:Bra[a_Association], gg_List ] :=
  Dagger @ SimpleForm[Ket[a], gg]

(* For some irreducible basis, e.g., from QuissoAdd[] *)
SimpleForm[ expr_Association, gg_List ] :=
  Map[ SimpleForm[#,gg]&, expr ]
(* NOTE: Association needs to be handled carefully due to HoldAllComplete
   Attribute of Association. Otherwise, the result may be different from what
   you would expect.  *)

SimpleForm[ expr_, gg_List ] := expr /. {
  v_Ket :> SimpleForm[v, gg],
  v_Bra :> SimpleForm[v, gg],
  a_Aggociation :> SimpleForm[a, gg] (* NOTE 3 *)
 }
(* NOTE 3: See the NOTE for LogicalForm[_Association, ...] *)


ProductForm::usage = "ProductForm[expr] represents every Ket in \*StayleBox[expr,Italic] in the simplest form dropping all subsystem indices.\nProductForm[expr, {S1, ..., {S2,S3,...}, ...}] splits each Ket into the form Row[{Ket[S1], ..., Ket[S2,S3,...], ...}]."

ProductForm[ expr_ ] := ProductForm[expr, NonCommutativeSpecies @ expr]

ProductForm[ expr_, S_?SpeciesQ ] := SimpleForm[ expr, {S} ]

ProductForm[ Ket[a_Association], gg_List ] := Row @ Map[
  Ket @ Row @ Riffle[#, $KetDelimiter]&,
  Flatten /@ List /@ Lookup[a, FlavorNone @ gg]
 ]

ProductForm[ v:Bra[a_Association], gg_List ] :=
  Dagger @ ProductForm[Ket[a], gg]

(* For some irreducible basis, e.g., from QuissoAdd[] *)
ProductForm[ expr_Association, gg_List ] :=
  Map[ ProductForm[#,gg]&, expr ]
(* NOTE: Association needs to be handled carefully due to HoldAllComplete
   Attribute of Association. Otherwise, the result may be different from what
   you would expect.  *)

ProductForm[ expr_, gg_List ] := expr /. {
  v_Ket :> ProductForm[v, gg],
  v_Bra :> ProductForm[v, gg],
  a_Aggociation :> ProductForm[a, gg] (* NOTE 3 *)
 }
(* NOTE 3: See the NOTE for LogicalForm[_Association, ...] *)


Affect::usage = "Affect[ket, op1, op2, ...] operates the operators op1, op2, ... (earlier operators first) on ket. Notice the order of the arguments. The result should be equivalent to Multiply[..., op2, op1, ket], but it is much faster than the counterpart for deep (the numer of operators is much bigger than the number of particles) expression. First first argument does not need to be a Ket, but otherwise Affect is not an advantage over Multiply."

SetAttributes[Affect, Listable]

Affect[ket_, op__] := Distribute[ doAffect @@ Garner[{ket, op}] ]

doAffect[ket_, a_, b__] := Fold[ doAffect, ket, {a, b} ]

doAffect[ket_, op_Multiply] := doAffect[ket, Sequence @@ Reverse[op]]

doAffect[ket_, op_] := Garner @ Multiply[op, ket]


 Ket::usage = "Ket represents a basis state of a system of Spins or similar systems.\nKet[0] and Ket[1] represent the two eigenvectors of the Pauli-Z matrix Pauli[3]. Ket[s$1, s$2, ...] represents the tensor product Ket[s$1] \[CircleTimes] Ket[s$2] \[CircleTimes] ....\nSee also Ket, TheKet, Bra, TheBra, State, TheState, Pauli, ThePauli, Operator, TheOperator."

Bra::usage = "Bra[expr] = Dagger[ Ket[expr] ].\nSee also Bra, TheBra, Ket, TheKet, Pauli, ThePauli."

SetAttributes[{Ket, Bra}, NHoldAll]
(* The integers in Ket[] and Bra[] should not be converted to real
   numbers by N[]. *)

Format[ Ket[Association[]] ] := Ket[Any]

Format[ Bra[Association[]] ] := Bra[Any]

Format[ Ket[a_Association] ] :=
  Ket @ DisplayForm @ Row @ KeyValueMap[ Subscript[#2,#1]&, a]

Format[ Bra[a_Association] ] :=
  Bra @ DisplayForm @ Row @ KeyValueMap[ Subscript[#2,#1]&, a]


Ket /: NonCommutativeQ[ Ket[___] ] = True

Bra /: NonCommutativeQ[ Bra[___] ] = True

Ket /: Kind[ Ket[___] ] = Ket

Bra /: Kind[ Bra[___] ] = Bra

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

Ket[ Ket[a_Association], spec__Rule ] := With[
  { rules = Flatten @ KetRule @ {spec} },
  VerifyKet @ Ket @ KeySort @ KetTrim @ Join[a, Association @ rules]
 ]

(* operator form *)
Ket[a_Association][spec__Rule] := Ket[ Ket[a], spec ]

(* extracting the values *)
Ket[a_Association][ss_List] := Lookup[a, FlavorNone @ ss]

(* extracting a value *)
Ket[a_Association][s_] := a[FlavorNone @ s]


Bra[] = Bra[ Association[] ]

Bra[spec__Rule] := Dagger @ Ket[Ket[], spec]

Bra[v_Bra, spec__Rule] := Dagger @ Ket[Dagger @ v, spec]


Bra[a_Association][spec__Rule] := Bra[ Bra[a], spec ]

Bra[a_Association][ss_List] := Lookup[a, FlavorNone @ ss]

Bra[a_Association][s_] := a[FlavorNone @ s]


KetRule::usage = "KetRule is a low-level function used in various packages. KetRule[expr] generates proper rules to be store in the Ket[<|...|>] data form."

SetAttributes[KetRule, Listable]

KetRule[r_Rule] := r


KetTrim::usage = "KetTrim[ ]..."

KetTrim[Ket[a_Association]] := Ket @ KetTrim[a]

KetTrim[a_Association] := Association @ KeyValueMap[KetTrim, a]

KetTrim[a_, b_] := Rule[a, b]

KetTrim[{}, _] := Nothing (* a fallback *)

KetTrim[_String, _] := Nothing (* an actual option *)


VerifyKet::usage = "VerifyKet[v] returns v if v is an valid Ket; 0 otherwise."

SetAttributes[VerifyKet, Listable]

VerifyKet[ expr_ ] := expr //. {v_Ket :> VerifyKet[v]}

VerifyKet[ Ket[a_Association] ] := With[
  { aa = KeyValueMap[VerifyKet, a] },
  If[MemberQ[aa, 0], 0, Ket@Association@aa, Ket@Association@aa]
 ]

VerifyKet[a_, b_] := Rule[a, b]


(* <Multiply> *)

(* Ket[] ** Ket[] = Ket[] x Ket[] *)
HoldPattern @
  Multiply[ pre___, a:Ket[_Association], b:Ket[_Association], post___ ] :=
  Multiply[pre, CircleTimes[a, b], post]

(* Bra[] ** Bra[] = Bra[] x Bra[] *)
HoldPattern @
  Multiply[ pre___, a:Bra[_Association], b:Bra[_Association], post___ ] :=
  Multiply[pre, CircleTimes[a, b], post]

HoldPattern @
  Multiply[ pre___, Bra[a_Association], Ket[b_Association], post___ ] :=
  BraKet[a, b] Multiply[pre, post]

HoldPattern @
  Multiply[ pre___, Bra[a___], Ket[b___], post___ ] :=
  BraKet[{a}, {b}] Multiply[pre, post]
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

(* </Multiply> *)

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


BraKet::usage = "BraKet[{a}, {b}] represents the Hermitian product \[LeftAngleBracket]a|b\[RightAngleBracket] of the two states Ket[a] and Ket[b]."

SetAttributes[BraKet, {NHoldAll, ReadProtected}]
(* The integers in BraKet[] should not be converted to real numbers by N[]. *)

Format[ BraKet[{}, b_List] ] := BraKet[{Any}, b]

Format[ BraKet[a_List, {}] ] := BraKet[a, {Any}]

Format[
  BraKet[ a:Except[_List|_Association], b:Except[_List|_Association] ]
 ] := BraKet[{a}, {b}]

BraKet /: ComplexQ[ BraKet[_List, _List] ] = True

BraKet /: Conjugate[ BraKet[a_List, b_List] ] := BraKet[b, a]

Dot[ Bra[a___], Ket[b___] ] := BraKet[{a}, {b}]
(* Recall that Dot has Flat attribute. *)

(* General evaluation rules *)

BraKet[ a_List, b_List ] := KroneckerDelta[a, b]

BraKet[ a_Association, b_Association ] := With[
  { qq = Union[Keys @ a, Keys @ b] },
  KroneckerDelta[ Lookup[a, qq], Lookup[b, qq] ]
 ]


ReleaseTimes::usage = "ReleaseTimes[expr] replace OTimes and OSlash with CirlceTimes (\[CircleTimes]) to recover the standard expression."

ReleaseTimes[expr_] := DefaultForm[
  expr /. {OTimes -> CircleTimes, OSlash -> CircleTimes}
 ]


OTimes::usage = "OTimes represents CircleTimes, but holds the arguments. Note that both OTimes and OSlash, two variants of CircleTimes, are intended for state vectors (but not gate operators)."
(* It is used, e.g., for QuissoFactor[]. *)

Format[ HoldPattern[ OTimes[a__] ] ] := CircleTimes @@ Map[HoldForm] @ {a}

OTimes[a_] := a

OTimes[a___, b_?CommutativeQ, c___] := b OTimes[a, c]

OTimes /:
HoldPattern @ Dagger[ OTimes[a__] ] := OTimes @@ Dagger @ {a}


OSlash::usage = "OSlash represents a special form of CircleTimes. It is useful, for example, to find the results of Measure[...] and to find the reduced Ket expressions. Note that both OTimes and OSlash, two variants of CircleTimes, are intended for state vectors (but not gate operators)."

Format[ HoldPattern[ OSlash[a:(_Ket|_Bra), b:Times[__]] ] ] :=
  DisplayForm @ CircleTimes[ HoldForm[a], RowBox[{"(",b,")"}] ]

Format[ OSlash[a:(_Ket|_Bra), b_] ] := CircleTimes[ HoldForm[a], HoldForm[b] ]

OSlash /: z_ OSlash[a_Ket, b_] := OSlash[a, z b]

OSlash /: OSlash[a_Ket, b_] + OSlash[a_Ket, c_] := 
  OSlash[a, b + c]

OSlash /:
HoldPattern @ Dagger[ OSlash[a__] ] := OSlash @@ Dagger @ {a}


Once[
  $GarnerHeads = Join[$GarnerHeads, {Pauli, Dyad, Ket, Bra, OTimes, OSlash}];

  $ElaborationHeads = Join[$ElaborationHeads, {Dyad, Pauli}];
 ]


RaiseLower::usage = "RaiseLower[expr] converts expr by rewriting Pauli or Spin X and Y operators in terms of the raising and lowering operators."

RaiseLower[ expr_ ] := Garner[
   expr //. $RaiseLowerRules
 ]

Once[
  $RaiseLowerRules = {
    Pauli[a___, 1, b___] :> (Pauli[a, 4, b] + Pauli[a, 5, b]),
    Pauli[a___, 2, b___] :> (Pauli[a, 4, b] - Pauli[a, 5, b]) / I
   }
 ]


PauliExpand::usage = "PauliExpand[expr] returns more explicit form of the expression expr."

PauliExpand[expr_] := (
  Message[Q3General::obsolete, PauliExpand, Elaborate];
  Elaborate[expr]
 )


Hadamard::usage = "Hadamard is a flavor index representing the Hadamard gate."

Quadrant::usage = "Quadrant is a flavor index representing the quadrant gate, i.e., the relative phase gate with phase angle 2Pi/4."

Octant::usage = "Octant is a flavor index representing the octant gate, i.e., the relative phase gate with phase angle 2Pi/8."


Pauli::usage = "Pauli[n] represents the Pauli operator (n=1,2,3). Pauli[0] represents the 2x2 identity operator, Pauli[4] the Pauli raising operator, Pauli[5] the Pauli lowering operator, and Pauli[6] the Hadamard operator.\nPauli[10] returns (Pauli[0]+Pauli[1])/2, the Projection to Ket[0].\nPauli[11] returns (Pauli[0]-Paui[1])/2, the projection to Ket[1].\nPauli[n1, n2, ...] represents the tensor product of the Pauli operators Pauil[n1], Pauli[n2], ... ."

SetAttributes[Pauli, {NHoldAll, ReadProtected}]
(* The integers in Pauli[] should not be converted to real numbers by N[]. *)

Pauli /:
MultiplyGenus[ Pauli[___] ] = "Singleton"

Format[ Pauli[a:(0|1|2|3|4|5|6|7|8|-7|-8)..] ] := With[
  { aa = {a} /. theIndexRules },
  DisplayForm[ CircleTimes @@ Map[SuperscriptBox["\[Sigma]",#]&] @ aa ]
 ]

Format @ Pauli[map__Rule] := With[
  { vv = Ket @@@ Transpose[List @@@ {map}] },
  Row @ {First @ vv, Dagger @ Last @ vv}
 ]


thePlus  = Style["+", Larger, Bold];
theMinus = Style["-", Larger, Bold];
theIndexRules = {
  1->"x", 2->"y", 3->"z",
  4->thePlus, 5->theMinus,
  6->"H", 7->"S", 8->"T", -7->"-S", -8->"-T" };


Raise[0] = Lower[0] = Hadamard[0] = Pauli[0]

Raise[] = Raise[1] = Pauli[Raise]

Lower[] = Lower[1] = Pauli[Lower]

Hadamard[] = Hadamard[1] = Pauli[Hadamard]


Pauli[10] := (Pauli[0] + Pauli[3]) / 2

Pauli[11] := (Pauli[0] - Pauli[3]) / 2


Pauli[Raise] := (Pauli[1] + I Pauli[2]) / 2
(* Pauli[4] is kept without being expanded in terms of Pauli[1] and Pauli[2] *)

Pauli[Lower] := (Pauli[1] - I Pauli[2]) / 2
(* Pauli[5] is kept without being expanded in terms of Pauli[1] and Pauli[2] *)

Pauli[Hadamard] := (Pauli[1]+Pauli[3])/Sqrt[2]
(* Pauli[6] is kept without being expanded *)

Pauli[Quadrant] := Pauli[0] (1+I)/2 + Pauli[3] (1-I)/2
(* Pauli[7] is kept without being expanded *)
Pauli[-Quadrant] := Pauli[0] (1-I)/2 + Pauli[3] (1+I)/2

Pauli[Octant] := Pauli[0] (1+Exp[I Pi/4])/2 + Pauli[3] (1-Exp[I Pi/4])/2
(* Pauli[8] is kept without being expanded *)
Pauli[-Octant] := Pauli[0] (1+Exp[-I Pi/4])/2 + Pauli[3] (1-Exp[-I Pi/4])/2

(*
Pauli[ a___, b:(Raise|Lower|Hadamard|Quadrant|Octant|10|11), c___ ] :=
  Garner @ CircleTimes[Pauli[a], Pauli[b], Pauli[c]]
 *)
Pauli[a__] := Garner @ Apply[CircleTimes, Pauli /@ {a}] /;
  ContainsAny[
    { a },
    { 10, 11, Raise, Lower, Hadamard,
      Quadrant, Octant, -Quadrant, -Octant }
   ]
(* NOTE: Multi-spin Pauli operators are stored in Pauli[a, b, c, ...],
   NOT CircleTimes[Pauli[a], Pauli[b], Pauli[c], ...].
   Namely, Pauli[...] is not expanded into CircleTimes. *)

Pauli[a:{(0|1)..} -> b:{(0|1)..}] := Pauli @@ Thread[a -> b]

Pauli /:
HoldPattern @ Elaborate[ Pauli[jj__] ] := Module[
  { new },
  new = {jj} /. {
    HoldPattern[0 -> 0] :> 10,
    HoldPattern[1 -> 1] :> 11,
    HoldPattern[1 -> 0] :> Raise,
    HoldPattern[0 -> 1] :> Lower,
    4 -> Raise,
    5 -> Lower,
    6 -> Hadamard,
    7 -> Quadrant,
    8 -> Octant,
    -7 -> -Quadrant,
    -8 -> -Octant
   };
  Garner @ Apply[CircleTimes, Pauli /@ new]
 ]

Pauli /:
Dagger[ Pauli[a__] ] := Pauli[a] /. {4->5, 5->4, 7->-7, -7->7, 8->-8, -8->8}
(* NOTE: Multi-spin Pauli operators are stored in Pauli[a, b, c, ...],
   NOT CircleTimes[Pauli[a], Pauli[b], Pauli[c], ...].
   Namely, Pauli[...] is not expanded into CircleTimes. *)


Pauli /: Conjugate[ Pauli[2] ] = -Pauli[2]

Pauli /: Conjugate[ Pauli[7] ] = Pauli[-7]

Pauli /: Conjugate[ Pauli[-7] ] = Pauli[7]

Pauli /: Conjugate[ Pauli[8] ] = Pauli[-8]

Pauli /: Conjugate[ Pauli[-8] ] = Pauli[8]

Pauli /: Conjugate[ Pauli[m:(0|1|3|4|5|6)] ] := Pauli[m]

Pauli /: Conjugate[ Pauli[a_, b__] ] := CircleTimes @@ Map[
  Conjugate @* Pauli, {a, b}
 ]

  
Pauli /:
CircleTimes[a_Pauli, b__Pauli] := Pauli @@ Catenate[List @@@ {a, b}]
(* CircleTimes[ Pauli[a], Pauli[b], ... ] are stored into Pauli[a, b, ...], where a, b, ... are elementry (0,1,2,3). *)


(* <Pauli in Multipy> *)
HoldPattern @ Multiply[pre___, op__Pauli, vec:Ket[(0|1)..], post___] :=
  Multiply[pre, Dot[op, vec], post]

HoldPattern @ Multiply[pre___, op_Pauli, more__Pauli, Shortest[post___]] :=
  Multiply[pre, Dot[op, more], post]

(* </Pauli in Multiply> *)


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

Operator[ { kk:{(0|1|2|3|4|5|6|7|8|-7|-8)..}, th:Except[_List], ph:Except[_List] } ] := 
  CircleTimes @@ Map[Operator] @ Tuples[{kk, {th}, {ph}}]
(* These are first expanded because they are not elementry. *)


PauliExpression::usage = "PauliExpression[m] returns an expression for the matrix M in terms of the Pauli matrices.\nPauliExpression[v] takes a 2^n dimensional vector v and rewrites it in a natural form expanded in the logical basis.\nPauliExpression[{j1,j2,...}, v] is for (2*j1+1)x(2*j2+1)x ... dimensional vector v."

(* for column vectors *)

Ket::badLen = "Incompatible length of the Ket."

PauliExpression[a_SparseArray?VectorQ] := Module[
  { n = Log[2,Length[a]], bits, vals },
  If[ !IntegerQ[n],
    Message[Ket::badLen];
    Return[a]
   ];
  bits = Cases[ Flatten @ Keys @ Association @ ArrayRules @ a, _Integer ];
  vals = a[[bits]];
  bits = Apply[Ket, IntegerDigits[bits-1,2,n], {1}];
  Garner @ Dot[vals, bits]
 ]

PauliExpression[a_?VectorQ] :=
  PauliExpression @ SparseArray[ ArrayRules[a], {Length @ a} ]

(* for square matrices *)

PauliExpression[m_?MatrixQ] := Block[
  {nn, ss, vv, jj},
  nn = Log[2, Length[m]];
  ss = Tuples[{0,1,2,3}, nn];
  vv = Map[ PauliInner[ThePauli@@#, m]&, ss ];
  jj = Flatten @ Position[vv, Except[0|0.], {1}, Heads->False];
  ss = Apply[Pauli, ss[[jj]], {1}];
  vv = vv[[jj]];
  Garner @ Dot[vv, ss]
 ]

PauliExpressionRL::usage = "PauliExpressionRL[m] returns an expression for the matrix M in terms of the Pauli matrices."

PauliExpressionRL[m_?MatrixQ] := Block[
  {nn, ss, vv, jj},
  nn = Log[2, Length[m]];
  ss = Tuples[{0,3,4,5}, nn];
  vv = Map[ PauliInner[ThePauli@@#, m]&, ss ];
  jj = Flatten @ Position[vv, Except[0|0.], {1}, Heads->False];
  ss = Apply[Pauli, ss[[jj]], {1}];
  ss = Map[ (# * 2^Count[#,4|5])&, ss ];
  vv = vv[[jj]];
  Garner @ Dot[vv, ss]
 ]


PauliInner::usage = "PauliInner[m1, m2] = Tr[Topple[m1].m2] / Length[m2] returns the Hermitian product of two square matrices M1 and M2."

PauliInner[m1_?MatrixQ, m2_?MatrixQ] :=
  Tr[ Topple[m1].m2 ] / Length[m2] /;
  Dimensions[m1] == Dimensions[m2]

PauliInner[v1_?VectorQ, v2_?VectorQ] := Topple[v1].v2


HermitianNorm::usage = "HermitianNorm[a] gives the norm of a complex number, vector, or matrix a.\nFor complex numbers, it is Abs[z].\nFor vectors, it is Sqrt[Conjugate[a].a].\nFor matrices, it is the Frobenius norm, i.e., Tr[ConjugateTranspose[a].a].\nIt should be distinguished from the TraceNorm."

HermitianNorm[a_?VectorQ] := Norm[a]

HermitianNorm[a_?MatrixQ] := Norm[a, "Frobenius"]

Format[ HermitianNorm[a_] ] := Sqrt @ AngleBracket[a, a]


HermitianProduct::usage = "HermitianProduct[a, b] returns the Hermitian product of two vectors a and b.\nFor two matrices a and b, it is equivalent to the Frobenius inner product, i.e., Tr[ConjugateTranspose[a].b]."

HermitianProduct[a_?VectorQ, b_?VectorQ] := Conjugate[a].b

HermitianProduct[a_?MatrixQ, b_?MatrixQ] :=
  HermitianProduct[Flatten @ a, Flatten @ b]

Format[ HermitianProduct[a_, b_] ] := AngleBracket[a, b]


BlochVector::usage = "BlochSphere[{c0, c1}] returns the point on the Bloch sphere corresponding to the pure state Ket[0]*c0 + Ket[1]*c1.\nBlochVector[\[Rho]] returns the point in the Bloch sphere corresponding to the mixed state \[Rho]."

BlochVector[rho_?MatrixQ] := Simplify[Rest @ PauliDecompose[rho] * 2] /;
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

BlochVector[expr_, q_?SpeciesQ] := Module[
  { ss = Species[expr],
    qq = FlavorNone @ q,
    cc },
  If[ Length[ss] > 1,
    cc = Complement[ss, {qq}];
    BlochVector @ PartialTrace[expr, cc, Identity],
    BlochVector @ Matrix[expr, qq]
   ]
 ]

BlochVector[expr_] := BlochVector[expr, 1] /;
  Not @ FreeQ[expr, _Pauli | _Ket]

BlochVector[expr_, j_Integer] := Module[
  { mat = Matrix[expr],
    n },
  n = Log[2, Length @ mat];
  If[ n > 1,
    BlochVector @ PartialTrace[mat, Complement[Range @ n, {j}]],
    BlochVector @ mat
   ]
 ] /; Not @ FreeQ[expr, _Pauli | _Ket]


BlochSphere::usage = "BlochSphere[primitives, options] returns Graphics3D containing the Bloch sphere as well as primitives.\nIt accepts all Graphics3D primitives and, in addition, BlochPoint.\nBlochSphere[options] just displays the Bloch sphere."

Options[BlochSphere] = {
  "Opacity" -> 0.8,
  "PointSize" -> 0.03,
  Ticks -> None,
  (* Axes -> True, *)
  (* AxesOrigin -> {0, 0, 0}, *)
  (* AxesStyle -> Thick, *)
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


(* *********************************************************************** *)
(*     <Basis>                                                             *)
(* *********************************************************************** *)

$RepresentableTests::usage = "$RepresentableTests gives the list of Pattern Tests to be considered in Basis and Matrix."

Once[ $RepresentableTests = {}; ]

Representables::usage = "Representables[expr] finds all operators appreaing in the expression expr that allows for matrix representation."

Representables[expr_] := Module[
  { tt = PatternTest[_, #]& /@ $RepresentableTests },
  Union @ FlavorMute @ Peel @
    Cases[ Normal @ expr, Alternatives @@ tt, Infinity ]
 ]


Basis::usage = "Basis[n] constructs the standard tensor-product basis of a system of n unlabelled qubits.\nBasis[{dim1, dim2, ..., dimn}] constructs the standard tensor-product basis of a total of n unlabelled systems with the Hilbert space dimensions dim1, dim2, ..., respectively.\nBasis[q1, q2, ...] constructs the tensor product basis for the system consising of Species q1, q2, ...\nBasis[q1, {q2, q3}, ...] is equivalent to Basis[q1, q2, q3, ...].\nBasis[expr] finds the relevant systems from the expression expr and constructs the basis."

Basis[n_Integer] := Ket @@@ Tuples[{0, 1}, n]

Basis[dim:{__Integer}] := Ket @@@ Tuples[Range[0,#-1]& /@ dim]
  
Basis[
  a:Alternatives[_?SpeciesQ, {__?SpeciesQ}],
  b:Alternatives[_?SpeciesQ, {__?SpeciesQ}].. ] :=
  Flatten @ Outer[ CircleTimes, Sequence @@ Map[Basis, {a, b}] ]

Basis[ {} ] := { Ket @ Association[] }
(* This is necessary as a fallback. *)

Basis[ expr_ ] := Basis @@ Representables[expr]

(* *********************************************************************** *)
(*     </Basis>                                                            *)
(* *********************************************************************** *)

(* *********************************************************************** *)
(*     <Matrix>                                                            *)
(* *********************************************************************** *)

Matrix::usage = "Matrix[expr, {a1, a2, ...}] constructs the matrix representation of the expression expr on the total system consisting of a1, a2, ....\nMatrix[expr] feagures out the subsystems involved in expr."

Matrix::rem = "There remain some elements, ``, that are not specified for matrix representation."

(* For Pauli Ket/Bra *)

Matrix[ Ket[j__Integer] ] := TheKet[j]

Matrix[ Ket[j__Integer], {___} ] := TheKet[j]

Matrix[ Bra[j__Integer] ] := TheKet[j]

Matrix[ Bra[j__Integer], {___} ] := TheKet[j]

(* For Pauli operators *)

Pauli /: Matrix[Pauli[j___]] := ThePauli[j]

Pauli /: Matrix[Pauli[j___], {___}] := ThePauli[j]

Pauli /: NonCommutativeQ[ Pauli[__] ] = True


(* For Dyad *)
(* Matrix[Dyad[...], {s1, s2, ...}] is handled below. *)
Dyad /: Matrix[ op:Dyad[_, _, qq_List] ] :=
  Matrix[ Elaborate[op], qq ]


(* For general Ket/Bra *)

Matrix[ Ket[Associatoin[]] ] := 0

Matrix[ Ket[a_Association] ] := Matrix[Ket[a], Keys @ a] /; Length[a] > 1
  
Matrix[ Ket[a_Association], qq:{__?SpeciesQ} ] := With[
  { ss = FlavorNone @ qq },
  CircleTimes @@ Map[
    Matrix @* Ket @* Association,
    Thread[ ss -> Lookup[a, ss] ]
   ]
 ]

Matrix[ Bra[Association[]] ] := 0

Matrix[ Bra[a_Association] ] := Matrix[Bra[a], Keys @ a] /; Length[a] > 1

Matrix[ Bra[v_Association], qq:{__?SpeciesQ} ] :=
  Conjugate[ Matrix[Ket[v], qq] ]


(* Dagger *)

HoldPattern @ Matrix[ Dagger[a_?NonCommutativeQ] ] := Topple @ Matrix[a]
(* NOTE: Matrix[a] may still include some operators; and hence Topple instead
   of ConjugateTranspose. *)

(* Arrays *)

HoldPattern @ Matrix[ expr:(_List|_Association), qq:{__?SpeciesQ} ] :=
  With[
    { ss = FlavorNone @ qq },
    Map[ Matrix[#, ss]&, expr ]
   ]


(* General Code for Operators *)

Matrix[ expr:Except[_Pauli|_Dyad|_Ket|_Bra|_?NonCommutativeQ] ] :=
  Matrix[expr, Representables @ expr]

Matrix[ expr_, {} ] := expr /; FreeQ[expr, _Pauli|_Dyad|_Ket|_Bra]

Matrix[ expr_, q_?SpeciesQ ] := Matrix[expr, {q}] (* for flexibility *)

(* NOTE: ___, not __ *)
Matrix[ expr_Plus, qq:{___?SpeciesQ} ] :=
  Total @ Map[ Matrix[#, qq]&, List @@ expr ]

(* NOTE: ___ (not __) to support Pauli *)
Matrix[ z_?CommutativeQ op_, qq:{___?NonCommutativeQ} ] := z Matrix[op, qq]

(* NOTE: __, not ___ *)
Matrix[ z_?CommutativeQ, qq:{__?NonCommutativeQ} ] := With[
  { jj = Range[ Times @@ (Dimension /@ qq) ] },
  SparseArray @ Thread[ Transpose @ {jj, jj} -> z ]
 ]

(* NOTE: __, not ___ *)
HoldPattern @
  Matrix[ op_?AnyNonCommutativeQ, qq:{__?NonCommutativeQ} ] :=
  BuildMatrix[op, FlavorNone @ qq]
    
(* NOTE: __, not ___ *)
HoldPattern @
  Matrix[ Multiply[ops__], qq:{__?NonCommutativeQ} ] :=
  BuildMatrix[{ops}, FlavorNone @ qq]

  
BuildMatrix::usage = "BuildMatrix is a low-level function that builds the matrix from an operator or a set of operators.\nSee Matrix."

BuildMatrix[ops_List, qq:{__?SpeciesQ}] := Dot @@ Map[
  BuildMatrix[#, qq]&,
  ops
 ]

BuildMatrix[v:Bra[_Association], qq:{__?SpeciesQ}] :=
  Transpose @ Transpose @ List @ Matrix[v, qq]
(* To preserve the SparseArray structure *)

BuildMatrix[v:Ket[_Association], qq:{__?SpeciesQ}] :=
  Transpose @ List @ Matrix[v, qq]

BuildMatrix[op_?AnySpeciesQ, qq:{__?SpeciesQ}] := (
  Message[Matrix::rem, op];
  op Matrix[1, qq]
 ) /; Not @ MemberQ[qq, FlavorMute @ Peel @ op]

BuildMatrix[ op:Dyad[_, _, _List], qq:{__?SpeciesQ} ] :=
  Matrix[ Elaborate[op], qq ]
(* NOTE: The case of Matrix[Dyad[...]] needs to be handled separately and,
   indeed, has already been done above. *)


(* NOTE: Leave op_ unspecified so as for BuildMatrix to be further refined for
   Fermions in Fock`. *)
BuildMatrix[op_, qq:{__?SpeciesQ}] := Module[
  { sp = FlavorMute @ Peel @ op,
    mm = Matrix[op],
    rr },
  rr = One /@ Dimension[qq];
  rr = Association @ Join[ Thread[qq -> rr], {sp -> mm} ];
  CircleTimes @@ rr
 ]


(* *********************************************************************** *)
(*     </Matrix>                                                           *)
(* *********************************************************************** *)


Parity::usage = "Parity[op] represents the parity operator of the species op. For a particle (Boson or Fermion) op, it refers to the even-odd parity of the occupation number. For a Qubit, it refers to the Pauli-Z.\nParity[{a, b, ...}] representts the overall parity of species a, b, ...."

Parity /: Peel[ Parity[a_] ] := a (* for Matrix[] *)

Parity /: Kind[ Parity[a_] ] := Kind[a] (* for Multiply[] *)

Parity /: MultiplyGenus[Parity[_]] := "Singleton" (* for Multiply *)

Parity /: AnySpeciesQ[ Parity[a_] ] := AnySpeciesQ[a] (* for Multiply[] *)

Parity /: AnyNonCommutativeQ[ Parity[a_] ] := AnyNonCommutativeQ[a] (* for Multiply[] *)

Parity[a_?SpeciesQ, b__?SpeciesQ] := Multiply @@ Parity /@ {a, b}

Parity[{op__?SpeciesQ}] := Multiply @@ Parity /@ {op}

HoldPattern @ Multiply[pre___, a_Parity, a_Parity, post___] :=
  Multiply[pre, post]

HoldPattern @ Multiply[pre___, a_Parity, b_Parity, post___] :=
  Multiply[pre, b, a, post] /; Not @ OrderedQ @ {a, b}


ParityEvenQ::usage = "ParityEvenQ[state_, {a, b, ...}] returns True if state (in a Ket expression) has a definite Even parity with respect to the systems a, b, .... Otherwise, False is returned.\nParityEvenQ[state] first finds all systems involved and tests the parity."

ParityOddQ::usage = "ParityOddQ[state_, {a, b, ...}] returns True if state (in a Ket expression) has a definite Odd parity. Otherwise, False is returned.ParityOddQ[state] first finds all systems involved and tests the parity."

ParityEvenQ[ q_?SpeciesQ ][ expr_ ] := ParityEvenQ[expr, {q}]

ParityOddQ[ q_?SpeciesQ ][ expr_ ] := ParityOddQ[expr, {q}]


ParityEvenQ[ qq:{__?SpeciesQ} ][ expr_ ] := ParityEvenQ[expr, qq]

ParityOddQ[ qq:{__?SpeciesQ} ][ expr_ ] := ParityOddQ[expr, qq]


ParityEvenQ[ expr_  ] := ParityEvenQ[expr, Representables[expr]] /;
  Not @ FreeQ[expr, _Ket]

ParityOddQ[ expr_  ] := ParityOddQ[expr, Representables[expr]] /;
  Not @ FreeQ[expr, _Ket]


ParityEvenQ[ expr_List, op_List ] := Map[ ParityEvenQ[#,op]&, expr ] /;
  Not @ FreeQ[expr, _Ket]

ParityOddQ[ expr_List, op_List ] := Map[ ParityOddQ[#,op]&, expr ] /;
  Not @ FreeQ[expr, _Ket]


ParityEvenQ[ z_?ComplexQ expr_, op_List ] := ParityEvenQ[expr, op] /;
  Not @ FreeQ[expr, _Ket]

ParityOddQ[ z_?ComplexQ expr_, op_List ] := ParityOddQ[expr, op] /;
  Not @ FreeQ[expr, _Ket]


ParityEvenQ[ expr_Plus, op_List ] :=
  And @@ ParityEvenQ[Cases[expr, _Ket, Infinity], op] /;
  Not @ FreeQ[expr, _Ket]

ParityOddQ[ expr_Plus, op_List ] :=
  And @@ ParityOddQ[Cases[expr, _Ket, Infinity], op] /;
  Not @ FreeQ[expr, _Ket]


ParityEvenQ[ Ket[<||>], {} ] := True

ParityOddQ[ Ket[<||>], {} ] := False


ParityEvenQ[ v_Ket, op:{__?SpeciesQ} ] :=
  Not[ Xor @@ Map[ParityOddQ[v,#]&, FlavorNone @ op] ]

ParityOddQ[ v_Ket, op:{__?SpeciesQ} ] :=
  Xor @@ Map[ParityOddQ[v,#]&, FlavorNone @ op]

(* *********************************************************************** *)

Once[ TheRotation::usage = "TheRotation[\[Phi], 1], TheRotation[\[Phi], 2], TheRotation[\[Phi], 3] give the 2x2 matrix representing the rotation by angle \[Phi] around the x, y, and z axis, respective in the two-dimensional Hilbert  space.\nTheRotation[{x1, n1,}, {x2, n2,}, ...] =
  TheRotation[x1, n1] \[CircleTimes] Rotation[x2, n2] \[CircleTimes] ..." ]

TheRotation[_, 0] := ThePauli[0]

TheRotation[ph_, n:(1|2|3)] :=
  Cos[ph/2] * ThePauli[0] - I*Sin[ph/2] * ThePauli[n]

TheRotation[{ph_, n:(0|1|2|3)}] := TheRotation[ph, n]

TheRotation[a:{_, (0|1|2|3)}, b:{_, (0|1|2|3)}..] :=
  CircleTimes @@ Map[TheRotation, {a, b}]


Once[ TheEulerRotation::usage = "TheEulerRotation[{a,b,c}] = TheRotation[a,3].TheRotation[b,2].TheRotation[c,3] and TheEulerRotation[{a,b}]=TheEulerRotation[{a,b,0}] return the matrices corresponding to the Euler rotations in SU(2) space." ]

TheEulerRotation[ {phi_, theta_, chi_} ] := {
  {Cos[theta/2]*Exp[-I*(phi+chi)/2], -Sin[theta/2]*Exp[-I*(phi-chi)/2]},
  {Sin[theta/2]*Exp[+I*(phi-chi)/2],  Cos[theta/2]*Exp[+I*(phi+chi)/2]}
 }

TheEulerRotation[ {phi_,theta_} ] := TheEulerRotation[ {phi, theta, 0} ]

TheEulerRotation[a:{_, _, _}, b:{_, _, _}..] :=
  CircleTimes @@ Map[TheEulerRotation, {a, b}]


TheEulerAngles::usage = "TheEulerAngles[U] gives the Euler angles {\[Alpha],\[Beta],\[Gamma]} of the SU(2) matrix U, where -\[Pi] < \[Alpha],\[Gamma] \[LessEqual] \[Pi] and 0 \[LessEqual] \[Beta] \[LessEqual] \[Pi]. TheEulerRotation[TheEulerAngles[U]] == U.\nTheEulerAngles[expr] gives the Euler angles {\[Alpha],\[Beta],\[Gamma]} of the single-qubit unitary operator given by expr in terms of Pauli operators."

TheEulerAngles::notUni = "`` is not a 2x2 special unitary matrix."

TheEulerAngles[U_?MatrixQ] := Module[
  { arg = Arg[U],
    ang = {0, 0, 0} },
  
  If[ Chop[U.Topple[U]] != {{1,0},{0,1}},
    Message[TheEulerAngles::notUni, U],
    If [ Chop[Det[U]] != 1, 
      Message[TheEulerAngles::notUni, U]
     ];
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


(* *********************************************************************** *)

Rotation::usage = "Rotation[\[Phi], 1], Rotation[\[Phi], 2], Rotation[\[Phi], 3] represent the rotations by angle \[Phi] around the x, y, and z axis, respective, in a two-dimensioinal Hilbert space.\nRotation[{x1, n1}, {x2, n2}, ...] = Rotation[x1, n1] \[CircleTimes] Rotation[x2, n2] \[CircleTimes] ..."

Rotation[_, 0] := Pauli[0]

Rotation[phi_, n:(1|2|3)] := Cos[phi/2]*Pauli[0]-I*Sin[phi/2]*Pauli[n]

Rotation[{phi_, n:(0|1|2|3)}] := Rotation[phi, n]

Rotation[a:{_, (0|1|2|3)}, b:{_, (0|1|2|3)}..] :=
  CircleTimes @@ Map[Rotation, {a, b}]


EulerRotation::usage = "EulerRotation[{a, b, c}] = Rotation[a, 3].Rotation[b, 2].Rotation[c, 3] represent the Euler rotation by angles a, b, c in a two-dimensional Hilbert space."

EulerRotation[ {a_, b_, c_} ] :=
  Rotation[a, 3].Rotation[b, 2].Rotation[c, 3]

EulerRotation[ a:{_, _, _}, b:{_, _, _}.. ] :=
  CircleTimes @@ Map[EulerRotation, {a, b}]


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
Dot[ Pauli[0], Pauli[n:(0|1|2|3|4|5|6|7|8)] ] := Pauli[n]

Pauli /:
Dot[ Pauli[n:(0|1|2|3|4|5|6|7|8)], Pauli[0] ] := Pauli[n]

Pauli /:
Dot[ Pauli[n:(0|1|2|3)], Pauli[n:(0|1|2|3)] ] := Pauli[0]

Pauli /:
Dot[ Pauli[7], Pauli[7] ] := Pauli[3]

Pauli /:
Dot[ Pauli[-7], Pauli[-7] ] := Pauli[3]

Pauli /:
Dot[ Pauli[8], Pauli[8] ] := Pauli[7]

Pauli /:
Dot[ Pauli[-8], Pauli[-8] ] := Pauli[-7]

Pauli /:
Dot[ Pauli[7], Pauli[-7] ] := Pauli[0]

Pauli /:
Dot[ Pauli[-7], Pauli[7] ] := Pauli[0]

Pauli /:
Dot[ Pauli[8], Pauli[-8] ] := Pauli[0]

Pauli /:
Dot[ Pauli[-8], Pauli[8] ] := Pauli[0]

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


Pauli /:
Dot[ Pauli[n:(4|5|6|7|8)], Pauli[k:(1|2|3|4|5|6|7|8)] ] :=
  ExpandAll @ Dot[ Pauli[n /. $PauliShortCuts], Pauli[k /. $PauliShortCuts] ]

Pauli /:
Dot[ Pauli[k:(1|2|3|4|5|6|7|8)], Pauli[n:(4|5|6|7|8)] ] :=
  ExpandAll @ Dot[ Pauli[k /. $PauliShortCuts], Pauli[n /. $PauliShortCuts] ]

Pauli /:
Dot[ a:Pauli[(-7|-8)], b_Pauli ] := Dot[ Dagger[ a /. $PauliShortCuts ], b ]

Pauli /:
Dot[ a_Pauli, b:Pauli[(-7|-8)] ] := Dot[ a, Dagger[ b /. $PauliShortCuts ] ]

$PauliShortCuts = {
  4 -> Raise,
  5 -> Lower,
  6 -> Hadamard,
  7 -> Quadrant,
  8 -> Octant
 }


Pauli /:
Dot[ Pauli[a_, b__], Pauli[c_, d__] ] :=
  CircleTimes @@ Dot @@@ Transpose[{ Pauli /@ {a,b}, Pauli /@ {c,d} }]
  
Pauli /:
Dot[ Pauli[a_, b__], Ket[c_, d__] ] := CircleTimes @@
  Dot @@@ Transpose[{ Pauli /@ {a,b}, Ket /@ {c,d} }]

Pauli /:
Dot[ Bra[c_, d__], Pauli[a_, b__] ] := CircleTimes @@
  Dot @@@ Transpose[{ Bra /@ {c,d}, Pauli /@ {a,b} }]

(* *********************************************************************** *)
(*     </Dot for Pauli and Bra/Ket>                                        *)
(* *********************************************************************** *)


CircleTimes::usage = "a \[CircleTimes] b \[CircleTimes] c or CircleTimes[a,b,c] represents the tensor product of Hilbert space vectors or operators on them.
  When a, b, c, ... are vectors or matrices, it returns the matrix direct product of them."

SetAttributes[CircleTimes, {ReadProtected}]

CircleTimes[] = 1 (* See also Times[]. *)

CircleTimes[a_] := a (* See also Times[]. *)

(* NOTE: DO NOT set the Flat and OneIdentity attributes for
   Cirlcetimes. Otherwise, the following definitions cause infinite loops. *)

HoldPattern[ CircleTimes[ args__ ] ] := Garner @ Block[
  { F },
  Distribute[ F[args] ] /. { F -> CircleTimes }
 ] /; DistributableQ[args]

CircleTimes[a___, z_?ComplexQ b_, c___] := z CircleTimes[a, b, c]

CircleTimes[a___, 0, c___] := 0
(* This happens when some Kets are null. *)

(* On matrices, it operates the same as KroneckerProduct[]. *)
CircleTimes[A__?MatrixQ] := KroneckerProduct[A]

(* For vectors, our CircleTimes[] is different from KroneckerProduct[]. *)
CircleTimes[A__?VectorQ] := Flatten[ TensorProduct[A] ]


(* Direct Sum *)

BlockDiagonalMatrix::usage = "BlockDiagonalMatrix[{a,b,c,...}] returns a matrix with the matrices a, b, c, ... as its blocks. BlockDiagonalMatrix[a,b,c,...] is the same."

BlockDiagonalMatrix[m:(_?MatrixQ) ..] := BlockDiagonalMatrix[{m}]

BlockDiagonalMatrix[m:{__?MatrixQ}] := Module[
  {x, y},
  {x, y} = Transpose @ Map[Dimensions] @ m;
  x = Range[Accumulate @ Most @ Prepend[x, 1], Accumulate @ x];
  y = Range[Accumulate @ Most @ Prepend[y, 1], Accumulate @ y];
  x = Catenate @ Map[Tuples] @ Transpose @ {x, y};
  SparseArray @ Thread[x -> Flatten @ m]
 ]

SetAttributes[CirclePlus, {ReadProtected}]

CirclePlus::usage = "a \[CirclePlus] b \[CirclePlus] c or CirclePlus[a,b,c]
returns the direct sum of the matrices a, b, and c."

CirclePlus[ m:(_?MatrixQ).. ] := BlockDiagonalMatrix[{m}]

CirclePlus[ v:(_?VectorQ).. ] := Join[v]


(* <Dyad> *)

Dyad::usage = "Dyad[a, b] for two vectors a and b return the dyad (a tensor of order 2 and rank 1) corresponding to the dyadic product of two vectors.\nDyad[v] = Dyad[v, v] for a vector v.\nDyad[a, b, qq] for two associations a and b and for a list qq of Species represents the dyadic product of Ket[a] and Ket[b], i.e., Ket[a]**Bra[b], operating on the systems in qq.\nWhen All is given for qq, the operator acts on all systems without restriction."

(* For simple column vectors *)

Dyad[a_?VectorQ] := KroneckerProduct[a, Conjugate @ a]

Dyad[a_?VectorQ, b_?VectorQ] := KroneckerProduct[a, Conjugate @ b]

(* For Pauli Kets *)

Dyad[Ket[a:(0|1)..], Ket[b:(0|1)..], All|{}] := Pauli[{b} -> {a}]

(* For general Kets *)

Format @ Dyad[a_Association, b_Association, qq:{___?SpeciesQ}] :=
  Row @ { LogicalForm[Ket[a], qq], LogicalForm[Bra[b], qq] }

Dyad /: NonCommutativeQ[ Dyad[___] ] = True

Dyad /:
Kind[ Dyad[_Association, _Association, qq_List] ] := First @ Kind @ qq

Dyad /:
MultiplyGenus[ Dyad[___] ] := "Singleton"

Dyad /:
HoldPattern @ Elaborate[ Dyad[a_, b_, c_List] ] := Module[
  { aa = Lookup[a, c],
    bb = Lookup[b, c],
    op },
  op = Construct @@@ Thread @ {c, Thread[bb -> aa]};
  Garner @ Elaborate[Multiply @@ op]
 ]

Dyad[a_Association, b_Association, {}|All] := Multiply[Ket[a], Bra[b]]
(* NOTE: No particlar reason to store it as Dyad. *)

Dyad[Ket[a_Association], Ket[b_Association], {}|All] :=
  Multiply[Ket[a], Bra[b]]

Dyad[Ket[a_Association], Ket[b_Association], qq:{__?SpeciesQ}] := 
  Dyad[a, b, FlavorNone @ qq]

Dyad[a_Association, b_Association, qq:{__?SpeciesQ}] := Module[
  { rr = KeySort @ GroupBy[qq, Kind] },
  Multiply @@ Map[ Dyad[KeyTake[a, #], KeyTake[b, #], #]&, Values @ rr]
 ] /; Length @ Union @ Kind[qq] > 1


Dyad[a_Plus, b_Plus, qq:(_List|All)] :=
  Garner @ Total @ Flatten @ Outer[Dyad[#1, #2, qq]&, List @@ a, List @@ b]

Dyad[a_Plus, b_, qq:(_List|All)] :=
  Garner @ Total @ Flatten @ Outer[Dyad[#1, #2, qq]&, List @@ a, List @ b]

Dyad[a_, b_Plus, qq:(_List|All)] :=
  Garner @ Total @ Flatten @ Outer[Dyad[#1, #2, qq]&, List @ a, List @@ b]

Dyad[z_ a_, b_, qq:(_List|All)] :=
  Garner[z Dyad[a, b, qq]] /; FreeQ[z, _Ket]

Dyad[a_, z_ b_, qq:(_List|All)] :=
  Garner[Conjugate[z] Dyad[a, b, qq]] /; FreeQ[z, _Ket]


Dyad[a_, b_] := Module[
  { qq = Cases[{a, b}, Ket[c_Association] :> Keys[c], Infinity] },
  Dyad[a, b, Union @ Flatten @ qq]
 ] /; Not @ Or[FreeQ[a, _Ket], FreeQ[b, _Ket]]


HoldPattern @ Multiply[
  pre___,
  Dyad[a_Association, b_Association, qq_List],
  Dyad[b_Association, c_Association, qq_List],
  post___
 ] := Multiply[pre, Dyad[a, c, qq], post]

HoldPattern @ Multiply[
  pre___,
  op_?AnySpeciesQ, Dyad[a_Association, b_Association, c_List],
  post___
 ] := Multiply[
   pre,
   Dyad[ op ** Ket[a], Ket[b], c ],
   post
  ] /; MemberQ[c, FlavorMute @ Peel @ op]

HoldPattern @ Multiply[
  pre___,
  Dyad[a_Association, b_Association, c_List], op_?AnySpeciesQ,
  post___
 ] := Multiply[
   pre,
   Dyad[ Ket[a], Dagger[op] ** Ket[b], c ],
   post
  ] /; MemberQ[c, FlavorMute @ Peel @ op]

HoldPattern @ Multiply[
  pre___,
  dd:Dyad[_Association, _Association, qq_List], op_?AnySpeciesQ,
  post___
 ] := Multiply[
   pre,
   op, dd,
   post
  ] /; With[
    { sp = FlavorMute @ Peel @ op },
    And[
      Kind[dd] == Kind[op],
      Not @ MemberQ[qq, sp],
      Not @ OrderedQ @ {First @ qq, sp}
     ]
   ]

HoldPattern @ Multiply[
  pre___,
  op_?AnySpeciesQ, dd:Dyad[_Association, _Association, qq_List],
  post___
 ] := Multiply[
   pre,
   dd, op,
   post
  ] /; With[
    { sp = FlavorMute @ Peel @ op },
    And[
      Kind[dd] == Kind[op],
      Not @ MemberQ[qq, sp],
      Not @ OrderedQ @ {sp, First @ qq}
     ]
   ]


HoldPattern @ Multiply[
  pre___,
  Bra[v_Association],
  Dyad[a_Association, b_Association, qq_List],
  post___
 ] := Module[
   { w = KeyDrop[v, qq],
     u = KeyTake[v, qq] },
   BraKet[u, a] Multiply[pre, Bra[w], Bra[b], post]
  ]

HoldPattern @ Multiply[
  pre___,
  Dyad[a_Association, b_Association, qq_List],
  Ket[v_Association],
  post___
 ] := Module[
   { w = KeyDrop[v, qq],
     u = KeyTake[v, qq] },
   BraKet[b, u] Multiply[pre, Ket[a], Ket[w], post]
  ]

(* </Dyad> *)


DyadExpression::usage = "DyadExpression[expr,{s1,s2,..}] converts the operator expression expr to the form in terms of Dyad acting on the systems s1, s2, .... If the systems are not specified, then they are extracted from expr.\nDyadExpression[mat,{s1,s2,...}] converts the matrix representation into an operator expresion in terms of Dyad acting on the systems s1, s2, ...."

DyadExpression[expr_] := 
  DyadExpression[expr, NonCommutativeSpecies[expr]]

DyadExpression[expr_, q_?SpeciesQ] := 
  DyadExpression[expr, FlavorNone@{q}]

DyadExpression[expr_, qq : {__?SpeciesQ}] := 
  DyadExpression[Matrix[expr, FlavorNone@qq], FlavorNone@qq]

DyadExpression[mat_?MatrixQ, q_?SpeciesQ] := 
  DyadExpression[mat, FlavorNone@{q}]

DyadExpression[mat_?MatrixQ, qq:{__?SpeciesQ}] := Module[
  { rr = FlavorNone @ qq,
    dd = Dimension @ qq,
    mm },
  mm = Tensorize[mat, Flatten @ Transpose  @  {dd, dd}];
  mm = Association @ Most @ ArrayRules @ mm;
  Total @ KeyValueMap[theDyadExpr[#1, dd, rr] #2 &, mm]
 ]

theDyadExpr[ij_, dd_, qq_] := Module[
  { kl = Transpose @ Partition[ij - 1, 2] },
  Dyad[
    KetTrim @ AssociationThread[qq -> First @ kl],
    KetTrim @ AssociationThread[qq -> Last @ kl],
    qq
   ]
 ]


(* ********************************************************************* *)

Zero::usage = "Zero[n] return an array of length n with all elements zero.\nZero[m, n, ...] \[Congruent] Zero[{m, n, ...}] returns an m x n x ... tensor with all elements zero."

Zero[mn__Integer] := SparseArray[{}, {mn}]

Zero[{mn__Integer}] := SparseArray[{}, {mn}]


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

(* ********************************************************************* *)

PauliExtract::usage = "PauliExtract has been deprecated. Use PauliDecompose instead."

PaulieExtract[m_?MatrixQ, dd_] := (
  Message[Q3General::obsolete, "PaulieExtract", "PauliDecompose"];
  PauliDecompose[m, dd]
 )


PauliExtractRL::usage = "PauliExtractRL has been deprecated. Use PauliDecomposeRL instead."

PaulieExtractRL[m_?MatrixQ, dd_] := (
  Message[Q3General::obsolete, "PaulieExtractRL", "PauliDecomposeRL"];
  PauliDecomposeRL[m, dd]
 )


(* ********************************************************************* *)

PauliDecompose::usage = "PauliDecompose[m] gives the coefficients in the Pauli decomposition of m as a tensor of rank n, where m is a 2^n x 2^n matrix."

PauliDecompose::badarg = "The argument M of PauliDecompose[M] should be a matrix of size 2^n*2^n."

PauliDecompose[dd:(0|1|2|3)..][m_?MatrixQ] := PauliDecompose[m, {dd}]

PauliDecompose[{dd:(0|1|2|3)..}][m_?MatrixQ] := PauliDecompose[m, {dd}]


PauliDecompose[m_?MatrixQ, d:(0|1|2|3)] := PauliDecompose[m, {d}]

PauliDecompose[m_?MatrixQ, idx:{ (0|1|2|3).. }] :=
  Tr @ Dot[m, CircleTimes @@ ThePauli /@ idx] / Length[m]


PauliDecompose[ m_?MatrixQ ] := Module[
  { n = Log[2, Length[m]],
    idxTable, idxList },
  If [ !IntegerQ[n],
    Message[PauliDecompose::badarg];
    Return[0]
   ];
  idxTable = Table[{0, 1, 2, 3}, {n}];
  idxList = Outer[ List, Sequence @@ idxTable ];
  Map[ PauliDecompose[m, #]&, idxList, {n} ]
 ]


PauliCompose::usage = "PauliCompose[coeff] constructs a 2^n x 2^n matrix using the coefficients specified in the tensor coeff.\nIt is an inverse of PauliDecompose and coeff is usually the tensor returned by it."

PauliCompose[c_?TensorQ] := Module[
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


PauliDecomposeRL[m_?MatrixQ] := Module[
  { nn = Log[2, Length[m]],
    idxTable, idxList },
  If [ !IntegerQ[nn],
       Message[PauliDecompose::badarg];
       Return[0]
   ];
  idxTable = Table[{0,3,4,5}, {nn}];
  idxList = Outer[List,Sequence@@idxTable];
  Map[ PauliDecomposeRL[m,#]&, idxList, {nn} ]
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

(* ********************************************************************* *)

SchmidtDecomposition::usage = "SchmidtDecomposition[v, {m, n}] returns the Schmidt decomposition of the pure state vector v of a bipartite system of dimensions m and n.\nSchmidtDecomposition[v, {d1, d2, ...}, {i1, i2, ...}, {j1, j2, ...}] returns the Schmidt decomposition of a pure state vector v for a system of multiple subsystems of dimensions d1, d2, .... The i1th, i2th, ... systems are grouped into one part and the j1th, j2th, ... subsystems are grouped into the other part."

SchmidtDecomposition::bad = "Incompatible dimensions `1` x `2` for a vector of length `3`."

SchmidtDecomposition[v_?VectorQ] :=
  SchmidtDecomposition[v, {Length[v]/2, 2}]

SchmidtDecomposition[v_?VectorQ, n_Integer] :=
  SchmidtDecomposition[v, {Length[v]/n, n}]

SchmidtDecomposition[v_?VectorQ, {n_Integer, Automatic}] :=
  SchmidtDecomposition[v, {n, Length[v]/n}]

SchmidtDecomposition[v_?VectorQ, {m_Integer, n_Integer}] := Module[
  { L = Min[m, n],
    U, S, V },
  { U, S, V } = SingularValueDecomposition @ Partition[v, n];
  { Diagonal @ S,
    Take[ Transpose @ U, L ],
    Take[ ConjugateTranspose @ V, L ]
   }
 ] /; Length[v] == m*n

SchmidtDecomposition[v_?VectorQ, {m_Integer, n_Integer}] := (
  Message[SchmidtDecomposition::bad, m, n, Length@v];
  {{1}, v, {1}}
 )

SchmidtDecomposition[v_?VectorQ, ii:{__Integer}, jj:{__Integer}] :=
  SchmidtDecomposition[v, ConstantArray[2, Length[ii]+Length[jj]], ii, jj]

SchmidtDecomposition[
  v_?VectorQ, dd:{__Integer}, ii:{__Integer}, jj:{__Integer}
 ] := Module[
   { M = Tensorize[v, dd],
     u },
   u = Flatten@Transpose[M, Ordering@Join[ii, jj]];
   SchmidtDecomposition[ u, Times @@@ { Part[dd, ii], Part[dd, jj] } ]
  ]

(* ********************************************************************* *)

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
  ii = Join[ Range[1,r,2], Range[2,r,2] ];
  Transpose[ ArrayReshape[m, Join[oo,ee]], ii ]
 ]

Tensorize[m_?MatrixQ] := Module[
  { n = Log[2, Length[m]],
    ii },
  If[ !IntegerQ[n],
    Message[Tensorize::notQubit];
    Return[m]
   ];
  ii = Join[ Range[1,2*n,2], Range[2,2*n,2] ];
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


PartialTranspose::usage = "..."

PartialTranspose[m_?MatrixQ, dd:{__Integer}, jj:{___Integer}] := Module[
  { tns = Tensorize[m, Flatten @ Transpose @ {dd, dd}],
    cyc = Cycles @ Transpose @ {2*jj-1, 2*jj} },
  TensorFlatten @ Transpose[tns, cyc]
 ]


PartialTrace::usage = "PartialTrace[m, {i,j,...}] takes the partial trace over the qubits i, j, ... and returns the resulting reduced matrix.\nPartialTrace[m, {m,n,...}, {i,j,...}] assumes a system of dimensions m, n, ..., takes the partial trace over the subsystems i, j, ..., and returns the resulting reduced matrix.\nPartialTrace[v, {i,j,...}] and PartialTrace[v, {m,n,...}, {i,j,...}] are the same but operate on the column vector v. Note that the result is a square matrix, i.e., the reduced density matrix, not a pure-state column vector any longer."

PartialTrace::notSubsystem = "Illegal qubit index(es) in ``."

PartialTrace[m_?MatrixQ, dd:{__Integer}, jj:{___Integer}] := Module[
  { M = Tensorize[m, Flatten @ Transpose @ {dd, dd}] },
  If[ !ContainsOnly[jj, Range @ Length[dd]],
    Message[PartialTrace::notSubsystem, jj];
    Return[m]
   ];
  TensorFlatten @ TensorContract[ M, Transpose @ {2jj-1,2jj} ]
 ]

PartialTrace[m_?MatrixQ, jj:{___Integer}] :=
  PartialTrace[m, ConstantArray[2, Log[2, Length[m]]], jj]

PartialTrace[v_?VectorQ, dd:{__Integer}, {}] :=
  KroneckerProduct[v, Conjugate[v]]

PartialTrace[v_?VectorQ, dd:{__Integer}, jj:{__Integer}] := Module[
  { nn = Range @ Length @ dd,
    ii, vv },
  If[ !ContainsOnly[jj, nn],
    Message[PartialTrace::notSubsystem, jj];
    Return[m] ];
  ii = Supplement[nn, jj];
  vv = Flatten[Tensorize[v, dd], {jj, ii}];
  Total @ Map[ KroneckerProduct[#,Conjugate[#]]& ] @ vv
 ]
(* REMARK: In many cases, handling density matrix is computationally
   inefficient. In this sense, returning the list of states involved in the
   mixed state will provide the user with more flexibility. *)

PartialTrace[v_?VectorQ, {}] := KroneckerProduct[v, Conjugate[v]]

PartialTrace[v_?VectorQ, jj:{__Integer}] :=
  PartialTrace[v, ConstantArray[2,Log[2,Length[v]]], jj]


PartialTrace[expr_, q_?SpeciesQ, func_] := PartialTrace[expr, {q}, func]

PartialTrace[expr_, qq:{__?SpeciesQ}, func_] := Module[
  { rr = FlavorNone @ Cases[qq, _?NonCommutativeQ],
    ss = NonCommutativeSpecies[expr],
    dd, jj },
  ss = Union[ss, rr];
  dd = Dimension[ss];
  jj = Flatten @ Map[FirstPosition[ss, #]&, rr];
  func[ PartialTrace[Matrix[expr, ss], dd, jj], Complement[ss, rr] ]
 ]


Purification::usage = "Purification[m] returns the purification of the mixed state m."

Purification[m_?MatrixQ] := Module[
  {val, vec},
  {val, vec} = Eigensystem[m]; (* m is supposed to be Hermitian. *)
  Sqrt[val] . MapThread[CircleTimes, {vec, One @ Dimensions @ m}]
 ]


Purge::usage = "Purge[m] returns the pure state closest to the mixed state m.\nIt is different from purification."

Purge[m_?MatrixQ] := Module[
  {val, vec},
  {val, vec} = Eigensystem[m]; (* m is suppposed to be Hermitian. *)
  {val, vec} = Last @ Sort @ Transpose @ {val, vec};
  (* returns the eigenvector belonging to the largest eigenvalue *)
  vec
 ]


PauliEmbed::usage = "PauliEmbed[A, qubits, n] returns the fully expanded form of A operating on the whole tensor product space. Here A is a linear operator on the Hilbert space of qubits={i, j, k, ...} among total n qubits."

PauliEmbed[A_?MatrixQ, bits_List, len_Integer] := Module[
  { a, b, c, d, none,
    n = Length[bits],
    AA = PauliDecompose[A] },
  a = Table[1, {len}];
  b = Table[Range[4], {n}];
  b = Flatten @ Outer[none, Sequence @@ b];
  b = Apply[List, b, 1];
  c = ReplacePart[a, #, List /@ bits, List /@ Range[n]]& /@ b;
  d = Table[ 0, Evaluate[ Sequence @@ Table[{4}, {len}] ] ];
  PauliCompose @ ReplacePart[d, AA, c, b]
 ]

PauliApply::usage = "PauliApply[A, qubits, v] applies the linear operator A on
  qubits of the state vector v."

PauliApply[A_?MatrixQ, bits_List, v_?VectorQ] := With[
  { n = Log[2, Length[v]] },
  PauliEmbed[A, bits, n] . v
 ]


KetPermute::usage = "KetPermute[v, {q1, q2, ...}, cycles] returns a new Ket permuting the values of the particles q1, q2, ... in Ket v."

(* for Pauli Kets *)

KetPermute[Ket[ss__], perm_Cycles] :=
  Ket @@ Permute[{ss}, perm]

KetPermute[Ket[ss__],
  group:(_SymmetricGroup|_AlternatingGroup|_PermutationGroup)
 ] := Ket @@@ Permute[{ss}, group]

KetPermute[expr_,
  spec:(_Cycles|_SymmetricGroup|_AlternatingGroup|_PermutationGroup)
 ] := expr /. { v_Ket :> KetPermute[v, spec] }

KetPermute[expr_, pp:{__Cycles}] :=
  Map[ KetPermute[expr, #]&, pp ]


(* for general Kets *)

KetPermute[v:Ket[_Association], qq:{__}, perm_Cycles] := Module[
  { vv = v[qq] },
  vv = Permute[vv, perm];
  Ket[v, qq -> vv]
 ]

KetPermute[v:Ket[_Association], qq:{__},
  group:(_SymmetricGroup|_AlternatingGroup|_PermutationGroup)
 ] := Module[
   { vv = v[qq] },
   vv = Permute[vv, group];
   Map[ Ket[v, qq -> #]&, vv ]
  ]

KetPermute[expr_, qq:{__},
  spec:(_Cycles|_SymmetricGroup|_AlternatingGroup|_PermutationGroup)
 ] := expr /. { v:Ket[_Association] :> KetPermute[v, qq, spec] }

KetPermute[expr_, qq:{__}, pp:{__Cycles}] :=
  Map[ KetPermute[expr, qq, #]&, pp ]

(* operator form *)
KetPermute[qq:{__}, spec_][v_] := KetPermute[v, qq, perm]


KetSymmetrize::usage = "KetSymmetrize[v, {q1, q2, ...}, {cyc, sign}] returns a new Ket resulting by symmetrizing the input Ket v with respect to the particles q1, q2, .... With sign = 1 (sign = -1), the Ket is symmerized (anti-symmetrized)."

KetSymmetrize[ 0, qq:{__}, {c_Cycles, s:(-1|1)} ] := 0

KetSymmetrize[ v_Ket, qq:{__}, {c_Cycles, s:(-1|1)} ] := Module[
  { vv = KetPermute[v, qq, c],
    ff },
  ff = If[ v === vv, 2, Sqrt[2] ];
  Sort[{v, vv}] . {1, s} / ff
 ]

KetSymmetrize[ vv_List, qq:{__}, {c_Cycles, s:(-1|1)} ] := DeleteCases[
  Simplify @ Union @ Map[ KetSymmetrize[#, qq, {c, s}]&, vv ],
  0
 ]

KetSymmetrize[ expr_, qq:{__}, {c_Cycles, s:(-1|1)} ] := (
  expr /. {
    v:_Ket :> KetSymmetrize[v, qq, {c,s}]
   }
 ) /; Not @ FreeQ[expr, _Ket]

KetSymmetrize[ expr_, qq:{__}, cc:{{_Cycles, (-1|1)}..} ] :=
  Simplify @ Fold[ KetSymmetrize[#1,qq,#2]&, expr, cc ] /;
  Not @ FreeQ[expr, _Ket]


(* total symmetrization for Pauli Kets *)

KetSymmetrize[any_] := KetSymmetrize[any, 1]

KetSymmetrize[v_Ket, 1] := Module[
  { vv },
  vv = KetPermute[v, SymmetricGroup[Length @ v]];
  Total @ vv / Sqrt[Length @ vv]
 ]

KetSymmetrize[vv:{__}, 1] :=
  Union[ KetSymmetrize[#, 1]& /@ vv ]

KetSymmetrize[expr_, 1] :=
  ReplaceAll[ expr, v_Ket :> KetSymmetrize[v, 1] ]


KetSymmetrize[v_Ket, -1] := Module[
  { n = Length @ v,
    vv = Sort @ v,
    ff },
  vv = Permute[vv, SymmetricGroup[n]];
  ff = Signature /@ vv;

  ff . vv / Sqrt[Length @ vv]
 ]

KetSymmetrize[vv:{__}, -1] := DeleteCases[
  Union[ KetSymmetrize[#, -1]& /@ vv ],
  0
 ]

KetSymmetrize[expr_, -1] :=
  ReplaceAll[ expr, v_Ket :> KetSymmetrize[v, -1] ]


(* total symmetrization for general Kets *)

KetSymmetrize[any_, qq:{__?SpeciesQ}] := KetSymmetrize[any, qq, 1]

KetSymmetrize[v_Ket, qq:{__?SpeciesQ}, 1] := Module[
  { vv },
  vv = KetPermute[v, qq, SymmetricGroup[Length @ qq]];
  Total @ vv / Sqrt[Length @ vv]
 ]

KetSymmetrize[vv:{__}, qq:{__?SpeciesQ}, 1] :=
  Union[ KetSymmetrize[#, qq, 1]& /@ vv ]

KetSymmetrize[expr_, qq:{__?SpeciesQ}, 1] :=
  ReplaceAll[ expr, v_Ket :> KetSymmetrize[v, qq, 1] ] /;
  Not @ FreeQ[expr, _Ket]


KetSymmetrize[v_Ket, qq:{__?SpeciesQ}, -1] := Module[
  { n = Length @ qq,
    vv = Sort @ v[qq],
    ff },
  vv = Permute[vv, SymmetricGroup[n]];
  ff = Signature /@ vv;

  vv = Map[ Ket[v, qq -> #]&, vv ];
  ff . vv / Sqrt[Length @ vv]
 ]

KetSymmetrize[vv:{__}, qq:{__?SpeciesQ}, -1] := DeleteCases[
  Union[ KetSymmetrize[#, qq, -1]& /@ vv ],
  0
 ]

KetSymmetrize[expr_, qq:{__?SpeciesQ}, -1] :=
  ReplaceAll[ expr, v_Ket :> KetSymmetrize[v, qq, -1] ] /;
  Not @ FreeQ[expr, _Ket]


PermutationMatrix::usage = "PermutationMatrix[perm, n] returns the n x n matrix representation of the permutation perm.\nPermutationMatrix[perm] first tries to find the proper dimension of the matrix from perm and returns the permutation matrix."

PermutationMatrix[perm_?PermutationCyclesQ] :=
  PermutationMatrix[ perm, Max @ Cases[perm, _Integer, Infinity] ]

PermutationMatrix[perm_?PermutationCyclesQ, n_Integer] := 
  Permute[ IdentityMatrix[n], perm ]


RandomVector::usage = "RandomVector is a shortcut to RandomComplex.\nRandomVector[] gives a two-dimensional random vector.\nRanbdomVector[n] gives an n-dimensional random vector.\nRandomVector[range, n] \[Congruent] RandomComplex[range, n]."

RandomVector[] := RandomComplex[(1+I){-1, 1}, 2]

RandomVector[n_Integer] := RandomComplex[(1+I){-1, 1}, n]

RandomVector[range_, n_Integer] := RandomComplex[range, n]


RandomMatrix::usage = "RandomMatrix is a shortcut to RandomComplex.\nRandomMatrix[] returns a randomly generated 2x2 matrix.\nRanbdomMatrix[n] returns an nxn random matrix.\nRandomMatrix[range, n] \[Congruent] RandomComplex[range, {n, n}].\nRandomMatrix[range, {m, n}] \[Congruent] RandomComplex[range, {m, n}]."

RandomMatrix[] := RandomComplex[(1+I){-1, 1}, {2, 2}]

RandomMatrix[n_Integer] := RandomComplex[(1+I){-1, 1}, {n, n}]

RandomMatrix[mn:{_Integer, _Integer}] := RandomComplex[(1+I){-1, 1}, mn]

RandomMatrix[range_, n_Integer] := RandomComplex[range, {n, n}]

RandomMatrix[range_, mn:{_Integer, _Integer}] := RandomComplex[range, mn]


RandomHermitian::usage = "RandomHermitian[range, n] gives a randomly generated n x n Hermitian matrix. The range specifies the range (see RandomComplex) of the elements."

RandomHermitian[] := RandomHermitian[(1+I){-1, 1}, 2]

RandomHermitian[n_Integer] := RandomHermitian[(1+I){-1, 1}, n]

RandomHermitian[range_, n_Integer] := With[
  { m = RandomComplex[range, {n, n}] },
  ( m + ConjugateTranspose[m] ) / 2
 ]

RandomUnitary::usage = "RandomUnitary[n] gives a randomly generated n x n Unitary matrix. The range specifies the range (see RandomComplex) of the elements."

RandomUnitary[] := RandomUnitary[2]

RandomUnitary[n_Integer] := With[
  { H = RandomHermitian[(1+I){-1,1}, n] (2 Pi / Sqrt[2]) },
  MatrixExp[-I H]
 ]


BasisComplement::usage = "BasisComplement[a, b] returns the subspace B\[UpTee] of H that is orgohtonal to B, where H is the Hilbert space spanned by the basis a, and B is the subspace of H spanned by the basis b."

BasisComplement[a_List, b_List] := Module[
  { Pr, cc, mm, dd, u, v },
  Pr = Total @ Map[(# ** Dagger[#]) &, b];
  cc = DeleteCases[ Union[a - Pr ** a], 0 ];
  mm = Outer[Multiply, Dagger @ a, cc];
  {u, d, v} = SingularValueDecomposition[mm];
  dd = PseudoInverse[d];
  DeleteCases[ Garner[cc.v.dd], 0 ]
 ]


WignerFunction::usage = "WignerFunction[j,m1,m2,\[Beta]] returns the matrix element WignerFunction[j,m1,m2,\[Beta]] = TheBra[j,m1].U[y,\[Beta]].TheKet[j,m2] of the rotation operator U[y,\[Beta]] around the spin y-axis by angule \[Beta] between the two angular momentum states TheKet[j,m1] and TheKet[j,m2] (notice the same j). These matrix elements are useful to calculate the matrix elements of an arbitrary rotation operator for large angular momentum."

(* 2016-09-12 Mathematica (v11) seems to handle quite efficiently the relevant
   MatrixExp for large angular momena. In this case, WignerFunction[] is not
   particularly useful (at least on the purpose of Pauli package). *)

WignerFunction[j_, m_, n_, z_] :=
  Conjugate[WignerFunction[j, n, m, -Conjugate[z]]] /; m > n

WignerFunction[j_, m_, n_, z_] :=
  Power[-1, m - n] WignerFunction[j, -m, -n, z] /; m < -n

WignerFunction[j_, m_, n_, z_] := 
  Sqrt[(j + m)! (j - m)! (j + n)! (j - n)!] *
  Power[Cos[z/2], 2 j] / Power[Tan[z/2], m + n] *
  With[
    { tan = Tan[z/2] },
    Sum[
      Power[-1, k - n] * Power[ tan, 2 k] /
        ((j - k)! (j + m + n - k)! (k - m)! (k - n)!),
      {k, n, j} ]
   ]

(* For integer spins *)

WignerFunction[j_, 0, m_, z_] :=
  Power[-1, m] * Sqrt[(j-m)!/(j+m)!] LegendreP[j, m, Cos[z]]

WignerFunction[j_, m_, 0, z_] := Conjugate[ WignerFunction[j, 0, m, z] ]


TraceNorm::usage = "TraceNorm[m] returns the trace norm of the matrix m, that is, Tr @ Sqrt[Dagger[m] ** m]."

TraceNorm[m_?MatrixQ] := With[
  { ss = SingularValueList[m] },
  Norm[ss, 1] (* Schattern norm with p = 1 *)
 ]

TraceDistance::usage = "TraceDistance[a, b] returns the trace distance of the two square matrices a and b, which equals to (1/2) TraceNorm[a - b]."

TraceDistance[a_?MatrixQ, b_?MatrixQ] := (1/2) TraceNorm[a-b]


Fidelity::usage = "Fidelity[\[Rho],\[Sigma]] returns the fidelity of the two mixed states \[Rho] and \[Sigma]."

Fidelity[a_?MatrixQ, b_?MatrixQ] := With[
  {c = MatrixPower[a, 1/2]},
  Tr @ MatrixPower[c.b.c, 1/2]
 ]

Fidelity[a_?VectorQ, b_?MatrixQ] := Chop @ Sqrt[Conjugate[a].b.a]

Fidelity[a_?MatrixQ, b_?VectorQ] := Fidelity[b, a]

Fidelity[a_?VectorQ, b_?VectorQ] := Abs[Conjugate[a].b]


(* ***************************************************************** *)
(*     <GraphForm>                                                   *)
(* ***************************************************************** *)

Vertex::usage = "Vertex[a, b, ...] represents an interaction vertex.\nNot to be confused with Vertices in Graph or related functions."


VertexLabelFunction::usage = "VertexLabelFunction is an option for GraphForm and ChiralGraphForm that specifies the function to generate primities for redering each vertex label.\nSee also VertexLabels."


EdgeLabelFunction::usage = "EdgeLabelFunction is an option for GraphForm and ChiralGraphForm that speicifes the function to generate primities for redering each edge label.\nSee also EdgeLabels."

defaultEdgeLabelFunction[ Rule[edge_, None] ] := Nothing

defaultEdgeLabelFunction[ Rule[edge_, lbl_] ] := Rule[ edge,
  Framed[lbl, FrameStyle -> None, Background -> White]
 ]


GraphForm::usage = "GraphForm[A] converts the matrix A to a graph revealing the connectivity, assuming that the matrix is a linear map on one vector space.\nGraphForm allows the same options as Graph, but their specifications may be slightly different.\nGraphForm is a variation of the built-in function GraphPlot.\nGraphForm[expr] returns a graph visualizing the connectivity of different particles in the expression.\nGraphForm allows all options of Graph.\nSee also ChiralGraphForm, GraphPlot, AdjacencyGraph, IncidenceGraph."

Options[GraphForm] = {
  VertexLabels -> Automatic,
  VertexLabelFunction -> Automatic,
  EdgeLabels -> Automatic,
  EdgeLabelFunction -> Automatic
 }

GraphForm[A_SparseArray?MatrixQ, opts___?OptionQ] := Module[
  { data = Most @ ArrayRules[A] },
  data = KeySort @ Association @ Flatten[ survey /@ data ];
  Return @ BuildGraph[data, opts];
 ]

GraphForm[A_?MatrixQ, opts___?OptionQ] := Module[
  { data = Flatten @ MapIndexed[survey, A, {2}],
    jj = Range @ Max @ Dimensions @ A },
  data = Join[Thread[jj -> jj], data];
  data = KeySort @ Association @ data;
  BuildGraph[data, opts]
 ]

GraphForm[expr_, opts___?OptionQ] := Module[
  { raw, val, data },
  raw = Flatten @ Cases[expr, _Multiply, Infinity];
  val = Coefficient[expr, raw];

  data = KeySort @ Association @ Flatten[ survey /@ Thread[raw -> val] ];
  
  BuildGraph[ data, opts,
    EdgeStyle -> {
      UndirectedEdge[_, _, "Pairing"] -> Directive[Red, Thick],
      UndirectedEdge[_, _, "Interaction"] -> Dashed
     }
   ]
 ]

BuildGraph[data_Association, opts___?OptionQ] := Module[
   { nodes, edges, jj, ee, fVertexLabel, fEdgeLabel },
   
  edges = Normal @ KeySelect[ data, MatchQ[#, _UndirectedEdge]& ];
  nodes = Normal @ KeyDrop[ data, Keys @ edges ];

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

survey::usage = "Survey the matrix and constructs Vertices, Edges and relevant options for the graph corresponding to the matrix."

survey[0, {_Integer, _Integer}] := Nothing

survey[_, {j_Integer, j_Integer}] := Nothing

survey[val_, {i_Integer, j_Integer}] := {
  Sort @ UndirectedEdge[i, j] -> val
 }

survey[{j_Integer, j_Integer} -> val_] := { j -> j }

survey[{i_Integer, j_Integer} -> val_] := {
  i -> i,
  j -> j,
  Sort @ UndirectedEdge[i, j] -> val
 }


HoldPattern @ survey[ Multiply[Dagger[a_], Dagger[b_]] -> val_ ] := {
  a -> a,
  b -> b,
  UndirectedEdge[ Sequence @@ Sort[{a,b}], "Pairing" ] -> val
 }

HoldPattern @ survey[ Multiply[a_?SpeciesQ, b_?SpeciesQ] -> val_ ] := {
  a -> a,
  b -> b,
  UndirectedEdge[ Sequence @@ Sort[{a,b}], "Pairing" ] -> val
 }

HoldPattern @ survey[ Multiply[Dagger[a_], a_?SpeciesQ] -> val_ ] := { a -> a }

HoldPattern @ survey[ Multiply[Dagger[a_], b_?SpeciesQ] -> val_ ] := {
  a -> a,
  b -> b,
  UndirectedEdge @@ Sort[{a,b}] -> val
 }

HoldPattern @ survey[ Multiply[a_, b_, c__] -> val_ ] := Module[
  { nodes = Sort[Peel @ {a,b,c}],
    edges, vtx },
  vtx = Vertex @@ nodes;
  edges = Thread @ UndirectedEdge[vtx, nodes, "Interaction"];
  Join[ {vtx -> val}, Thread[edges -> None] ]
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


convertVertexLabel::usage = "converteVertexLabel[vtx -> lbl] converts the lbl applying $VertexLabelFunction[vtx, lbl]."
  
convertVertexLabel[spec:(None|All|Automatic|"Indexed"|"Name")] := spec

convertVertexLabel[Rule[vtx_, lbl_]] :=
  Rule[vtx, $VertexLabelFunction[vtx, lbl]]


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
  ChiralBuildGraph[ ii, jj, data["edges"], opts,
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
  ChiralBuildGraph[ ii, jj, data["edges"], opts,
    Sequence @@ Normal @ KeyDrop[data, {"nodes", "edges"}],
    VertexStyle -> {Blue, Red}
   ]
 ]

ChiralBuildGraph[
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


Protect[ Evaluate @ $symbs ]

End[]


Q3Protect[]


EndPackage[]
