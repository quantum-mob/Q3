(* ::Package:: *)

BeginPackage["QuantumMob`Q3S`", {"System`"}]

{ TheKet, TheBra };

{ State, StateForm, Operator };
{ RandomState, RandomOperator };

{ KetChop, KetDrop, KetUpdate, KetRule, KetTrim, KetVerify,
  KetFactor, KetPurge, KetSort,
  KetSpecies, KetRegulate, KetMutate,
  KetCanonical };

{ KetNorm, KetNormSquare, KetNormalize, KetOrthogonalize }; 

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

{ ProperSystem, ProperValues, ProperVectors = ProperStates };

{ BlochSphere, BlochVector };

{ Affect };

{ Pauli, Raising, Lowering, Hadamard, Quadrant, Octant, Hexadecant };
{ ThePauli };

{ RaisingLoweringForm };

{ Rotation, EulerRotation,
  TheRotation, TheEulerRotation };

{ RotationAngle, RotationAxis, RotationSystem,
  TheEulerAngles }

{ CircleTimes, CirclePlus };

{ Dyad, DyadForm };

{ Parity, ParityValue, ParityEvenQ, ParityOddQ };

{ PartialTrace, ReducedMatrix, Reduced };

{ PauliCoefficients, PauliSeries, PauliVector };

{ MatrixEmbed };

{ SchmidtDecomposition, SchmidtForm };

{ HilbertSchmidtProduct, HilbertSchmidtNorm, HilbertSchmidtDistance,
  FrobeniusProduct, FrobeniusNorm, FrobeniusDistance };

{ TraceNorm, TraceDistance, Fidelity, ClassicalFidelity };
{ PartialTranspose, PartialTransposeNorm,
  Negativity, LogarithmicNegativity };

{ Purification, Snapping };


Begin["`Private`"]

$symb = Unprotect[CircleTimes, CirclePlus, Ket, Bra]


(**** <TheKet> ****)

TheBra::usage = "TheBra[...] is formally different from but equalt to TheKet[...]."

TheBra[args__] := TheKet[args]

TheKet::usage = "TheKet[0]={1,0}, TheKet[1]={0,1}.
  TheKet[s1,s2,...] = TheKet[s1]\[CircleTimes]TheKet[s2]\[CircleTimes]...."

SyntaxInformation[TheKet] = {"ArgumentsPattern" -> {_}};

TheKet[0] = TheKet[Up] = {1, 0}

TheKet[1] = TheKet[Down] = {0, 1}

TheKet[x_?BinaryQ] = {1-x, x}

TheKet[aa:{(0|1|Up|Down)..}] := Module[
  { bb = aa /. {Up -> 0, Down -> 1},
    k },
  k = 1 + FromDigits[bb, 2];
  SparseArray[{k -> 1}, Power[2, Length @ bb]]
]

(**** </TheKet> ****)


(**** <ThePauli> ****)

ThePauli::usage = "ThePauli[n] (n=1,2,3) returns the Pauli matrix numbered n.
  ThePauli[0] returns the 2\[Times]2 identity matrix. ThePauli[4] and ThePauli[5] represent the raising and lowering operators, respectively, and ThePauli[6] returns the 2\[Times]2 Hadamard matrix. ThePauli[7], ThePauli[8], ThePauli[9] represent the quadrant, octant, and hexadecant phase gates, respectively.\nThePauli[{n1, n2, n3, \[Ellipsis]}] = ThePauli[n1] \[CircleTimes] ThePauli[n2] \[CircleTimes] ThePauli[n3]\[CircleTimes] \[Ellipsis]."

SetAttributes[ThePauli, {NHoldAll, ReadProtected}]

SyntaxInformation[ThePauli] = {"ArgumentsPattern" -> {_}};


ThePauli[kk_SparseArray] := ThePauli[Normal @ kk]

ThePauli[kk:{___, _List, ___}] := ThePauli /@ Thread[kk]
(* Note: similar to the Listable attribute. *)

ThePauli[kk_List] := ThePauli @ ReplaceAll[ kk,
  { All -> {1, 2, 3},
    Full -> {0, 1, 2, 3} }
] /; ContainsAny[kk, {All, Full}]

ThePauli[All] := ThePauli /@ {1, 2, 3}

ThePauli[Full] := ThePauli /@ {0, 1, 2, 3}

ThePauli[] = ThePauli[{}] = {{1}} (* fallback *)


ThePauli[kk:{(_Integer|_Rule)..}] := CircleTimes @@ Map[ThePauli, kk]


ThePauli[0] = SparseArray[{{1, 1} -> 1, {2, 2} -> 1}, {2, 2}]

ThePauli[1] = ThePauli[-1] = SparseArray[{{1, 2} -> 1, {2, 1} -> 1}, {2, 2}]

ThePauli[2] = ThePauli[-2] = SparseArray[{{1, 2} ->-I, {2, 1} -> I}, {2, 2}]

ThePauli[3] = ThePauli[-3] = SparseArray[{{1, 1} -> 1, {2, 2} ->-1}, {2, 2}]


ThePauli[4] = ThePauli[-5] =
  SparseArray[{{1, 2} -> 1}, {2, 2}]

ThePauli[5] = ThePauli[-4] =
  SparseArray[{{2, 1} -> 1}, {2, 2}]

ThePauli[6] = ThePauli[-6] =
  {{1,1},{1,-1}}/Sqrt[2]

ThePauli[7] =
  SparseArray[{{1, 1} -> 1, {2, 2} -> +I}, {2, 2}]

ThePauli[8] =
  SparseArray[{{1, 1} -> 1, {2, 2} -> Exp[+I*Pi/4]}, {2, 2}]

ThePauli[9] =
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


ThePauli[Raising] = ThePauli[4]

ThePauli[Lowering] = ThePauli[5]

ThePauli[Hadamard] = ThePauli[6]

ThePauli[Quadrant] = ThePauli[7]

ThePauli[Octant] = ThePauli[8]

ThePauli[Hexadecant] = ThePauli[9]


(* These are for Matrix[Dyad[...]]. *)
ThePauli[1 -> 0] = ThePauli[4]

ThePauli[0 -> 1] = ThePauli[5]

ThePauli[0 -> 0] = ThePauli[10]

ThePauli[1 -> 1] = ThePauli[11]

(**** </ThePauli> ****)


(**** <KetRegulate> ****)

theKetRegulate::usage = "theKetRegulate[assoc, {s1, s2, ...}] returns a new association with all default values assigned.\nSee also theKetTrim."

theKetRegulate[a_Association, ss:{___?SpeciesQ}] := With[
  { tt = Union[Keys @ a, FlavorCap @ ss] },
  KeySort @ AssociationThread[tt -> Lookup[a, tt]]
]
(* NOTE:
   1. Does not drop any key from a.
   2. It does not affect the fermion-permutation signature. *)


KetRegulate::usage = "KetRegulate[expr] converts every Ket[...] and Bra[...] in expr into the fully logical form without dropping any element.\nKetRegulate[expr, {S1, S2, \[Ellipsis]}] assumes that expr involves systems labeled by S1, S2, ....\nKetRegulate[expr, S] is quivalent to KetRegulate[expr, {S}].\nSee also KetTrim."

KetRegulate[expr_] := expr /;
  FreeQ[expr, Ket[_Association] | Bra[_Association]]

KetRegulate[expr_] := KetRegulate[expr, KetSpecies @ expr]

KetRegulate[expr_, S_?SpeciesQ] := KetRegulate[expr, S @ {$}]

KetRegulate[expr_, ss:{__?SpeciesQ}] :=
  KetRegulate[expr, FlavorCap @ ss] /; Not[FlavorCapQ @ ss]

KetRegulate[expr_, ss:{__?SpeciesQ}] := With[
  { tt = KetSpecies[expr] },
  KetRegulate[expr, Union[ss, tt]] /;
    Not @ ContainsAll[ss, tt]
 ]


KetRegulate[v:(_Ket|_Bra), ss:{___?SpeciesQ}] = v

KetRegulate[Ket[a_Association], ss:{___?SpeciesQ}] := Ket @ theKetRegulate[a, ss]

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

(**** </KetRegulate> ****)


(**** <KetMutate> ****)

KetMutate::usage = "KetMutate[expr, {s1, s2, \[Ellipsis]}] changes every Ket[v1,v2,\[Ellipsis]] to Ket[<|s1->v1, s2->v2, \[Ellipsis]|>] and vice versa in expr."

KetMutate[any_, ss:{__?SpeciesQ}] :=
  KetMutate[any, FlavorCap @ ss] /; Not[FlavorCapQ @ ss]

KetMutate[any_Association, ss:{__?SpeciesQ}] := Map[KetMutate[#, ss]&, any]
(* NOTE: Recall that Association has attribute HoldAllComplete. *)

KetMutate[Ket[{v__}], ss:{__?SpeciesQ}] := Ket[ss -> PadRight[{v}, Length @ ss]]

KetMutate[Bra[{v__}], ss:{__?SpeciesQ}] := Bra[ss -> PadRight[{v}, Length @ ss]]

KetMutate[Ket[a_Association], ss:{__?SpeciesQ}] := Ket @ Lookup[a, ss]

KetMutate[Bra[a_Association], ss:{__?SpeciesQ}] := Bra @ Lookup[a, ss]

KetMutate[Pauli[v__], ss:{__?SpeciesQ}] := With[
  { qq = Select[ss, QubitQ] },
  Multiply @@ MapThread[
    Construct,
    {qq, PadRight[{v}, Length @ qq]}
  ]
]

KetMutate[expr_, ss:{__?SpeciesQ}] := ReplaceAll[ expr,
  { v_Association :> KetMutate[v, ss],
    v:(_Ket|_Bra) :> KetMutate[v, ss],
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
  SimpleForm[expr, FlavorCap @ ss] /; Not[FlavorCapQ @ ss]

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
  ProductForm[expr, FlavorCap @ ss] /; Not[FlavorCapQ @ ss]

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
  SpinForm[expr, FlavorCap @ a, FlavorCap @ b] /;
  Not[FlavorCapQ @ {a, b}]

SpinForm[expr_] := SpinForm[expr, Agents @ expr, {}]

SpinForm[expr_, s_?SpeciesQ, rest_] := SpinForm[expr, s @ {$}, rest]

SpinForm[expr_, qq_List, s_?SpeciesQ] := SpinForm[expr, qq, s @ {$}]

SpinForm[v_Ket, rest__] :=
  Interpretation[theSpinForm[v, rest], v]
  
SpinForm[Bra[spec___], rest___] :=
  Interpretation[Dagger @ theSpinForm[Ket[spec], rest], Bra[spec]]
  
SpinForm[expr_, qq_List] := SpinForm[ expr, FlavorCap @ qq,
  Complement[Agents @ expr, FlavorCap @ qq]
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

KetCanonical[State[v_?VectorQ, rest__], nrm_:True] :=
  State[CanonicalizeVector[v, nrm], rest]

KetCanonical[expr_?fKetQ, nrm_:True] := Elaborate[
  KetCanonical[StateForm @ expr, nrm]
]

KetCanonical[expr_?fPauliKetQ, nrm_:True] := ExpressionFor[
  CanonicalizeVector[Matrix @ expr, nrm]
]

KetCanonical[expr_, nrm_:True] := Module[
  { vv = Cases[Garner @ {expr}, _Ket, Infinity],
    cc },
  cc = Coefficient[expr, vv];
  CanonicalizeVector[cc, nrm] . vv
] /; Not @ FreeQ[expr, _Ket]

KetCanonical[any_, nrm_:True] = any

(**** </KetCanonical> ****)


(**** <XBasisForm> ****)

XBasisForm::usage = "XBasisForm[expr, {q1,q2,\[Ellipsis]}] displays the quantum state in expression expr in the eigenbasis of the Pauli X operator for qubits q1, q2, \[Ellipsis]."

XBasisForm[expr_, q_?QubitQ] := XBasisForm[expr, q @ {$}] 

XBasisForm[expr_, qq:{__?QubitQ}] := 
  XBasisForm[expr, FlavorCap @ qq] /; Not[FlavorCapQ @ qq]

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
  YBasisForm[expr, FlavorCap @ qq] /; Not[FlavorCapQ @ qq]

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


Affect::usage = "Affect[ket, op1, op2, ...] operates the operators op1, op2, ... (earlier operators first) on ket. Notice the order of the arguments. The result should be equivalent to Multiply[..., op2, op1, ket], but it is much faster than the counterpart for deep (the numer of operators is much bigger than the number of particles) expression. The first argument does not need to be a Ket, but otherwise Affect is not an advantage over Multiply."

SetAttributes[Affect, Listable]

Affect[ket_, op__] := Distribute[ theAffect @@ Garner[{ket, op}] ]

theAffect[ket_, a_, b__] := Fold[ theAffect, ket, {a, b} ]

theAffect[ket_, op_Multiply] := theAffect[ket, Sequence @@ Reverse[op]]

theAffect[ket_, op_] := Garner @ Multiply[op, ket]


(**** <fPauliKetQ> ****)

fPauliKetQ::usage = "fPauliKetQ[expr] returns True if expr is a valid expression for a state vector of a system of unlabelled qubits.\nPauli[\[Ellipsis]] operates consistently on such an expression.";

HoldPattern @ fPauliKetQ[Ket[{(0|1)..}]] = True

HoldPattern @ fPauliKetQ[Multiply[__, Ket[{(0|1)..}]]] = True

HoldPattern @ fPauliKetQ[z_?CommutativeQ expr_] := fPauliKetQ[expr]

HoldPattern @ fPauliKetQ[Plus[terms__]] := AllTrue[KetChop @ {terms}, fPauliKetQ]
(* NOTE: KetChop is required since 0. or Complex[0., 0.] can ocur in numerical evaluattions. *)

HoldPattern @ fPauliKetQ[expr_Times] := fPauliKetQ[Expand @ expr]

HoldPattern @ fPauliKetQ[expr_] := False /; FreeQ[expr, Ket[(0 | 1) ..]]

HoldPattern @ fPauliKetQ[expr_] := False /;
  Not[Equal @@ Length /@ Cases[{expr}, Ket[kk_List] :> kk, Infinity]]

(**** </fPauliKetQ> ****)


(**** <fKetQ> ****)

fKetQ::usage = "fKetQ[expr] returns True if expr is a valid expression for a state vector of labelled qubits.";

HoldPattern @ fKetQ[Ket[_Association]] = True

HoldPattern @ fKetQ[Multiply[__, Ket[_Association]]] = True

HoldPattern @ fKetQ[z_?CommutativeQ expr_] := fKetQ[expr]

HoldPattern @ fKetQ[Plus[terms__]] := TrueQ[
  And @@ fKetQ /@ DeleteCases[ {terms}, (Complex[0., 0.] | 0.) ]
]
(* NOTE: 0. or Complex[0., 0.] can ocur in numerical evaluattions. *)

HoldPattern @ fKetQ[expr_] := False /; FreeQ[expr, Ket[_Association]]

(**** </fKetQ> ****)


(**** <KetFormat> <BraFormat>****)

KetFormat::usage = "KetFormat[\[Ellipsis]] is a low-level function to display Ket[\[Ellipsis]]."

KetFormat[a_] :=
  DisplayForm @ TemplateBox[List @ Row[theKetFormat @ a, $KetDelimiter], "Ket"]

KetFormat[a_?theKetFormatQ] :=
  DisplayForm @ TemplateBox[List @ Row[theKetFormat @ a, $KetDelimiter], "Ket"]
(* NOTE: This is necessary to handle special formats such as YoungTableau. *)

KetFormat[a_List] :=
  DisplayForm @ TemplateBox[List @ Row[theKetFormat /@ a, ","], "Ket"]

BraFormat[a_] :=
  DisplayForm @ TemplateBox[List @ Row[theKetFormat @ a, $KetDelimiter], "Bra"]

BraFormat[a_?theKetFormatQ] :=
  DisplayForm @ TemplateBox[List @ Row[theKetFormat @ a, $KetDelimiter], "Bra"]
(* NOTE: This is necessary to handle special formats such as YoungTableau. *)

BraFormat[a_List] :=
  DisplayForm @ TemplateBox[List @ Row[theKetFormat /@ a, ","], "Bra"]


theKetFormat[Vacuum] = Any

theKetFormat[Association[]] = {Any}

theKetFormat[a_Association] := KeyValueMap[SpeciesBox[#2, {#1}, {}]&, a]

theKetFormat[v_] = v


theKetFormatQ[_] = False

(**** </KetFormat> </BraFormat> ****)


(**** <Ket & Bra> ****)

Ket::usage = "Ket represents a basis state of a system of Spins or similar systems.\nKet[0] and Ket[1] represent the two eigenvectors of the Pauli-Z matrix Pauli[3].\nKet[s1, s2, \[Ellipsis]] represents the tensor product Ket[s1] \[CircleTimes] Ket[s2] \[CircleTimes] ....\nSee also Ket, TheKet, Bra, TheBra, State, Pauli, ThePauli, Operator."

Bra::usage = "Bra[expr] := Dagger[Ket[expr]].\nSee also Bra, TheBra, Ket, TheKet, Pauli, ThePauli."


SetAttributes[{Ket, Bra}, NHoldAll]
(* The integers in Ket[...] and Bra[...] should not be converted to real
   numbers by N[]. *)

SetAttributes[{Ket, Bra}, ReadProtected]
(* Prevent values associated with Ket and Bra from being seen. *)
(* Recall that Ket adn Bra has the System` context. *)

If[ $VersionNumber > 13.2,
  SyntaxInformation[Ket] = {"ArgumentsPattern" -> {___}};
  SyntaxInformation[Bra] = {"ArgumentsPattern" -> {___}};
]

Ket /:
MakeBoxes[expr:Ket[v_Association], StandardForm|TraditionalForm] := With[
  { box = ToBoxes @ Ket @ List @ Row[theKetFormat @ v, $KetDelimiter] },
  InterpretationBox[box, expr]
]

Format[Ket[Vacuum]] := Interpretation[Ket @ {"\[CupCap]"}, Ket[Vacuum]]

Format[Ket[{}]] := Interpretation[Ket @ {Any}, Ket[{}]]

Format[Ket[v_List]] := Interpretation[Ket[theKetFormat /@ v], Ket[v]] /;
  AnyTrue[v, theKetFormatQ]


Bra /:
MakeBoxes[expr:Bra[v_Association], StandardForm|TraditionalForm] := With[
  { box = ToBoxes @ Bra @ List @ Row[theKetFormat @ v, $KetDelimiter] },
  InterpretationBox[box, expr]
]

Format[Bra[Vacuum]] := Interpretation[Bra @ {"\[CupCap]"}, Bra[Vacuum]]

Format[Bra[{}]] := Interpretation[Bra @ {Any}, Bra[{}]]

Format[Bra[v_List]] := Interpretation[Bra[theKetFormat /@ v], Bra[v]] /;
  AnyTrue[v, theKetFormatQ]


Ket /: Dagger[Ket[a___]] := Bra[a]

Bra /: Dagger[Bra[a___]] := Ket[a]


Ket /: NonCommutativeQ[ _Ket ] = True

Bra /: NonCommutativeQ[ _Bra ] = True

Ket /: MultiplyKind[ _Ket ] = Ket

Bra /: MultiplyKind[ _Bra ] = Bra

Ket /: MultiplyGenus[ _Ket ] = "Ket"

Bra /: MultiplyGenus[ _Bra ] = "Bra"


Ket /:
CircleTimes[a:Ket[_Association], b:Ket[_Association]..] :=
  fermionKeySort @ Join[a, b, 2]

Bra /:
CircleTimes[a:Bra[_Association], b:Bra[_Association]..] :=
  fermionKeySort @ Join[a, b, 2]

Ket /:
CircleTimes[a:Ket[_List], b:Ket[_List]..] := Join[a, b, 2]

Bra /:
CircleTimes[a:Bra[_List], b:Bra[_List]..] := Join[a, b, 2]


fermionKeySort::usage = "fermionKeySort[Ket[assoc]] sorts the Keys of assoc and multiply a factor of the signature of fermion Keys."

fermionKeySort[(head:(Ket|Bra))[a_Association]] := 
  Signature[Keys @ theKetTrim @ KeySelect[a, FermionQ]] * head[KeySort @ a]


Ket[s_?IntegerQ] := Ket @ {s}

Bra[s_?IntegerQ] := Bra @ {s}

(* Ket[<|...|>] *)

Ket[] := Ket[ Association[] ]

Ket[ spec__Rule ] := Ket[ Ket[], spec ]

Ket[ Ket[a_Association], spec__Rule ] := Module[
  { rules = Flatten @ KetRule @ {spec},
    vec },
  vec = theKetVerify @ Join[a, Association @ rules];
  If[FailureQ @ vec, $Failed, fermionKeySort @ Ket @ vec]
]


Ket[ spec___Rule, ss:{__?AgentQ}] := KetRegulate[Ket[spec], ss]

Ket[ v_Ket, spec___Rule, ss:{__?AgentQ} ] := KetRegulate[Ket[v, spec], ss]


(* operator form *)
Ket[a_Association][spec__Rule] := Ket[Ket[a], spec]

(* extracting the values *)
Ket[a_Association][ss_List] := Lookup[a, FlavorCap @ ss]

(* extracting a value *)
Ket[a_Association][s_] := a[FlavorCap @ s]

(* otherwise *)
(* Ket[a:Except[_List|_Association|_Rule]..] := Ket @ {a} *)


Bra[] = Bra[ Association[] ]

Bra[spec__Rule] := Dagger @ Ket[Ket[], spec]

Bra[v_Bra, spec__Rule] := Dagger @ Ket[Dagger @ v, spec]


Bra[ spec___Rule, ss:{__?SpeciesQ}] := KetRegulate[Bra[spec], ss]

Bra[ v_Bra, spec___Rule, s_?SpeciesQ] := KetRegulate[Bra[v, spec], {s}]

Bra[ v_Bra, spec___Rule, ss:{__?SpeciesQ}] := KetRegulate[Bra[v, spec], ss]


Bra[a_Association][spec__Rule] := Bra[ Bra[a], spec ]

Bra[a_Association][ss_List] := Lookup[a, FlavorCap @ ss]

Bra[a_Association][s_] := a[FlavorCap @ s]

(**** </Ket & Bra> ****)


KetRule::usage = "KetRule[rule] is a low-level function used when constructing Ket[<|\[Ellipsis]|>] to generate proper elementary rules from the compound rule specified in rule."

SetAttributes[KetRule, Listable]

KetRule[ r:Rule[_, _] ] := FlavorCap[r]

KetRule[ r:Rule[_List, _] ] := FlavorCap @ Thread[r]

KetRule[r_Rule] := r


(**** <KetVerify> ****)

theKetVerify::usage = "theKetVerify[assoc] returns assoc if assoc is an Association of valid Key-Value pairs; $Failed otherwise.\ntheKetVerify[a->b] returns a->b if Ket[<|a->b|>] is a valid Ket; $Failed otherwise."

theKetVerify[a_Association] := With[
  { aa = AssociationMap[theKetVerify, a] },
  If[ AnyTrue[aa, FailureQ],
    $Failed,
    Association @ aa,
    Association @ aa
  ]
]

theKetVerify[any_Rule] = any


KetVerify::usage = "KetVerify[ket] returns ket if ket is a valid Ket; $Failed otherwise.\nKetVerify[expr] checks every Ket[<|...|>] in expr."

KetVerify[Ket[a_Association]] := With[
  { aa = theKetVerify[a] },
  If[FailureQ[aa], $Failed, Ket @ aa, Ket @ aa]
]

KetVerify[expr_] := expr /. { v_Ket :> KetVerify[v] }

(**** </KetVerify> ****)


(**** <KetTrim> ****)

theKetTrim::usage = "theKetTrim[assoc] removes from assoc the elements that are either irrelevant or associated with the default value."

theKetTrim[a_Association] := AssociationMap[theKetTrim, a]

theKetTrim[any_Rule] = any

theKetTrim[{} -> _] = Nothing (* fallback *)


KetTrim::usage = "KetTrim[expr] converts every Ket[...] and Bra[...] in expr into the simplest form by dropping elements with default values.\nTo be compared with KetRegulate."

KetTrim[Ket[a_Association]] := Ket[theKetTrim @ a]

KetTrim[expr_] := expr /. {
  a_OTimes -> a, (* NOTE *)
  HoldPattern[OSlash[v_Ket, new_]] :> OSlash[v, KetTrim @ new],
  Ket[a_Association] :> Ket[theKetTrim @ a],
  Bra[a_Association] :> Bra[theKetTrim @ a]
}
(* NOTE: This line is necessary to prevent the Kets and Bras in OTimes from
   being affected. *)

(**** </KetTrim> ****)


KetSpecies::usage = "KetSpecies[expr] returns the list of all species of Ket-like objects in expression expr."

KetSpecies[expr_] := Select[
  Union @ Flatten @ Cases[{expr}, (Ket|Bra|ProductState|CoherentState)[a_Association] :> Keys[a], Infinity],
  NonCommutativeQ
 ]


(**** <KetChop> ****)

KetChop::usage = "KetChop[expr] removes approximate zeros, 0.` or 0.` + 0.`\[ImaginaryI], from expr, where the rest is a valid Ket expression."

SetAttributes[KetChop, Listable]

KetChop[any_, ___] := any /;FreeQ[any, _Ket]

KetChop[expr_] := KetChop[expr, 1*^-10]

KetChop[expr_, delta_] := Module[
  { var = Cases[{expr}, _Ket, Infinity],
    cff },
  cff = Coefficient[expr, var];
  IntegerChop[cff] . var
]

(**** </KetChop> ****)


KetDrop::usage = "KetDrop[v, {s1, s2, \[Ellipsis]}] returns Ket[<|\[Ellipsis]|>] with the species {s1, s2, \[Ellipsis]} removed from v.\nKetDrop[expr, {s1, s2, \[Ellipsis]}] removes {s1, s2, \[Ellipsis]} from every ket in expr.\nKetDrop[{s1,s2,\[Ellipsis]}] is an operator form of KetDrop."

KetDrop[Ket[a_Association], ss:{__?SpeciesQ}] :=
  Ket @ KeyDrop[a, FlavorCap @ ss]

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

KetSort[Ket[vv_List]] := Ket @ Sort[vv] (* Pauli Ket *)

KetSort[expr_] := KetSort[expr, Agents @ expr] /;
  Not @ FreeQ[expr, Ket[_Association]]

KetSort[expr_] := expr /. { v:Ket[__] :> KetSort[v] }

KetSort[expr_, ss:{__?SpeciesQ}] := expr /. {
  v:Ket[_Association] :> KetSort[v, ss]
 }


KetNormSquare::usage = "KetNormSquare[expr] returns the norm square of Ket expression expr."

SetAttributes[KetNorm, Listable]

KetNormSquare[0] = 0

KetNormSquare[z_?CommutativeQ * any_Ket] := AbsSquare[z]

KetNormSquare[expr_] := NormSquare[Matrix @ expr] /; Not @ FreeQ[expr, _Ket]


KetNorm::usage = "KetNorm[expr] returns the norm of Ket expression expr."

SetAttributes[KetNorm, Listable]

KetNorm[0] = 0

KetNorm[z_?CommutativeQ * any_Ket] := Abs[z]

KetNorm[expr_] := Norm[Matrix @ expr] /; Not @ FreeQ[expr, _Ket]


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
  { ss = FlavorCap[qq] },
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
 ] /; ContainsAll[FlavorCap @ qq, Agents @ expr]


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
  Aggregate @ Map[ Ket @* Association, Normal @ a ] /;
  Length[a] > 0

ketSplit[ Bra[] ] := Bra[]

ketSplit[ Bra[a_Association] ] := 
  Aggregate @ Map[ Bra @* Association, Normal @ a ] /;
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
  Multiply[ pre___, Bra[a_List], Ket[b_List], post___ ] :=
  BraKet[a, b] * Multiply[pre, post]

HoldPattern @
  Multiply[ pre___, Bra[a___], Ket[b___], post___ ] :=
  BraKet[{a}, {b}] * Multiply[pre, post]
(* Recall that Multiply has no Flat attribute. *)

HoldPattern @
  Multiply[Bra[u___], op__, Ket[v___], post__] :=
  Multiply[Bra[u], op, Ket[v]] * Multiply[post]

HoldPattern @
  Multiply[pre__, Bra[u___], op__, Ket[v___], post___] :=
  Multiply[Bra[u], op, Ket[v]] * Multiply[pre, post]
(* NOTE: Do not try to combine the above two definitions into one by using
   pre___ and post___. It will result in infinite loop. *)


Multiply /:
HoldPattern @ ComplexQ[ Multiply[Bra[___], ___, Ket[___]] ] = True
(* NOTE: Hence partial trace, for example, is not allowed. *)

Multiply /:
HoldPattern @ Conjugate[ Multiply[Bra[a___], op___, Ket[b___]] ] :=
  Multiply[Bra[b], Dagger @ Multiply[op], Ket[a]]

(**** </Multiply> ****)


(**** <BraKet> ****)

BraKet::usage = "BraKet[{a}, {b}] represents the Hermitian product \[LeftAngleBracket]a|b\[RightAngleBracket] of the two states Ket[a] and Ket[b]."

SetAttributes[BraKet, NHoldAll]
(* The integers in BraKet[] should not be converted to real numbers by N[]. *)

Format @ BraKet[{}, b_List] :=
  Interpretation[BraKet[{Any}, b], BraKet[{}, b]]

Format @ BraKet[a_List, {}] :=
  Interpretation[BraKet[a, {Any}], BraKet[a, {}]]

BraKet /: ComplexQ[ BraKet[a_, b_] ] = True

BraKet /: Conjugate[ BraKet[a_, b_] ] := BraKet[b, a]

(* General evaluation rules *)

BraKet[a_List, b_List] := TheDelta[a, b] /;
  AllTrue[Flatten @ {a, b}, NumericQ]

BraKet[a_List, b_List] := 0 /; Length[a] != Length[b]

BraKet[a_List, b_List] := TheDelta[a, b]


BraKet[a_Association, b_Association] := With[
  { qq = Union[Keys @ a, Keys @ b] },
  TheDelta[Lookup[a, qq], Lookup[b, qq]]
]

(**** </BraKet> ****)


(**** <State> ****)

State::usage = "State[vec, {s1,s2,\[Ellipsis]}] represents the state of the systems {s1, s2, \[Ellipsis]} with the vector representation vec."

SyntaxInformation[State] = {"ArgumentsPattern" -> {_, _, OptionsPattern[]}};

AddElaborationPatterns[_State]

State /:
MakeBoxes[vv:State[vec_?VectorQ, ss:{__?SpeciesQ}, opts___?OptionQ], fmt_] :=
  BoxForm`ArrangeSummaryBox[
    State, vv, None,
    { BoxForm`SummaryItem @ {"Species: ", ss},
      BoxForm`SummaryItem @ {"Dimension: ", Length @ vec} },
    { BoxForm`SummaryItem @ {"Vector (up to 5): ", Normal@vec[[;;UpTo[5]]]},
      BoxForm`SummaryItem @ {"Options: ", Flatten @ {opts}} },
    fmt, "Interpretable" -> Automatic ]


State[vec_?VectorQ, S_?SpeciesQ, opts___?OptionQ] := 
  State[vec, S @ {$}, opts]

State[vec_?VectorQ, ss:{__?SpeciesQ}, opts___?OptionQ] :=
  State[vec, FlavorCap @ ss, opts] /; Not[FlavorCapQ @ ss]

State[vec_?VectorQ, ss:{__?SpeciesQ}, {}] :=
  State[vec, ss]

State[vec_?VectorQ, ss:{__?SpeciesQ}, opts___?OptionQ] := With[
  { tt = Sort @ ss},
  State[MatrixEmbed[vec, ss, tt], tt, opts]
] /; Not[OrderedQ @ ss]
(* TODO: To support fermions *)


State /:
Matrix[ State[vec_?VectorQ, ss:{__?SpeciesQ}, ___?OptionQ], tt:{___?QubitQ} ] :=
  MatrixEmbed[vec, ss, tt]

State /:
Elaborate[ State[vec_?VectorQ, ss:{__?SpeciesQ}, ___?OptionQ] ] :=
  ExpressionFor[vec, ss]


State /:
Times[z_, State[v_, ss_, opts___?OptionQ]] :=
  State[z * v, ss, opts]

State /:
Plus[State[a_, ss_, opts___?OptoinQ], State[b_, ss_, more___?OptionQ]] :=
  State[a + b, ss, opts, more]

State /:
Plus[State[a_, ss:{__?SpeciesQ}, opts___?OptoinQ], State[b_, tt:{__?SpeciesQ}, more___?OptionQ]] :=
  With[
    { all = Union[ss, tt] },
    State[MatrixEmbed[a, ss, all] + MatrixEmbed[b, tt, all], opts, more]
  ]


State::dupe = "Species `` appear in multiple states to be multiplied or tensor-producted."

State /:
CircleTimes[vv__State] := Module[
  { rr = Flatten[Options /@ {vv}],
    ss = Map[Part[#, 2]&, {vv}],
    dd },
  dd = Intersection @@ ss;
  If[ Length[dd] > 0,
    Message[State::dupe, dd];
    ss = Union @@ ss;
    Return @ State[Zero[Aggregate @ Dimension @ ss], ss, rr]
  ];
  State[CircleTimes @@ Map[First, {vv}], Flatten @ ss, rr]
]
(* TODO: To support fermions *)

State /:
Multiply[ pre___, v_State, ww__State, Shortest[post___] ] :=
  Multiply[pre, CircleTimes[v, ww], post]

State /:
Multiply[ pre___, w_Ket, v_State, Shortest[post___] ] :=
  Multiply[pre, CircleTimes[StateForm @ w, v], post]

State /:
Multiply[ pre___, v_State, w_Ket, Shortest[post___] ] :=
  Multiply[pre, CircleTimes[v, StateForm @ w], post]


State /:
Multiply[pre___, op:Except[_Plus|_Times], State[vec_?VectorQ, ss:{__?SpeciesQ}, ___?OptionQ], post___] :=
  With[
    { tt = Agents @ {op, ss} },
    Multiply[
      pre,
      State[Matrix[op, tt] . MatrixEmbed[vec, ss, tt], tt],
      post
    ]
  ]


(**** </State> ****)


(**** <StateForm> ****)

StateForm::usage = "StateForm[expr] converts the Ket expression expr to State[vec, {s1, s2, \[Ellipsis]}."

StateForm[expr_?fKetQ] := With[
  { ss = Agents @ expr },
  State[Matrix[expr, ss], ss]
]

StateForm[vec_ProductState] := Expand[vec]

(**** </StateForm> ****)


(**** <Operator> ****)

Operator::usage = "Operator[mat, {s1,s2,\[Ellipsis]}] represents the operator acting on systems {s1, s2, \[Ellipsis]} with the matrix representation mat."

SyntaxInformation[Operator] = {"ArgumentsPattern" -> {_, _, OptionsPattern[]}};

AddElaborationPatterns[_Operator]

Operator /:
MakeBoxes[op:Operator[mat_?MatrixQ, ss:{__?QubitQ}, opts___?OptionQ], fmt_] :=
  BoxForm`ArrangeSummaryBox[
    Operator, op, None,
    { BoxForm`SummaryItem @ {"Species: ", ss},
      BoxForm`SummaryItem @ {"Dimension: ", Dimensions @ mat} },
    { BoxForm`SummaryItem @ {"Matrix (5\[Times]5): ", MatrixForm@mat[[;;UpTo[5], ;;UpTo[5]]]},
      BoxForm`SummaryItem @ {"Options: ", Flatten @ {opts}} },
    fmt, "Interpretable" -> Automatic ]


Operator[mat_?MatrixQ, S_?SpeciesQ, opts___?OptionQ] := 
  Operator[mat, S @ {$}, opts]

Operator[mat_?MatrixQ, ss:{__?SpeciesQ}, opts___?OptionQ] :=
  Operator[mat, FlavorCap @ ss, opts] /; Not[FlavorCapQ @ ss]


Operator /:
Matrix[ Operator[mat_?MatrixQ, ss:{__?SpeciesQ}, ___?OptionQ], tt:{__?QubitQ} ] :=
  MatrixEmbed[mat, ss, tt]

Operator /:
Elaborate[ Operator[mat_?MatrixQ, ss:{__?SpeciesQ}, ___?OptionQ] ] :=
  Elaborate @ ExpressionFor[mat, ss]


Operator /:
Multiply[
  pre___,
  Operator[mat_?MatrixQ, ss:{__?SpeciesQ}, ___?OptionQ],
  Ket[aa_Association], 
  post___
] :=
  Multiply[
    pre,
    ExpressionFor[mat . Matrix[Ket @ KeyTake[aa, ss], ss], ss],
    Ket @ KeyDrop[aa, ss],
    post
  ]

Operator /:
Multiply[
  pre___, 
  Operator[mat_?MatrixQ, ss:{__?SpeciesQ}, ___?OptionQ], 
  State[vec_?VectorQ, tt:{__?SpeciesQ}, ___?OptionQ],
  post___
] :=
  With[
    { qq = Union[ss, tt] },
    Multiply[
    pre,
    State[ MatrixEmbed[mat, ss, qq] . MatrixEmbed[vec, tt, qq], qq ],
    post
    ]
  ]

(**** </Operator> ****)


(**** <RaisingLoweringForm> ****)

RaisingLoweringForm::usage = "RaisingLoweringForm[expr] converts expr by rewriting Pauli or Spin X and Y operators in terms of the raising and lowering operators."

RaisingLoweringForm[expr_] := Garner[expr //. $RaisingLoweringRules]

$RaisingLoweringRules = {
  Pauli[a___, 1, b___] :> (Pauli[a, 4, b] + Pauli[a, 5, b]),
  Pauli[a___, 2, b___] :> (Pauli[a, 4, b] - Pauli[a, 5, b]) / I
 }

(**** </RaisingLoweringForm> ****)


Raising::usage = "Raising represents the raising operator."

Lowering::usage = "Lowering represents the lowering operator."

Hadamard::usage = "Hadamard represents the Hadamard gate."

Quadrant::usage = "Quadrant represents the phase gate with phase angle 2*\[Pi]/4."

Octant::usage = "Octant represents the phase gate with phase angle 2*\[Pi]/8."

Hexadecant::usage = "Hexadecant represents the phase gate with phase angle 2*\[Pi]/16."


(**** <Pauli> ****)

Pauli::usage = "Pauli[n] represents the Pauli operator (n=1,2,3). Pauli[0] represents the 2x2 identity operator. Pauli[4] and Pauli[5] represent the Pauli raising and lowering operator, respectively. Pauli[6] represents the Hadamard operator. Pauli[7], Pauli[8], Pauli[9] represent the quadrant, octant, hexadecant phase operator, respectively.\nPauli[10] returns (Pauli[0]+Pauli[1])/2, the Projection to Ket[0].\nPauli[11] returns (Pauli[0]-Paui[1])/2, the projection to Ket[1].\nPauli[n1, n2, ...] represents the tensor product of the Pauli operators Pauil[n1], Pauli[n2], ... ."

Pauli::dot = "Different lengths of Pauli indices `` and ``."

SetAttributes[Pauli, NHoldAll]

SyntaxInformation[Pauli] = {"ArgumentsPattern" -> {_}};

Pauli[kk_SparseArray] := Pauli[Normal @ kk]

Pauli[kk:{___, _List, ___}] := Pauli /@ Thread[kk]
(* Note: similar to the Listable attribute. *)

Pauli[kk_List] := Pauli @ ReplaceAll[ kk,
  { All -> {1, 2, 3},
    Full -> {0, 1, 2, 3} }
 ] /; ContainsAny[kk, {All, Full}]

Pauli[All] := Pauli /@ {1, 2, 3}

Pauli[Full] := Pauli /@ {0, 1, 2, 3}

Pauli[k_Integer] := Pauli @ {k}


Format @ Pauli[kk_List] :=
  Interpretation[thePauliForm @ Pauli @ kk, Pauli @ kk]


Pauli /: MultiplyKind[ Pauli[_] ] = Pauli

Pauli /: MultiplyGenus[ Pauli[_] ] = "Singleton"

Pauli /: NonCommutativeQ[ Pauli[_] ] = True


Pauli[k:Rule[_Integer,_Integer]] := Pauli @ {k}

Pauli[{1 -> 0}] = Pauli[{4}]

Pauli[{0 -> 1}] = Pauli[{5}]

Pauli[{0 -> 0}] = Pauli[{10}]

Pauli[{1 -> 1}] = Pauli[{11}]


Pauli[Raising] = (Pauli[{1}] + I Pauli[{2}]) / 2

Pauli[Lowering] = (Pauli[{1}] - I Pauli[{2}]) / 2

Pauli[Hadamard] = (Pauli[{1}] + Pauli[{3}])/Sqrt[2]

Pauli[Quadrant] = Pauli[{0}] (1+I)/2 + Pauli[{3}]*(1-I)/2

Pauli[Octant] = Pauli[{0}] (1+Exp[I Pi/4])/2 + Pauli[{3}]*(1-Exp[I Pi/4])/2

Pauli[Hexadecant] = Pauli[{0}] (1+Exp[I Pi/8])/2 + Pauli[{3}]*(1-Exp[I Pi/8])/2


Pauli[{-1}] = Pauli[{1}]

Pauli[{-2}] = Pauli[{2}]

Pauli[{-3}] = Pauli[{3}]

Pauli[{-4}] = Pauli[{5}]

Pauli[{-5}] = Pauli[{4}]

Pauli[{-6}] = Pauli[{6}]


Pauli @ C[n_Integer?NonNegative] = Pauli[{0}]

Pauli[-C[n_Integer?NonNegative]] = Pauli[{0}]


Pauli[a:{(0|1)..} -> b:{(0|1)..}] := Pauli @@ Thread[a -> b]

Pauli[kk_List] := Garner @ Apply[CircleTimes, Pauli /@ kk] /;
  ContainsAny[kk, {Raising, Lowering, Hadamard, Quadrant, Octant, Hexadecant}]

(* Elaboration rules *)

Pauli /: Elaborate[ Pauli[kk_List] ] :=
  Garner @ Apply[CircleTimes, Elaborate[Pauli /@ kk]]

Pauli /: Elaborate[ op:Pauli[{0|1|2|3}] ] := op

Pauli /: Elaborate @ Pauli[{10}] := (Pauli[{0}] + Pauli[{3}]) / 2

Pauli /: Elaborate @ Pauli[{11}] := (Pauli[{0}] - Pauli[{3}]) / 2

Pauli /: Elaborate @ Pauli[{4}] := Pauli[Raising]

Pauli /: Elaborate @ Pauli[{5}] := Pauli[Lowering]

Pauli /: Elaborate @ Pauli[{6}] := Pauli[Hadamard]

Pauli /: Elaborate @ Pauli[{7}] := Pauli[Quadrant]

Pauli /: Elaborate @ Pauli[{8}] := Pauli[Octant]

Pauli /: Elaborate @ Pauli[{9}] := Pauli[Hexadecant]

Pauli /: Elaborate @ Pauli[{-7}] := Dagger @ Pauli[Quadrant]

Pauli /: Elaborate @ Pauli[{-8}] := Dagger @ Pauli[Octant]

Pauli /: Elaborate @ Pauli[{-9}] := Dagger @ Pauli[Hexadecant]

Pauli /: Elaborate @ Pauli @ {C[n_Integer]} := With[
  { f = Exp[I*2*Pi*Power[2, n]] },
  Pauli[{0}]*(1+f)/2 + Pauli[{3}]*(1-f)/2
]

(* Dagger *)

Pauli /: Dagger[ Pauli[{m:(0|1|2|3|6)}] ] := Pauli[{m}]

Pauli /: Dagger[ Pauli[{4}] ] := Pauli[{5}]

Pauli /: Dagger[ Pauli[{5}] ] := Pauli[{4}]

Pauli /: Dagger[ Pauli[{7}] ] := Pauli[{-7}]

Pauli /: Dagger[ Pauli[{8}] ] := Pauli[{-8}]

Pauli /: Dagger[ Pauli[{9}] ] := Pauli[{-9}]

Pauli /: Dagger[ Pauli[{-7}] ] := Pauli[{7}]

Pauli /: Dagger[ Pauli[{-8}] ] := Pauli[{8}]

Pauli /: Dagger[ Pauli[{-9}] ] := Pauli[{9}]

Pauli /: Dagger @ Pauli @ {C[n_Integer]} := Pauli[{-C[n]}]

Pauli /: Dagger @ Pauli @ {-C[n_Integer]} := Pauli[{C @ n}]

Pauli /: Dagger @ Pauli[kk_List] :=
  Garner @ Apply[CircleTimes, Dagger /@ Pauli /@ kk]

(* Conjugate *)

Pauli /: Conjugate[ Pauli[{2}] ] = -Pauli[{2}]

Pauli /: Conjugate[ Pauli[{7}] ] := Pauli[{-7}]

Pauli /: Conjugate[ Pauli[{8}] ] := Pauli[{-8}]

Pauli /: Conjugate[ Pauli[{9}] ] := Pauli[{-9}]

Pauli /: Conjugate[ Pauli[{-7}] ] := Pauli[{7}]

Pauli /: Conjugate[ Pauli[{-8}] ] := Pauli[{8}]

Pauli /: Conjugate[ Pauli[{-9}] ] := Pauli[{9}]

Pauli /: Conjugate[ Pauli[{m:(0|1|3|4|5|6)}] ] := Pauli[{m}]

Pauli /: Conjugate[ Pauli[kk_List] ] :=
  CircleTimes @@ Conjugate[Pauli /@ kk]

  
Pauli /:
CircleTimes[a:Pauli[_List], bc:Pauli[_List]..] := Join[a, bc, 2]

(*
Pauli /:
CircleTimes[a:Pauli[_Integer], bc:Pauli[_Integer]..] :=
  Pauli @ Catenate[List @@@ {a, bc}]
 *)


HoldPattern @ Multiply[pre___, vec_Bra, op__Pauli, post___] :=
  Multiply[pre, PauliDot[vec, op], post]

HoldPattern @ Multiply[pre___, op__Pauli, vec_Ket, post___] :=
  Multiply[pre, PauliDot[op, vec], post]

HoldPattern @ Multiply[pre___, op_Pauli, more__Pauli, Shortest[post___]] :=
  Multiply[pre, PauliDot[op, more], post]

(**** </Pauli> ****)


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
  bits = Ket /@ IntegerDigits[bits-1, 2, n];
  KetChop @ Garner @ Dot[vals, bits]
]


(* Matrix to operator for unlabeled qubits *)

ExpressionFor[mat_?MatrixQ] := Module[
  { n = Log[2, Length @ mat],
    tt, pp },
  If[ Not @ IntegerQ[n],
    Message[ExpressionFor::notls, mat];
    Return[0]
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
  { nL = Aggregate @ Dimension @ ss,
    bs = Basis @ ss },
  
  If[ nL == Length[vec], Null,
    Message[ExpressionFor::incmpt, vec, FlavorCap @ ss];
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
  If[ Aggregate[dd] == Length[mat], Null,
    Message[ExpressionFor::incmpt, mat, FlavorCap @ ss];
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


(**** <BlochVector> ****)

BlochVector::usage = "BlochVector[{c0, c1}] returns the three-dimensional coordinates {x, y, z} on the Bloch sphere corresponding to the pure state Ket[0]*c0 + Ket[1]*c1.\nBlochVector[\[Rho]] returns the point in the Bloch sphere corresponding to the mixed state \[Rho]."

BlochVector::traceless = "Matrix `` is traceless."

BlochVector::qubit = "`` does not represent a quantum state of qubits."

BlochVector[vec_?VectorQ] := Module[
  { new },
  new = If[VectorQ[vec, NumericQ], Normalize[vec], vec];
  Simplify @ {
    Conjugate[new] . ThePauli[1] . new,
    Conjugate[new] . ThePauli[2] . new,
    Conjugate[new] . ThePauli[3] . new
  }
] /; Length[vec] == 2

BlochVector[rho_?SquareMatrixQ] := Module[
  { nrm = Tr[rho],
    new },
  If[ ZeroQ[nrm],
    Message[BlochVector::traceless, rho];
    Return[{0, 0, 0}]
  ];  
  new = If[MatrixQ[rho, NumericQ], rho/nrm, rho];
  Simplify[2 * PauliVector[new]]
] /; Length[rho] == 2


BlochVector[rho:(_?VectorQ|_?SquareMatrixQ)] := BlochVector[rho, 1]

BlochVector[rho:(_?VectorQ|_?SquareMatrixQ), k_Integer] :=
  BlochVector[ReducedMatrix[rho, {k}]] /; 
    If[ IntegerPowerQ[2, Length @ rho], True,
      Message[BlochVector::qubit, rho];
      False
    ] 


BlochVector[Ket[]] := BlochVector @ {1, 0}

BlochVector[_?CommutativeQ Ket[]] := BlochVector @ {1, 0}

BlochVector[expr_, q_?SpeciesQ] := Module[
  { ss = Agents[expr] },
  If[ Length[ss] > 1,
    BlochVector @ ReducedMatrix[expr, FlavorCap @ {q}],
    BlochVector @ Matrix[expr, FlavorCap @ {q}]
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

(**** </BlochVector> ****)


(**** <BlochSphere> ****)

BlochSphere::usage = "BlochSphere[primitives, options] returns Graphics3D containing the Bloch sphere as well as primitives.\nIt accepts all Graphics3D primitives and, in addition, BlochPoint.\nBlochSphere[options] just displays the Bloch sphere."

Options[BlochSphere] = {
  "SphereStyle" -> {Opacity[0.8], Cyan},
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
  
BlochSphere[primitives_, opts:OptionsPattern[{BlochSphere, Graphics3D}]] :=
  Graphics3D[
    { theBlochSphere[opts], primitives },
    FilterRules[
      Join[{opts}, Options @ BlochSphere],
      Options @ Graphics3D
    ]
  ]

theBlochSphere[OptionsPattern[{BlochSphere, Graphics3D}]] := { 
  Flatten @ {Opacity[0.8], Cyan, OptionValue["SphereStyle"], Sphere[]},
  { Thick, GrayLevel[0.4],
    Line @ {
      1.1 {{-1,0,0}, {1,0,0}},
      1.1 {{0,-1,0}, {0,1,0}},
      1.1 {{0,0,-1}, {0,0,1}}
    },
    Line @ {
      Table[{0, Cos[t Pi], Sin[t Pi]}, {t, 0, 2, 0.01}],
      Table[{Cos[t Pi], 0, Sin[t Pi]}, {t, 0, 2, 0.01}],
      Table[{Cos[t Pi], Sin[t Pi], 0}, {t, 0, 2, 0.01}]
    }
  }
}

(**** </BlochSphere> ****)


(**** <Basis> ****)

Basis::usage = "Basis[n] constructs the standard tensor-product basis of a system of n unlabelled qubits.\nBasis[{dim1, dim2, ..., dimn}] constructs the standard tensor-product basis of a total of n unlabelled systems with the Hilbert space dimensions dim1, dim2, ..., respectively.\nBasis[q1, q2, ...] constructs the tensor product basis for the system consising of Species q1, q2, ...\nBasis[q1, {q2, q3}, ...] is equivalent to Basis[q1, q2, q3, ...].\nBasis[expr] finds the relevant systems from the expression expr and constructs the basis."

Basis::incon = "Inconsistent Ket, Bra, or Pauli in ``."

Basis[n_Integer] := Ket /@ Tuples[{0, 1}, n]

Basis[dim:{__Integer}] := Ket /@ Tuples[Range[0,#-1]& /@ dim]


Basis[] := { Ket @ Association[] } (* fallback *)

Basis[a_?SpeciesQ, b__?SpeciesQ] := Basis @ {a, b}

Basis[ss:{__?SpeciesQ}] := CircleTimes @@@ Tuples[Basis /@ ss]

Basis[
  a:Alternatives[_?SpeciesQ, {__?SpeciesQ}],
  b:Alternatives[_?SpeciesQ, {__?SpeciesQ}].. ] :=
  Basis @ Flatten @ {a, b}


Basis[ expr:Except[_?SpeciesQ] ] := Basis @@ Agents[expr] /;
  FreeQ[expr, _Pauli | Ket[_List] | Bra[_List] ]

Basis[ expr:Except[_?SpeciesQ] ] := Module[
  { pp },
  pp = Cases[ {expr}, 
    Pauli[a_List] | Ket[a:{(0|1)..}] | Bra[a:{(0|1)..}] :> Length[a],
    Infinity ];
  If[ Equal @@ pp,
    Basis[First @ pp],
    Message[Basis::incon, Cases[{expr}, _Pauli|_Ket|_Bra, Infinity]];
    Return[{Ket[{}]}]
  ]
]

(**** </Basis> ****)


(**** <TheMatrix> ****)

TheMatrix::usage = "TheMatrix[op] returns the matrix representation of op. Here, op is an elementary operators.\nThis function is a low-level function intended for internal use.\nSee also TheExpression, which serves for similar purposes."

HoldPattern @ TheMatrix[ Dagger[op_] ] := Topple @ TheMatrix[op]

(* For Ket/Bra of unlabelled qubits *)

TheMatrix @ Ket[ss_List] := TheKet @ ss

TheMatrix @ Bra[ss_List] := TheKet @ ss


TheMatrix[rr:Rule[_?SpeciesQ, _]] := TheMatrix @ Ket @ Association @ rr

TheMatrix @ Association[aa:Rule[_?SpeciesQ, _]..] := TheMatrix /@ {aa}


(* For Pauli operators of unlabelled qubits *)

TheMatrix @ Pauli[nn_List] := ThePauli @ nn

(**** </TheMatrix> ****)


(**** <Matrix> ****)

Matrix::usage = "Matrix[expr, {a1, a2, ...}] constructs the matrix representation of the expression expr on the total system consisting of a1, a2, ....\nMatrix[expr] feagures out the subsystems involved in expr.\nMatrix[dyadic, {a1, a2, \[Ellipsis]}, {b1, b2, \[Ellipsis]}] is for the dyadic expression acting on {a1, a2, ...} from the right and on {b1, b2, ...} from the left."

Matrix::rmndr = "There remain some elements, ``, that are not specified for matrix representation."

Matrix::fermion = "Operator `` does not appear in the species list ``."

Matrix::pauli = "The index list `` of the Pauli string is longer than ``."


(* General Code *)

Matrix[ expr_ ] := Matrix[expr, Agents @ expr]

Matrix[ expr_, S_?SpeciesQ ] := Matrix[expr, S @ {$}]

Matrix[ expr_, S_?SpeciesQ, tt_ ] := Matrix[expr, S @ {$}, tt]

Matrix[ expr_, ss_, T_?SpeciesQ ] := Matrix[expr, ss, T @ {$}]

Matrix[ expr_, ss:{__?SpeciesQ} ] := 
  Matrix[expr, FlavorCap @ ss] /; Not[FlavorCapQ @ ss]

Matrix[ expr_, ss:{__?SpeciesQ}, tt:{__?SpeciesQ} ] :=
  Matrix[expr, FlavorCap @ ss, FlavorCap @ tt] /;
  Not[FlavorCapQ @ {ss, tt}]


(* linearity *)

Matrix[expr_Plus, rest__] := TrigToExp @ ExpToTrig @ With[
  { new = KetChop @ expr },
  If[ Head[new] === Plus, 
    Map[Matrix[#, rest]&, new],
    Matrix[new, rest]
  ]
]
(* NOTE: rest__ NOT rest___ *)
(* NOTE: TrigToExp @ ExpToTrig helps simplify in many cases. *)
(* NOTE: KetChop is required here because "0. + Ket[...] + ..." may happen. *)

Matrix[ z_?CommutativeQ op_, rest__ ] := z * Matrix[op, rest]
(* NOTE: rest__ NOT rest___ *)

Matrix[ z_?CommutativeQ, {} ] := z * One[2]

Matrix[ z_?CommutativeQ, qq:{__?SpeciesQ} ] :=
  z * One[Aggregate @ Dimension @ qq]

Matrix[ z_?CommutativeQ, ss:{__?SpeciesQ}, tt:{__?SpeciesQ} ] :=
  z * One[{Aggregate @ Dimension @ ss, Aggregate @ Dimension @ tt}]


(* Dagger *)

HoldPattern @ Matrix[Dagger[op_?AgentQ], rest___] := Topple @ Matrix[op, rest]
(* NOTE: Matrix[a] may still include some operators; hence, Topple instead
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
  Matrix[expr_Association, rest__] := Map[Matrix[#, rest]&, expr]

HoldPattern @
  Matrix[expr_List, rest__] := Map[Matrix[#, rest]&, expr]
(* NOTE: {SparseArray[...], SparseArray[...], ...} may not take full advantage
   of sparse array, and we may add SparseArray at the end. But I decided not
   to do it as one usually expect {...} as the output. One should handle the
   output as he prefers. *)


(*  For Bra *)
Matrix[Bra[any_], rest___] := Conjugate @ Matrix[Ket[any], rest]


(* For Ket of unlabelled species *)
Matrix[vec:Ket[_List], {___}] := TheMatrix[vec]


(* For Ket of labelled species *)

Matrix[Ket[<||>], {}] := 0

Matrix[Ket[Vacuum], ss:{__?SpeciesQ}] := Matrix[Ket[<||>], ss]

Matrix[Ket[a_Association], ss:{__?SpeciesQ}] :=
  CircleTimes @@ Map[TheMatrix, Thread[ss -> Lookup[a, ss]]]


(* For Pauli[...] *)

Matrix[ op:Pauli[_List], {___} ] := TheMatrix[op]

Pauli /: (* for FromGottesmanMatrix and CliffordFactor *)
Matrix[Pauli[mm:{__Integer}], n_Integer] := Which[
  Length[mm] == n, ThePauli[mm],
  Length[mm] < n, MatrixEmbed[ThePauli @ mm, Range @ Length @ mm, n]
] /; If[ Length[mm] <= n, True,
    Message[Matrix::pauli, mm, n];
    False
  ]


(* For Fermions *)

Matrix[op_?FermionQ, qq:{__?SpeciesQ}] := fermionMatrix[op, qq]
(* NOTE: Dagger[fermion] is handled by Matrix[Dagger[...], ...] above. *)

(* NOTE: Matrix and MatrixIn must be consistent, recalling that
   Basis always sorts the Keys in Ket. This function also depends on Basis. *)
fermionMatrix[op_?FermionQ, ff:{___?SpeciesQ}] := Module[
  { mm },
  mm = SequenceCases[ ff,
    {pre___, op, post___} :> {
      fermionOne /@ {pre},
      {TheMatrix[op]},
      One /@ Dimension /@ {post} }
  ];
  If[ mm == {},
    Message[Matrix::fermion, op, ff];
    op * Matrix[1, ff],
    CircleTimes @@ Join @@ First[mm]
  ]
]

fermionOne[_?FermionQ] := ThePauli[3]

fermionOne[any_?SpeciesQ] := One[Dimension @ any]


(* For other Species *)

Matrix[op_?AnyAgentQ, ss:{__?SpeciesQ}] := Module[
  { mm = TheMatrix @ op,
    sp = FlavorMute @ Peel @ op,
    rr },
  rr = One /@ Dimension[ss];
  rr = Association @ Join[ Thread[ss -> rr], {sp -> mm} ];
  CircleTimes @@ rr
] /; MemberQ[ss, FlavorMute @ Peel @ op]
(* NOTE: Dagger[op] is handled by Matrix[Dagger[...], ...] above, but other modifiers such as Canon may happen. *)

Matrix[op_?AnyAgentQ, qq:{__?SpeciesQ}] := (
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
  Zero[{Length @ bs, Length @ bs}]
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
  AssociationThread[kk -> Flatten[mat, 1] ]
]

(**** </MatrixIn> ****)


(**** <ProperSystem> ****)

ProperSystem::usage = "ProperSystem[expr] returns a list of {values, vectors} of the eigenvalues and eigenstates of expr.\nProperSystsem[expr, {s1, s2, ...}] regards expr acting on the system consisting of the Species {s1, s2, ...}.\nThe operator expression may be in terms of either (but not both) Pauli[...] for unlabelled qubits or other labelled operators on Species."

ProperSystem::mixed = "The operator `` contains the Pauli operators of unlabelled qubits as well as other labelled operators for Species."

ProperSystem::incon = "Inconsistent Pauli operators in ``."

ProperSystem::eigsysno = "Could not get the eigenvalues and eigenvectors of ``."

ProperSystem[expr_] := Module[
  { ss = Agents[expr],
    pp = Cases[{expr}, Pauli[kk_List] :> kk, Infinity],
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
  
  rr = Complement[FlavorCap @ qq, ss];
  If[ rr == {}, Null,
    val = Flatten @ Transpose @ ConstantArray[val, Aggregate @ Dimension @ rr];
    vec = Flatten @ Outer[CircleTimes, vec, Basis @ rr]
   ];
  {val, vec}
 ]


ProperVectors::usage = "ProperVectors is an alias for " <>
  ToString[
    Hyperlink["ProperStates", "paclet:Q3/ref/ProperStates"],
    StandardForm
   ]

ProperStates::usage = "ProperStates[expr] returns a list of the eigenstates of expr.\nProperSystsem[expr, {s1, s2, ...}] regards expr acting on the system consisting of the Species {s1, s2, ...}.\nThe operator expression may be in terms of either (but not both) Pauli[...] for unlabelled qubits or other labelled operators on Species."

ProperStates::mixed = "The operator `` contains the Pauli operators of unlabelled qubits as well as other labelled operators for Species."

ProperStates::incon = "Inconsistent Pauli operators in ``."

ProperStates::eigsysno = "Could not get the eigenvalues and eigenvectors of ``."

ProperStates[expr_] := Module[
  { ss = Agents[expr],
    pp = Cases[{expr}, Pauli[kk_List] :> kk, Infinity],
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
  
  rr = Complement[FlavorCap @ qq, ss];
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
  
  rr = Complement[FlavorCap @ qq, ss];
  If[ rr == {},
    Return[val],
    Return @ Flatten @ Transpose @ ConstantArray[val, Aggregate @ Dimension @ rr]
  ]
]

(**** </ProperSystem> ****)


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

ParityValue[spec:(_?SpeciesQ|{___?SpeciesQ})] := 
  ParityValue[FlavorCap @ spec] /; Not[FlavorCapQ @ spec]

ParityValue[spec:(_?SpeciesQ|{___?SpeciesQ})][expr_] := 
  ParityValue[expr, spec]


ParityValue[expr_, spec:(_?SpeciesQ|{___?SpeciesQ})] := 
  ParityValue[expr, FlavorCap @ spec] /; Not[FlavorCapQ @ spec]


ParityValue[expr_Association, spec:(_?SpeciesQ|{___?SpeciesQ})] :=
  Map[ParityValue[spec], expr]

ParityValue[expr_List, spec:(_?SpeciesQ|{___?SpeciesQ})] :=
  Map[ParityValue[spec], expr]


ParityValue[z_?CommutativeQ expr_, spec:(_?SpeciesQ|{___?SpeciesQ})] :=
  ParityValue[expr, spec] /; Not @ FreeQ[expr, _Ket]

ParityValue[expr_Plus, spec:(_?SpeciesQ|{___?SpeciesQ})] := With[
  { vv = ParityValue[Union @ Cases[expr, _Ket, Infinity], spec] },
  If[Equal @@ vv, First @ vv, Indeterminate]
 ] /; Not @ FreeQ[expr, _Ket]


ParityValue[v_Bra, spec:(_?SpeciesQ|{___?SpeciesQ})] :=
  ParityValue[Dagger @ v, spec]

ParityValue[v_Ket, ss:{__?SpeciesQ}] :=
  Multiply @@ Map[ParityValue[v, #]&, ss]

ParityValue[Ket[<||>], {}] = 1

ParityValue[Ket[Vacuum], {}] = 1


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
  Not[ Xor @@ Map[ParityOddQ[v,#]&, FlavorCap @ ss] ]

ParityOddQ[ v_Ket, ss:{__?SpeciesQ} ] :=
  Xor @@ Map[ParityOddQ[v,#]&, FlavorCap @ ss]

(**** </Parity> ****)


(**** <RotationSystem> ****)

RotationSystem::usage = "RotationSystem[mat] returns the rotation angle and axis in the form {angle, {x, y, z}} that the matrix mat represents.\nFor rotations in the three-dimensional space of real vectors, mat is a 3\[Times]3 real orthogonal matrix. In this case, the returned angle is in the range from -\[Pi] to \[Pi].\nFor rotations in the Bloch space, mat is a 2\[Times]2 unitary matrix. Angle is in the range from -2\[Pi] to 2\[Pi].\nIn either case, the axis vector always points to the upper hemisphere."

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

TheEulerAngles::u = "Matrix `` is not a 2x2 unitary matrix; its determinant is ``."

TheEulerAngles[U_?MatrixQ] := Module[
  { arg = Arg[U],
    ang = {0, 0, 0} },
  
  If[ UnitaryMatrixQ[U],
    If[Chop[Det @ U] != 1, Message[TheEulerAngles::su, U, Det @ U]],
    Message[TheEulerAngles::u, U, Chop @ Det @ U]
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

Rotation::usage = "Rotation[\[Phi], 1], Rotation[\[Phi], 2], and Rotation[\[Phi], 3] returns an operator corresponding to the rotations by angle \[Phi] around the x, y, and z axis, respectively, on a two-dimensioinal Hilbert space.\nRotation[{a1, n1}, {a2, n2}, ...] = Rotation[a1, n1] \[CircleTimes] Rotation[a2, n2] \[CircleTimes] ...\nRotation[a, {x, y, z}] returns an operator corresponding the rotation by angle a around the axis along the vector {x, y, z}.\nRotation[\[Phi], {x, y, z}, S] represents the rotation by angle \[Phi] around the axis {x, y, z} on qubit or spin S.\nRotation[\[Phi], S[i,\[Ellipsis],1]] is equivalent to Rotation[\[Phi], {1, 0, 0}, S[i,\[Ellipsis],$]].\nRotation[\[Phi], S[i,\[Ellipsis],2]] is equivalent to Rotation[\[Phi], {0, 1, 0}, S[i,\[Ellipsis],$]].\nRotation[\[Phi], S[i,\[Ellipsis],3]] is equivalent to Rotation[\[Phi], {0, 0, 1}, S[i,\[Ellipsis],$]]."

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

Format[ op:Rotation[phi_, v:{_, _, _}, S:(_?SpinQ|_?QubitQ), rest___] ] :=
  Interpretation[
    DisplayForm @ RowBox @ { Exp,
      RowBox @ {"(", -I * (phi/2) * Dot[S @ All, Normalize @ v], ")"}
    },
    op 
  ]


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
 ) /; Not @ AllTrue[v, QuantumMob`Q3S`RealQ] /; AllTrue[v, NumericQ]

Rotation[phi_, v:{_, _, _}, S:(_?SpinQ|_?QubitQ), rest___] :=
  Rotation[phi, v, S[$], rest] /;
  Not[FlavorCapQ @ S]

Rotation[aa_List, v:{_, _, _}, S:(_?SpinQ|_?QubitQ), rest___] :=
  Map[Rotation[#, v, S, rest]&, aa]

Rotation[any_, v:{_, _, _}, ss:{(_?SpinQ|_?QubitQ)..}, rest___] :=
  Map[Rotation[any, v, #, rest]&, ss]


(* NOTE: The following code makes many calculations significantly slow. It is far better to use the high-level feature as those given below for MultiplyPower and Multiply. *)
(*
Rotation /:
Multiply[pre___, op_Rotation, post___] := Multiply[pre, Elaborate[op], post]
 *)

Rotation /:
MultiplyPower[Rotation[phi_, rest__], n_Integer] :=
  Rotation[n * phi, rest]

Rotation /:
Multiply[
  pre___, 
  Rotation[a_, axis_, ss_, opts___?OptoinQ],
  Rotation[b_, axis_, ss_, more___?OptoinQ],
  post___
] :=
  Multiply[pre, Rotation[a+b, axis, ss, more, opts], post]


Rotation /:
Dagger[ Rotation[ang_, v:{_, _, _}, S:(_?SpinQ|_?QubitQ), opts___?OptionQ] ] :=
  Rotation[-Conjugate[ang], v, S, ReplaceRulesBy[{opts}, "Label" -> mySuperDagger]]


Rotation /:
Matrix[op_Rotation, rest___] := Matrix[Elaborate @ op, rest]

(**** </Rotation> ****)


(**** <EulerRotation> ****)

EulerRotation::usage = "EulerRotation[{a, b, c}] = Rotation[a, 3].Rotation[b, 2].Rotation[c, 3] represent the Euler rotation by angles a, b, c in a two-dimensional Hilbert space."

EulerRotation[{a_, b_, c_}] :=
  Multiply[Rotation[a, 3], Rotation[b, 2], Rotation[c, 3]]

EulerRotation[a:{_, _, _}, b:{_, _, _}..] :=
  CircleTimes @@ Map[EulerRotation, {a, b}]


(* Rotation on Qubit and Spin *)

Options[EulerRotation] = { "Label" -> Automatic }


EulerRotation[aa:{_, _, _}, ss:{(_?SpinQ|_?QubitQ)..}, rest___] :=
  Map[EulerRotation[aa, #, rest]&, FlavorCap @ ss]

EulerRotation[aa:{_, _, _}, G:(_?SpinQ|_?QubitQ), rest___] :=
  EulerRotation[aa, G[$], rest] /; Not[FlavorCapQ @ G]


(* NOTE: The following code makes many calculations significantly slow. It is far better to use the high-level feature as those given below for MultiplyPower and Multiply. *)
(*
EulerRotation /:
Multiply[pre___, op_EulerRotation, post___ ] :=
  Multiply[pre, Elaborate @ op, post]
 *)

EulerRotation /:
Dagger @ EulerRotation[{a_, b_, c_}, S:(_?SpinQ|_?QubitQ), opts___?OptionQ] :=
  EulerRotation[{-c, -b, -a}, S, ReplaceRulesBy[{opts}, "Label" -> mySuperDagger]]


EulerRotation /:
Matrix[op_EulerRotation, rest___] := Matrix[Elaborate @ op, rest]


EulerRotation /:
Elaborate @ EulerRotation[{a_, b_, c_}, S:(_?SpinQ|_?QubitQ), ___] :=
  Garner @ Elaborate @
  Multiply[ Rotation[a, S[3]], Rotation[b, S[2]], Rotation[c, S[3]] ]

EulerRotation /:
Expand @ EulerRotation[{a_, b_, c_}, S:(_?SpinQ|_?QubitQ), ___] :=
  QuantumCircuit[ Rotation[a, S[3]], Rotation[b, S[2]], Rotation[c, S[3]] ]

(**** </EulerRotation> ****)


(**** <PauliDot> ****)

PauliDot::usage = "PauliDot[a, b, \[Ellipsis]] represents the non-commutative multiplication between Pauli operators a, b, \[Ellipsis]."

SetAttributes[PauliDot, {Flat, OneIdentity}];

Format[PauliDot[a_Pauli, b_Pauli]] := Row @ {"(",a,")","(",b,")"}
(* NOTE: Normally, this should not occur. However, for example, incompatible Pauli strings are left unevaluated. *)

PauliDot[expr_Plus, a_] := Map[PauliDot[#, a]&, expr]

PauliDot[a_, expr_Plus] := Map[PauliDot[a, #]&, expr]

PauliDot[ a_ * b_, c_] :=
  a * PauliDot[b, c] /; FreeQ[a, _PauliDot|_Pauli|_Ket|_Bra]

PauliDot[ a_, b_ * c_] :=
  b * PauliDot[a, c] /; FreeQ[b, _PauliDot|_Pauli|_Ket|_Bra]


PauliDot[Bra[a_List], Ket[b_List]] := BraKet[a, b]


(* Pauli operating on Ket and Bra *)

PauliDot[ Pauli[{0}], a_Ket ] := a

PauliDot[ a_Bra, Pauli[{0}] ] := a

PauliDot[ Pauli[{n:(1|2|3|4|5|6|7|8)}], Ket[{0|Up}] ] :=
  Dot[ {Ket[0], Ket[1]}, ThePauli[n][[;;, 1]] ]

PauliDot[ Pauli[{n:(1|2|3|4|5|6|7|8)}], Ket[{1|Down}] ] :=
  Dot[ {Ket[0], Ket[1]}, ThePauli[n][[;;, 2]] ]

PauliDot[ Bra[{0|Up}], Pauli[{n:(1|2|3|4|5|6|7|8)}] ] :=
  Dot[ ThePauli[n][[1, ;;]], {Bra[0], Bra[1]} ]

PauliDot[ Bra[{1|Down}], Pauli[{n:(1|2|3|4|5|6|7|8)}] ] :=
  Dot[ ThePauli[n][[2, ;;]], {Bra[0], Bra[1]} ]

PauliDot[ z_?CommutativeQ, op_Pauli ] := z * op

PauliDot[ op_Pauli, z_?CommutativeQ ] := z * op

PauliDot[ Pauli[{0}], Pauli[{n_}] ] := Pauli[{n}]

PauliDot[ Pauli[{n_}], Pauli[{0}] ] := Pauli[{n}]

PauliDot[ Pauli[{n:(0|1|2|3)}], Pauli[{n_}] ] := Pauli[0]

PauliDot[ Pauli[{m_}], Pauli[{n_}] ] := Pauli[{0}] /; m == -n

PauliDot[ Pauli[{7}], Pauli[{7}] ] := Pauli[{3}]

PauliDot[ Pauli[{8}], Pauli[{8}] ] := Pauli[{7}]

PauliDot[ Pauli[{n:(4|5)}], Pauli[{n_}] ] := 0

PauliDot[ Pauli[{1}], Pauli[{2}] ] := I Pauli[{3}]

PauliDot[ Pauli[{2}], Pauli[{3}] ] := I Pauli[{1}]

PauliDot[ Pauli[{3}], Pauli[{1}] ] := I Pauli[{2}]

PauliDot[ Pauli[{2}], Pauli[{1}] ] := -I Pauli[{3}]

PauliDot[ Pauli[{3}], Pauli[{2}] ] := -I Pauli[{1}]

PauliDot[ Pauli[{1}], Pauli[{3}] ] := -I Pauli[{2}]

(* general rules *)

(*
PauliDot[ Pauli[m_], Pauli[n_] ] :=
  Garner @ PauliDot[Elaborate @ Pauli @ m, Elaborate @ Pauli @ n]
 *)

PauliDot[ Pauli[aa_List], Pauli[bb_List] ] := CircleTimes @@
  PauliDot @@@ Transpose[Elaborate @ {Pauli /@ aa, Pauli /@ bb}] /;
  If[ ArrayQ[{aa, bb}], True,
    Message[Pauli::dot, aa, bb]; False
  ]
  
PauliDot[ Pauli[aa_List], Ket[bb_List] ] := CircleTimes @@
  PauliDot @@@ Transpose[{Pauli /@ aa, Ket /@ bb}]

PauliDot[ Bra[aa_List], Pauli[bb_List] ] := CircleTimes @@
  PauliDot @@@ Transpose[{Bra /@ aa, Pauli /@ bb}]

(**** </PauliDot> ****)


(**** <CircleTimes> ****)

CircleTimes::usage = "CircleTimes[a,b,c] or a \[CircleTimes] b \[CircleTimes] c represents the tensor product of (abstract) algebraic tensors a, b, c, ....\nWhen a, b, c, ... are vectors or matrices, it returns the matrix direct product of them.\nCirlceTimes is a built-in symbol with context System`, and has been extended in Q3.\nSee \!\(\*TemplateBox[{\"Q3/ref/CircleTimes\", \"paclet:Q3/ref/CircleTimes\"}, \"RefLink\", BaseStyle->\"InlineFunctionSans\"]\) for more details."

SetAttributes[CircleTimes, ReadProtected]

CircleTimes[] = 1 (* See also Times[]. *)

CircleTimes[a_] := a (* See also Times[]. *)

(* NOTE: DO NOT set the Flat and OneIdentity attributes for
   Cirlcetimes. Otherwise, the following definitions cause infinite loops. *)

HoldPattern @ CircleTimes[args__] := Garner @ ReleaseHold[
  Distribute @ Hold[CircleTimes][args]
] /; DistributableQ[{args}]
(* NOTE: The Inactive-Activate pair may also be used, but is slower. *)

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
CircleTimes[vecs__?VectorQ] := Flatten @ KroneckerProduct[vecs]

(**** </CircleTimes> ****)


(**** <CirclePlus> ****)

CirclePlus::usage = "a \[CirclePlus] b \[CirclePlus] c or CirclePlus[a,b,c]
returns the direct sum of the matrices a, b, and c."

CirclePlus[pre___, {}, post___] := CirclePlus[pre, post]

CirclePlus[mm__?MatrixQ] := 
  SparseArray @ BlockDiagonalMatrix[{mm}, TargetStructure -> "Sparse"]

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
MultiplyGenus @ Dyad[___] := "Singleton"

Dyad /:
MultiplyKind @ Dyad[a_Association, b_Association] :=
  First @ MultiplyKind @ Union[Keys @ a, Keys @ b]


Dyad /:
Dagger[op_Dyad] := Conjugate[op] (* fallback *)

Dyad /:
Dagger @ Dyad[a_Association, b_Association] = Dyad[b, a]


Dyad /:
Elaborate[op_Dyad] = op (* fallback *)

Dyad /:
Elaborate @ Dyad[a_Association, b_Association] := Module[
  { cc = Keys @ a,
    na = Values @ a,
    nb = Values @ b,
    nn },
  nn = (1 - na)*(1 - nb);
  Multiply[
    Multiply @@ Power[Dagger @ cc, na],
    Multiply @@ Power[1 - Dagger[cc] ** cc, nn],
    Multiply @@ Power[Reverse @ cc, Reverse @ nb]
  ]
] /; AllTrue[Keys @ a, FermionQ] && Keys[a] == Keys[b]
(* NOTE: This assumes that the keys in Ket are sorted. *)

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
Matrix[op_Dyad, ss_List, tt_List] := Zero[{Length @ ss, Length @ tt}]
  
Dyad /:
Matrix[op_Dyad, ss:{__?SpeciesQ}, tt:{__?SpeciesQ}] :=
  Matrix[op, FlavorCap @ ss, FlavorCap @ tt] /;
  Not[FlavorCapQ @ {ss, tt}]

Dyad /:
Matrix[ Dyad[a_Association, b_Association],
  ss:{__?SpeciesQ}, tt:{__?SpeciesQ} ] := Module[
    { sa = Complement[ss, Keys @ a],
      tb = Complement[tt, Keys @ b],
      aa, bb },
    If[sa != tb,
      Message[Dyad::mtrx, Row @ {ss, Keys @ a, Keys @ b, tt}];
      Return[Zero @ {Length @ ss, Length @ tt}]
     ];
    aa = Map[TheMatrix] @ Map[KeyTake[ss]] @ Map[Join[a, #]&] @
      Map[AssociationThread[sa -> #]&] @ Tuples[LogicalValues @ sa];
    bb = Map[TheMatrix] @ Map[KeyTake[tt]] @ Map[Join[b, #]&] @
      Map[AssociationThread[tb -> #]&] @ Tuples[LogicalValues @ tb];
    Total @ MapThread[ Dyad, {CircleTimes @@@ aa, CircleTimes @@@ bb}]
   ]


Dyad /: (* fallback *)
Matrix[op_Dyad, ss_List] := Zero[{Length @ ss, Length @ ss}]
  
Dyad /:
Matrix[op_Dyad, ss:{__?SpeciesQ}] := Matrix[op, FlavorCap @ ss] /;
  Not[FlavorCapQ @ ss]

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
    One[Aggregate @ Dimension @ ss]
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
    { sss = Union @ FlavorCap @ Join[ss],
      ttt = Union @ FlavorCap @ Join[tt] },
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


Dyad[S_?SpeciesQ] := Dyad[FlavorCap @ {S}]

Dyad[ss:{__?SpeciesQ}] := Dyad[FlavorCap @ ss] /; Not[FlavorCapQ @ ss]

Dyad[ss:{__?SpeciesQ}][a_, b_] := Dyad[a, b, ss]


Dyad[a_, b_, ss_] := Dyad[a, b, ss, ss]

Dyad[a_, b_, S_?SpeciesQ, tt_] := Dyad[a, b, S @ {$}, tt]

Dyad[a_, b_, ss_, T_?SpeciesQ] := Dyad[a, b, ss, T @ {$}]

Dyad[a_, b_, ss:{__?SpeciesQ}, tt:{__?SpeciesQ}] :=
  Dyad[a, b, FlavorCap @ ss, FlavorCap @ tt] /;
  Not[FlavorCapQ @ {ss, tt}]

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
   Multiply[ pre,
     Dyad[
       KeySort @ CheckJoin[a, KeyTake[c, cc]],
       KeySort @ CheckJoin[d, KeyTake[b, bb]]
      ] * BraKet[KeyTake[b, bc], KeyTake[c, bc]],
     post ]
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
Dyad[Ket[a:{(0|1)..}], Ket[b:{(0|1)..}], ___] := Pauli @ Thread[b -> a]

(* For general kets for unlabelled systems *)
Dyad[a_Ket, b_Ket, ___] := Multiply[a, Dagger @ b]


(* For simple column vectors *)

Dyad[a_?VectorQ] := ( Message[Dyad::one]; Dyad[a, a] ) /; FreeQ[a, _?SpeciesQ]

Dyad[a_?VectorQ, b_?VectorQ] := KroneckerProduct[a, Dagger @ b]
(* NOTE: Dagger -- not Conjugate -- in the above two definitions. *)

(**** </Dyad> ****)


(**** <DyadForm> ****)

DyadForm::usage = "DyadForm[expr,{s1,s2,..}] converts the operator expression expr to the form in terms of Dyad acting on the systems s1, s2, .... If the systems are not specified, then they are extracted from expr.\nDyadForm[mat,{s1,s2,...}] converts the matrix representation into an operator expresion in terms of Dyad acting on the systems s1, s2, ...."

DyadForm[expr_] := RaisingLoweringForm[expr] /; Not @ FreeQ[expr, _Pauli]
(* NOTE: DyaForm is pointless for Pauli expressions. *)

DyadForm[expr_] := DyadForm[expr, Agents @ expr]

DyadForm[expr_, q_?SpeciesQ] := DyadForm[expr, q @ {$}]

DyadForm[expr_, qq:{__?SpeciesQ}] := DyadForm[Matrix[expr, qq], qq]

DyadForm[expr_, qq:{__?SpeciesQ}] := DyadForm[expr, FlavorCap @ qq] /;
  Not[FlavorCapQ @ qq]


DyadForm[mat_?MatrixQ] := Module[
  { n = Log[2, Length @ mat],
    tsr },
  tsr = ArrayReshape[mat, ConstantArray[2, 2*n]];
  tsr = Association @ Most @ ArrayRules @ tsr;
  Garner @ Total @ KeyValueMap[theDyadForm[#1, n] * #2&, tsr]
] /; IntegerPowerQ[2, Length @ mat]

theDyadForm[val:{__}, n_Integer] := Module[
  {a, b},
  {a, b} = ArrayReshape[val-1, {2, n}];
  Pauli @ Thread[b -> a]
]


DyadForm[mat_?MatrixQ, qq:{__?SpeciesQ}] := Module[
  { dim = Dimension @ qq,
    spc = FlavorCap @ qq,
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

(**** </DyadForm> ****)


(**** <PauliVector> ****)

PauliVector::usage = "PauliVector[mat] returns the Pauli expansion coefficients of the traceless part of 2\[Times]2 matrix mat."

PauliVector::dim = "`` is not a 2\[Times]2 matrix."

PauliVector @ {{a_, b_}, {c_, d_}} := {b+c, I*(b-c), a-d} / 2

PauliVector[mat_?MatrixQ] := PauliVector[Normal @ mat] /;
  Dimensions[mat] == {2, 2}

PauliVector[mat_] := (
  Message[PauliVector::dim, mat];
  {0, 0, 0}
)

(**** </PauliVector> ****)


(**** <PauliCoefficients> ****)

PauliCoefficients::usage = "PauliCoefficients[mat] gives an Association of coefficients in the expansion of 2^n\[Times]2^n matrix mat in the Pauli matrices."

PauliCoefficients::dim = "The dimensions `` of matrix `` are not integer powers of 2."

Options[PauliCoefficients] = {
  "RaisingLowering" -> False
};

PauliCoefficients[mat_?SquareMatrixQ, OptionsPattern[]] := Module[
  { n = Log[2, Length @ mat] },
  If[ Not[IntegerQ @ n],
    Message[PauliCoefficients::dim, Dimensions @ mat, mat];
    Return[<||>]
  ];
  If[ OptionValue["RaisingLowering"],
    thePauliCoeffsRL[mat, n],
    thePauliCoeffsXY[mat, n]
  ]
]

thePauliCoeffsXY[mat_?SquareMatrixQ, n_Integer] := Module[
  { trs },
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

thePauliCoeffsRL[mat_?SquareMatrixQ, n_Integer] := Module[
  { trs },
  trs = SparseArray @ {
    {1, 0, 0, 1}/2,
    {0, 1, 0, 0},
    {0, 0, 1, 0},
    {1, 0, 0,-1}/2
  };
  trs = CircleTimes @@ Table[trs, n];
  trs = Association @ Most @ ArrayRules @ Chop @
    ArrayReshape[trs . Flatten[Tensorize @ mat], Table[4, n]];
  KeySort @ KeyReplace[trs, {1 -> 0, 2 -> 4, 3 -> 5, 4 -> 3}]
]

(**** </PauliCoefficients> ****)


(**** <PauliSeries> ****)

PauliSeries::usage = "PauliSeries[assc] reconstructs the matrix using the Pauli expansion coefficients given in Association assc."

PauliSeries[aa_Association] :=
  Total @ KeyValueMap[(ThePauli[#1] * #2)&, aa]

(**** </PauliSeries> ****)


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
  { ab = FlavorCap @ Join[aa, bb],
    ww, uu, vv },
  { ww, uu, vv } = SchmidtDecomposition[
    Matrix[expr, ab],
    {Aggregate @ Dimension @ aa, Aggregate @ Dimension @ bb}
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
  { rr = FlavorCap @ Cases[qq, _?NonCommutativeQ],
    ss = Agents[expr],
    dd, jj, mm },
  ss = Union[ss, rr];
  dd = Dimension[ss];
  jj = Flatten @ Map[FirstPosition[ss, #]&, rr];
  mm = PartialTranspose[Matrix[expr, ss], dd, jj];
  ExpressionFor[mm, ss]
]

(**** </PartialTranspose> ****)


(**** <PartialTransposeNorm> ****)

PartialTransposeNorm::usage = "PartialTransposeNorm[rho, spec] returns the trace norm of the partial transpose of rho, where the partial transposition is specified by spec (see PartialTranspose)."

PartialTransposeNorm[vec_?VectorQ, spec__] := TraceNorm @ PartialTranspose[vec, spec]

PartialTransposeNorm[mat_?MatrixQ, spec__] := TraceNorm @ PartialTranspose[mat, spec]


PartialTransposeNorm[rho_, jj:{__Integer}] :=
  PartialTransposeNorm[Matrix @ rho, jj] /;
  Or[fPauliKetQ[rho], Not @ FreeQ[expr, _Pauli]]

(* 
PartialTransposeNorm[rho_, qq:{__?SpeciesQ}] := Module[
  { rr = FlavorCap @ Cases[qq, _?NonCommutativeQ],
    ss = Agents[rho],
    all, pos, mat, trm },
  all = Union @ FlavorCap @ Join[rr, ss];
  pos = Flatten @ Map[FirstPosition[all, #]&, FlavorCap @ rr];
  mat = Matrix[rho, all];

  trm = If[MatrixQ[mat], Tr[mat], Norm[mat]^2];
  If[Chop[trm] == 0, Message[PartialTransposeNorm::traceless, rho]; Return[1]];
  
  PartialTransposeNorm[mat, Dimension @ all, pos] / trm
] 
 *)
(* NOTE: Too dangerous, and removed. *)
(* NOTE: rho is assumed to be properly normalized; and hence the factor ofr
   1/trm in the code. *)


PartialTransposeNorm[rho_, aa:{__?SpeciesQ}, bb:{__?SpeciesQ}] := Module[
  { all, pos, mat },
  all = Union @ FlavorCap @ Join[aa, bb];
  pos = Flatten @ Map[FirstPosition[all, #]&, FlavorCap @ bb];
  mat = Matrix[rho, all];
  PartialTransposeNorm[mat, Dimension @ all, pos]
]
(* NOTE 1: For PartialTranspose, argument aa is not necessary. However, it
   is necessary for proper normalization. For example, consider rho = I x I /
   4. Without aa, it may be regarded as I / 4, which leads to a wrong value of
   the logarithmic negativity. *)
(* NOTE 2: rho may refer to a pure state; i.e., mat may be a vector. *)

PartialTransposeNorm[rho_, S_?SpeciesQ, bb:{__?SpeciesQ}] := PartialTransposeNorm[rho, {S}, bb]

PartialTransposeNorm[rho_, aa:{__?SpeciesQ}, T_?SpeciesQ] := PartialTransposeNorm[rho, aa, {T}]

PartialTransposeNorm[rho_, S_?SpeciesQ, T_?SpeciesQ] := PartialTransposeNorm[rho, {S}, {T}]

(* PartialTransposeNorm[rho_, S_?SpeciesQ] := PartialTransposeNorm[rho, {S}] *)
(* NOTE: Too dangerous! *)


Negativity::usage = "Negativity[rho, spec] returns the negativity of quantum state rho.\nFor specification spec of the rest of the arguments, see PartialTranspose."

Negativity[spec__] := (PartialTransposeNorm[spec] - 1) / 2


LogarithmicNegativity::usage = "LogarithmicNegativity[rho, spec] returns the logarithmic negativity of quantum state rho.\nFor specification spec of the rest of the arguments, see PartialTranspose."

LogarithmicNegativity[spec__] := Log[2, PartialTransposeNorm[spec]]

(**** </PartialTransposeNorm> ****)


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
  { tt = FlavorCap[ss] },
  PartialTrace[expr, Union[Agents @ expr, tt], tt]
]

PartialTrace[expr_, qq:{__?SpeciesQ}, S_?SpeciesQ] :=
  PartialTrace[expr, qq, {S}]

PartialTrace[expr_, qq:{__?SpeciesQ}, ss:{__?SpeciesQ}] := Module[
  { bb = FlavorCap @ Cases[ss, _?NonCommutativeQ],
    aa, dd, jj, mm },
  aa = Agents @ {expr, FlavorCap @ qq};
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
) /; Not @ IntegerPowerQ[2, Length @ rho]

ReducedMatrix[rho:(_?VectorQ|_?MatrixQ), jj:{__Integer}] :=
  ReducedMatrix[rho, ConstantArray[2, Log[2, Length @ rho]], jj]


ReducedMatrix[expr_, S_?SpeciesQ] := ReducedMatrix[expr, {S}]

ReducedMatrix[expr_, ss:{__?SpeciesQ}] := Module[
  { qq = Agents[expr],
    rr = Agents[FlavorCap @ ss],
    jj },
  qq = Union[qq, rr];
  jj = Flatten @ Map[FirstPosition[qq, #]&, Complement[qq, rr]];
  PartialTrace[Matrix[expr, qq], Dimension[qq], jj]
]


ReducedMatrix[expr_, jj:{__Integer}] := Module[
  { nn = Length @ FirstCase[expr, Ket[ss_List] :> ss, Infinity] },
  PartialTrace[Matrix[expr], Complement[Range @ nn, jj]]
] /; fPauliKetQ[expr]

ReducedMatrix[expr_, jj:{__Integer}] := Module[
  { nn = Length @ FirstCase[expr, Pauli[kk_List] :> kk, Infinity] },
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

Purification[rho_, S_?SpeciesQ] := Purification[rho, FlavorCap @ {S}]

Purification[rho_] := With[
  { ss = Agents[rho] },
  Purification[rho, ss]
] /; FreeQ[rho, _Pauli]

Purification[rho_] := ExpressionFor @ Purification @ Matrix[rho] /;
  Not @ FreeQ[rho, _Pauli]

Purification[z_?CommutativeQ] := ExpressionFor @ Purification[z * One[2]]
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

MatrixEmbed[ss:{__?SpeciesQ}, tt:{__?SpeciesQ}] :=
  MatrixEmbed[FlavorCap @ ss, FlavorCap @ tt] /;
  Not[FlavorCapQ @ Join[ss, tt]]

MatrixEmbed[ss:{__?SpeciesQ}, tt:{__?SpeciesQ}][any_] :=
  MatrixEmbed[any, ss, tt]

MatrixEmbed[any_, ss:{__?SpeciesQ}, tt:{__?SpeciesQ}] :=
  MatrixEmbed[any, FlavorCap @ ss, FlavorCap @ tt] /;
  Not[FlavorCapQ @ Join[ss, tt]]

MatrixEmbed[any_, ss:{___?SpeciesQ}, ss_] = any
(* NOTE: Quite often, MatrixEmbed[expr, {}, {}] occurs from Matrix. *)

MatrixEmbed[mat_?MatrixQ, ss:{__?SpeciesQ}, tt:{__?SpeciesQ}] := Module[
  { rmd = Complement[tt, ss],
    new, idx },
  new = CircleTimes[mat, One[Aggregate @ Dimension @ rmd]];
  idx = PermutationList @ FindPermutation[Join[ss, rmd], tt];
  TensorFlatten @ Transpose[
    Tensorize[new, Riffle @@ Table[Dimension @ Join[ss, rmd], 2]],
    Riffle[2*idx - 1, 2*idx]
  ]
] /; ContainsAll[tt, ss]

MatrixEmbed[vec_?VectorQ, ss:{__?SpeciesQ}, tt:{__?SpeciesQ}] := Module[
  { rmd = Complement[tt, ss],
    new, idx },
  new = CircleTimes[vec, UnitVector[Aggregate @ Dimension @ rmd, 1]];
  idx = PermutationList @ FindPermutation[Join[ss, rmd], tt];
  Flatten @ Transpose[
    ArrayReshape[new, Dimension @ Join[ss, rmd]],
    idx
  ]
] /; ContainsAll[tt, ss]

MatrixEmbed[_, ss:{__?SpeciesQ}, tt:{__?SpeciesQ}] :=
  Message[MatrixEmbed::rmdr, ss, tt]


MatrixEmbed[kk:{__Integer}, n_Integer] :=
  MatrixEmbed[kk, Table[2, n]]

MatrixEmbed[kk:{__Integer}, dd:{__Integer}][any_] :=
  MatrixEmbed[any, kk, dd]


MatrixEmbed[any_, kk:{__Integer}, n_Integer] :=
  MatrixEmbed[any, kk, Table[2, n]]

MatrixEmbed[mat_?MatrixQ, kk:{__Integer}, dd:{__Integer}] := Module[
  { all = Range @ Length @ dd,
    rmd, new, idx },
  rmd = Complement[all, kk];
  new = CircleTimes[mat, One[Aggregate @ Part[dd, rmd]]];
  idx = PermutationList @ FindPermutation[Join[kk, rmd], all];
  TensorFlatten @ Transpose[
    Tensorize[new, Riffle @@ Table[Part[dd, Join[kk, rmd]], 2]],
    Riffle[2*idx - 1, 2*idx]
  ]
] /; And @@ Thread[kk <= Length[dd]]

MatrixEmbed[vec_?VectorQ, kk:{__Integer}, dd:{__Integer}] := Module[
  { all = Range @ Length @ dd,
    rmd, new, idx },
  rmd = Complement[all, kk];
  new = CircleTimes[vec, UnitVector[Aggregate @ Part[dd, rmd], 1]];
  idx = PermutationList @ FindPermutation[Join[kk, rmd], all];
  Flatten @ Transpose[
    ArrayReshape[new, Part[dd, Join[kk, rmd]]],
    idx
  ]
] /; And @@ Thread[kk <= Length[dd]]

MatrixEmbed[_, kk:{__Integer}, dd:{__Integer}] :=
  Message[MatrixEmbed::rmdr, kk, Range @ Length @ tt]

(**** </MatrixEmbed> ****)


(**** <RandomState> ****)

RandomState::usage = "RandomState[{s1, s2, \[Ellipsis]}] returns a random normalized state vector in the Hilbert space of species {s1, s2, \[Ellipsis]} distributed uniformly in terms of the Haar measure.\nRandomState[{s1, s2, \[Ellipsis]}, n] returns n mutually orthogonal and uniformly distributed state vectors (hence, n cannot be larger than the total Hilbert space dimension)."

RandomState::dim = "Cannot generate more than dimension `` mutually orthogonal states."

RandomState[S_?SpeciesQ, spec___] := RandomState[S @ {$}, spec]

RandomState[ss:{__?SpeciesQ}, spec___] := RandomState[FlavorCap @ ss, spec] /; Not[FlavorCapQ @ ss]

RandomState[ss:{__?SpeciesQ}] := First @ RandomState[ss, 1]

RandomState[ss:{__?SpeciesQ}, n_Integer] := With[
  { dim = Aggregate[Dimension @ ss] },
  Basis[ss] . RandomIsometric[{dim, n}] /;
  If[ dim >= n, True,
    Message[RandomState::dim, dim];
    False
  ]
]

(**** </RandomState> ****)


(**** <HilbertSchmidtNorm> *****)

FrobeniusNorm::usage = "FrobeniusNorm is an alias for HilbertSchmidtNorm."

FrobeniusNorm = HilbertSchmidtNorm

HilbertSchmidtNorm::usage = "HilbertSchmidtNorm[a] gives the Hilbert-Schmidt norm (i.e., Frobenius norm) of a complex matrix a.\nIf a is a vector, it is regarded as Dyad[a,a].\nSee also TraceNorm."

HilbertSchmidtNorm[v_?VectorQ] := Norm[v]^2

HilbertSchmidtNorm[m_?MatrixQ] := Norm[m, "Frobenius"]

(* HilbertSchmidtNorm[rho_] := HilbertSchmidtNorm @ Matrix[rho] *)
(* NOTE: Too dangerous! *)

HilbertSchmidtNorm[rho_, qq:(_?SpeciesQ|{__?SpeciesQ})] :=
  HilbertSchmidtNorm @ Matrix[rho, qq]


FrobeniusDistance::usage = "FrobeniusDistance is an alias for HilbertSchmidtDistance."

FrobeniusDistance = HilbertSchmidtDistance


HilbertSchmidtDistance::usage = "HilbertSchmidtDistance[a, b] returns the Hilbert-Schmidt distance of two (pure or mixed) states a and b. It is equivalent to HilbertSchmidtNorm[a-b]."

HilbertSchmidtDistance[a_?MatrixQ, b_?MatrixQ] := HilbertSchmidtNorm[a - b]

HilbertSchmidtDistance[a_?VectorQ, b_?MatrixQ] := HilbertSchmidtNorm[Dyad[a, a] - b]

HilbertSchmidtDistance[b_?MatrixQ, a_?VectorQ] := HilbertSchmidtNorm[Dyad[a, a] - b]

HilbertSchmidtDistance[a_?VectorQ, b_?VectorQ] := HilbertSchmidtNorm[Dyad[a, a] - Dyad[b, b]]


HilbertSchmidtDistance[a_, b_, ss:(_?SpeciesQ | {___?SpeciesQ})] :=
  HilbertSchmidtDistance[Matrix[a, ss], Matrix[b, ss]]


FrobeniusProduct::usage = "FrobeniusProduct is an alias for HilbertSchmidtProduct."

FrobeniusProduct = HilbertSchmidtProduct

HilbertSchmidtProduct::usage = "HilbertSchmidtProduct[a, b] returns the Hilbert-Schmidt (or Frobenius) inner product of two matrices a and b, that is, Tr[ConjugateTranspose[a].b].\nIf a is a vector, it is regarded as Dyad[a,a], and similary for b."

HilbertSchmidtProduct::incmp = "Two matrix `1` and `2` are not compatible for the Hilbert-Schmidt inner product."

HilbertSchmidtProduct[a_?MatrixQ, b_?MatrixQ] := (
  Message[HilbertSchmidtProduct::incmp, a, b];
  Return[0]
 )

HilbertSchmidtProduct[a_?MatrixQ, b_?MatrixQ] := Tr[Topple[a] . b] /;
  ArrayQ[{a, b}]

HilbertSchmidtProduct[a_?VectorQ, b_?MatrixQ] := Conjugate[a] . b . a

HilbertSchmidtProduct[a_?MatrixQ, b_?VectorQ] := Conjugate[a] . Topple[b] . a

HilbertSchmidtProduct[a_?VectorQ, b_?VectorQ] := Abs[Conjugate[a] . b]^2


HilbertSchmidtProduct[a_, b_] := With[
  { ss = Agents @ {a, b} },
  HilbertSchmidtProduct[a, b, ss]
]


HilbertSchmidtProduct[S_?SpeciesQ] :=
  HilbertSchmidtProduct[FlavorCap @ {S}]

HilbertSchmidtProduct[ss:{___?SpeciesQ}] :=
  HilbertSchmidtProduct[FlavorCap @ ss] /; Not[FlavorCapQ @ ss]

HilbertSchmidtProduct[ss:{___?SpeciesQ}][a_, b_] :=
  HilbertSchmidtProduct[a, b, ss]

HilbertSchmidtProduct[a_, b_, ss:{___?SpeciesQ}] :=
  HilbertSchmidtProduct[Matrix[a, ss], Matrix[b, ss]]

(**** </HilbertSchmidtNorm> *****)


(**** <TraceNorm> *****)

TraceNorm::usage = "TraceNorm[mat] returns the trace norm of matrix mat.\nTraceNorm[vec] is equivalent to TraceNorm[Dyad[vec, vec]] and Norm[vec]^2.\nTraceNorma[op, {s1, s2, \[Ellipsis]}] returns the trace norm of operator op acting on a system of species s1, s2, \[Ellipsis]."

TraceNorm[m_?MatrixQ] := Total @ SingularValueList[m]

TraceNorm[v_?VectorQ] := Norm[v]^2


(* TraceNorm[rho:Except[_?MatrixQ | _?VectorQ]] := TraceNorm @ Matrix[rho] *)
(* NOTE: Still too dangerous! *)

TraceNorm[rho_, spec:(_?SpeciesQ | {__?SpeciesQ})] := TraceNorm @ Matrix[rho, spec]


TraceDistance::usage = "TraceDistance[a, b] returns the trace distance of the two square matrices a and b, which equals to TraceNorm[a - b]."

TraceDistance[a_?MatrixQ, b_?MatrixQ] := TraceNorm[a-b]

TraceDistance[a_?VectorQ, b_?MatrixQ] := TraceNorm[Dyad[a, a] - b]

TraceDistance[a_?MatrixQ, b_?VectorQ] := TraceNorm[a - Dyad[b, b]]

TraceDistance[a_?VectorQ, b_?VectorQ] := TraceNorm[Dyad[a, a] - Dyad[b, b]]
(* NOTE: This is NOT equal to TraceNorm[a - b]. *)

(* TraceDistance[a_, b_] := TraceDistance[a, b, Agents @ {a, b}] *)
(* NOTE: Too dangerous! *)

TraceDistance[a_, b_, ss:(_?SpeciesQ | {___?SpeciesQ})] :=
  TraceDistance[Matrix[a, ss], Matrix[b, ss]]

(**** </TraceNorm> *****)


(**** <Fidelity> *****)

Fidelity::usage = "Fidelity[\[Rho],\[Sigma]] returns the fidelity of the states \[Rho] and \[Sigma]. \[Rho] and \[Sigma] can take a vector (pure state), matrix (mixed state), ket expression (pure state), or opertor expression (mixed state).\nSee also ClassicalFidelity."

Fidelity::num = "For efficiency, Fidelity supports only numerical matrices. For symbolic matrices, resort to the definition."

Fidelity[a_?MatrixQ, b_?MatrixQ] := With[
  { c = MatrixPower[a, 1/2] },
  Tr @ MatrixPower[c . b . c, 1/2]
] /; If[ MatrixQ[a, NumericQ] && MatrixQ[b, NumericQ],
    True,
    Message[Fidelity::num];
    False
  ]


Fidelity[v_?VectorQ, m_?MatrixQ] := Sqrt[Conjugate[v] . m . v]

Fidelity[m_?MatrixQ, v_?VectorQ] := Fidelity[v, m]

Fidelity[a_?VectorQ, b_?VectorQ] := Abs[Conjugate[a] . b]


Fidelity[rho_, sgm_, ss:(_?SpeciesQ|{___?SpeciesQ})] :=
  Fidelity[Matrix[rho, ss], Matrix[sgm, ss]]


(* 
Fidelity[rho_, sgm_] := Fidelity @@ Matrix @ {rho, sgm} /;
  And[FreeQ[rho, _Ket], FreeQ[sgm, _Ket]]
 *)
(* NOTE: Too dangerous! *)

(*  
Fidelity[vec_, rho_] := Chop @ Sqrt[Dagger[vec] ** rho ** vec] /;
  And[Not @ FreeQ[vec, _Ket], FreeQ[rho, _Ket]]

Fidelity[rho_, vec_] := Chop @ Sqrt[Dagger[vec] ** rho ** vec] /;
  And[Not @ FreeQ[vec, _Ket], FreeQ[rho, _Ket]]

Fidelity[vec_, wec_] := Abs[Dagger[vec] ** wec] /;
  And[Not @ FreeQ[vec, _Ket], Not @ FreeQ[wec, _Ket]]
*)
(* NOTE: Not big benefits. *)


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


Protect[ Evaluate @ $symb ]

End[]

EndPackage[]
