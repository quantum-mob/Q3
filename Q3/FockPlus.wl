(* -*- mode:math -*- *)
BeginPackage[ "Q3`FockPlus`",
  { "Q3`Fock`", "Q3`Grassmann`", 
    "Q3`Pauli`", "Q3`Cauchy`", "Q3`" }
 ]

Q3Clear[];

Begin["`Private`"]
`Version = StringJoin[
  $Input, " v",
  StringSplit["$Revision: 1.11 $"][[2]], " (",
  StringSplit["$Date: 2021-03-08 02:31:34+09 $"][[2]], ") ",
  "Mahn-Soo Choi"
 ];
End[]

{ Pairings, Wick, Average };

{ FockSeries };

{ FockSum, FockSumThread, FockSumExpand, FockSumCollect };

{ FockSimplify, FockFullSimplify,
  FockSumSimplify, FockSumFullSimplify }


Begin["`Private`"]

$symbs = Unprotect[
  Multiply
 ]


Pairings::usage = "Pairings[list] generates all possible pairings of the elements in list."

Pairings[a : {_, _}] := {a}

Pairings[a_List] := Module[
  { pairs = Thread[{First @ a, Rest @ a}] },
  Catenate @ Map[iPairings[#, Supplement[a, #]]&, pairs]
 ] /; DuplicateFreeQ[a]

Pairings[a_List] := Module[
  {jj = Range@Length@a,
    pp},
  pp = Pairings[jj];
  Map[Part[a, #] &, pp, {3}]
 ] /; Not@DuplicateFreeQ[a]

iPairings[a : {_, _}, b : {_, _}] := {{a, b}}

iPairings[a : {_, _}, b_List] := Map[Join[{a}, #] &, Pairings[b]]


Average::usage = "Average[expr] represents the quantum mechanical expectation value of expr."


Wick::usage = "Wick[a, b, ...] applies the Wick theorem."

HoldPattern @ Wick[ Multiply[op__?AnyBosonQ] ] := Wick[op]

Wick[op__?AnyBosonQ] := 0 /; OddQ[Length@{op}]

Wick[a_?AnyBosonQ, b_?AnyBosonQ] := Average[a**b]

Wick[a_?AnyBosonQ, b_?AnyBosonQ, op__?AnyBosonQ] := Module[
  { pp = Pairings@{a, b, op} },
  Total[ Times @@@ Apply[ Composition[Average, Multiply], pp, {2} ] ]
 ] /; EvenQ[Length@{a, b, op}]

Wick[expr_] := expr /. {
  HoldPattern[ Multiply[op__?AnyBosonQ] ] :> Wick[op]
 }


FockSeries::usage = "FockSeries[f, arg, n] expands function f into a series of order n around 0. The argument of the expansion is arg and its powers are computed using FockPower.  The result is returned in terms of powers of arg."

FockSeries[f_, expr_, n_:5] := Module[
  { s, x },
  s = Normal @ Series[f[x], {x, 0, n}];
  s /. { x^pw_. -> FockPower[expr, pw] }
 ]

FockSeries[f_[expr_], n_:5] := FockSeries[f, expr, n]

FockSeries[E^expr_, n_:5] := FockSeries[Exp, expr, n]


FockSum::usage = "FockSum[expr, {indexes}] denotes a symbolic sum of anexpression over indexes.  For example, FockSum[Dagger[a[j]], {j}] denotes a sum of a[j] over all possible values of j."

(* No sum at all *)
FockSum[z_, {}] := z

(* The indexes must be sorted for the simplifications to work correctly *)
FockSum[z_, ls_List] := FockSum[z, Sort[ls]] /; Not @ OrderedQ @ ls

(* It's always safe to extract a number *)
FockSum[z_ a_, ls_List] /; ComplexQ[z] := z FockSum[a, ls]

FockSum[z_ a_, ls_List] /; flavorFreeQ[z, ls] := z FockSum[a, ls]

FockSum[z_, ls_List] := z FockSum[1, ls] /;
  And[ flavorFreeQ[z, ls], z != 1 ]

(* Conjugation *)
FockSum /:
Dagger[ FockSum[z_, jj_List] ] := FockSum[Dagger[z], jj]

(* Multiple sums *)
FockSum[ FockSum[a_, ls1_List], ls2_List ] :=
  FockSum[a, exclusiveJoin[ls1, ls2]]
(* In nested sums, the same dummy index cannot appear at different levels. *)

(* Returns True if expr contains none of symbols in list ls *)
flavorFreeQ[expr_, ls_List] := And @@ Map[FreeQ[expr, #]&, ls]

(* Join two Lists. Send a message if the indexes overlap. *)
exclusiveJoin[l1_List, l2_List] := Module[
  {l},
  l = Sort @ Join[l1, l2];
  If[l =!= Union[l], Message[exclusiveJoin::overlap, l1, l2] ];
  l
 ]

exclusiveJoin::overlap = "Overlapping indexes detected when joining
`` and ``."

(* Product of sums *)

(* Summation indices are merely dummy indices.  The same name for indices
   appearing in different sums within a product of sums has no meaning.
   Therefore, when combined into a single sum, the repeated names should be
   renamed.  The new name is formed by taking the symbol name that occurs
   twice and appending a number. The number is chosen such that the new name
   does not conflict with other index names. *)

(* In the special case for the commutators [a,b]=ab-ba where a and b are both
   sums, renaming is performed for the second argument (b) in both
   products. Typically, the resulting expressions can be simplified to a
   greater extent in this approach. *)

HoldPattern @ Multiply[ FockSum[a1_, j1_List], FockSum[a2_, j2_List] ] :=
  renameDuplicateIndices[a1, a2, j1, j2]

Unprotect[Commutator]

Commutator[ FockSum[a1_, ls1_List], FockSum[a2_, ls2_List] ] := 
  renameDuplicateIndices[a1, a2, ls1, ls2, False] -
  renameDuplicateIndices[a1, a2, ls1, ls2, True]

Protect[Commutator]

(* Rename duplicate indices (if any) appearing in the FockSum. *)
renameDuplicateIndices[a1_, a2_, ls1_List, ls2_List, reverse_:False] := 
  Module[
    {u, rule, dups},
    u = Union[ls1, ls2];
    (* duplicate names from the second index list *)
    dups = Select[ Common[ls2, ls1], Not[FreeQ[a1,#]]& ];
    (* rename the duplicate indices *)
    rule = {};
    Scan[
      ( nn = uniqueIndex[#, u, a1];
        AppendTo[u, nn];
        AppendTo[rule, # -> nn] )&,
      dups ];
    If[ reverse,
      FockSum[Multiply[a2 /. rule, a1], Sort @ u],
      FockSum[Multiply[a1, a2 /. rule], Sort @ u]
     ]
   ]

(* Returns a new symbol name for the dummy index formed by taking the symbol
   name n and appending a number. The number is chosen such that the new name
   does not yet appear in the list NAMES nor the expression EXPR. *)

uniqueIndex[n_, names_List, expr_:1] := Module[
  {ns, i, nn},
  ns = trimTrailingDigits @ ToString[n];
  For[i = 1, True, i++, 
    nn = ToExpression[ ns <> ToString[i] ];
    If[FreeQ[names, nn] && FreeQ[expr, nn], Break[]];
   ];
  Let[Flavors, nn]; (* Not implemented yet *)
  nn
 ]

(* Returns back the string str after removing the final digits *)
trimTrailingDigits[str_String] := StringReplace[
  str,
  Shortest[x : (_ ~~ ___)] ~~ DigitCharacter.. ~~ EndOfString :> x
 ]

(* Returns back the symbol name symbol after removing the final digits.
   Mathematica 6 or later required *)
trimTrailingDigits[var_Symbol] := 
  ToExpression @ trimTrailingDigits @ SymbolName[var]

FockSumThread::usage = "FockSumThread threads FockSum[{expr1, expr2}, {indexes}] over the list in the first argument."

FockSumThread[expr_] := expr //. rulesFockSumThread

rulesFockSumThread = {
  FockSum[z_List, ls_List] :> Map[FockSum[#, ls]&, z]
 }

FockSumExpand::usage = "FockSumExpand[expr] expands sums over the addends."

FockSumExpand[expr_] := expr //. rulesFockSumExpand

rulesFockSumExpand = { 
  FockSum[a_ + b_, ls_List] :> FockSum[a, ls] + FockSum[b, ls],
  FockSum[a_, ls_List] :> FockSum[ExpandAll[a], ls]
 }

FockSumCollect::usage = "FockSumCollect[expr] collects sums over the addends."

FockSumCollect[expr_] := expr //. rulesFockSumCollect

rulesFockSumCollect = { 
  Plus[z1_. FockSum[a1_, ls_List], z2_. FockSum[a2_, ls_List]] :>
    FockSum[z1 a1+z2 a2, ls],
  
  Plus[z1_. FockSum[a1_, ls1_List], z2_. FockSum[a2_, ls2_List]] /; 
    Intersection[ls1, ls2] =!= {} :>
    Module[
      {int},
      int = Intersection[ls1, ls2];
      FockSum[FockSum[z1 a1, Complement[ls1, int]]
        +FockSum[z2 a2, Complement[ls2, int]], int]
     ],

  HoldPattern @ Multiply[a___, FockSum[b_,ls_List], c___] :>
    FockSum[Multiply[a, b, c], ls]
 }

(* Vacuum expectation *)

HoldPattern @ Multiply[Dagger[VacuumState], FockSum[ops_, ls_List], VacuumState] :=
  FockSum[ VacuumExpectation[ops], ls ]

VacuumExpectationWick[FockSum[ops_, ls_List]] :=
  FockSum[ VacuumExpectationWick[ops], ls ]


FockSimplify::usage = "FockSimplify[expr] attempts to rewrite an expression in terms of higher level Fock functions.  It works well for simle expressions."

FockSimplify[expr_] := Module[
  {x},
  x = funcSimplifyNumber[expr];
  x = funcSimplifySpin[x];
  Return[x]
 ]

FockFullSimplify::usage = "Like the built-in function FullSimplify[]."

FockFullSimplify[expr_] := Simplify[
  expr,
  TransformationFunctions ->
    { Automatic,
      funcSimplifyNumber,
      funcSimplifySpin,
      FockSimplify }
 ]


funcSimplifyBasic[expr_] := Simplify[
  expr,
  TransformationFunctions -> 
    {Automatic, Function[x, x //. rulesSimplifyBasic]}
 ]

rulesSimplifyBasic = {
  UnitStep[k_]+UnitStep[-k_] -> 1,
  1 - UnitStep[-k_] ->  UnitStep[k],
  UnitStep[-k_] - 1 -> -UnitStep[k]
 }

funcSimplifyNumber[expr_] := Simplify[
  expr,
  TransformationFunctions ->
    {Automatic, Function[x, x //. rulesSimplifyNumber]}
 ]

rulesSimplifyNumber := {
  HoldPattern @ Multiply[Dagger[op_[j___,s_]], op_[j___,s_]] :> 
    HoldForm[ FockNumber[op[j,s]] ] /; OperatorQ[op] && spinfulQ[op],
  Expand[
    z_. (HoldForm[FockNumber[c_[j___,up]]] +
        HoldForm[FockNumber[c_[j___,down]]]) ] :>
    z HoldForm[ FockNumber[c[j,All]] ]
 }

funcSimplifySpin[expr_] := Simplify[
  expr,
  TransformationFunctions -> 
    {Automatic, Function[x, x //. rulesSimplifySpin]}
 ]

rulesSimplifySpin := Block[
  {op1, op2, rule1, rule2, rule3, l1, l2, ir1, ir2, i1, i2},
  Let[Fermion, op1, op2, Spin->1/2]; (* hence specific to Spin 1/2 *)
  l1 = {
    HoldForm @ FockSpin[op1[i1],1], 
    HoldForm @ FockSpin[op1[i1],2], 
    HoldForm @ FockSpin[op1[i1],3]
   };
  l2 = {
    HoldForm @ FockSpin[op2[i2],1],
    HoldForm @ FockSpin[op2[i2],2], 
    HoldForm @ FockSpin[op2[i2],3]
   };
  ir1 = {op1 -> a_?OperatorQ, op2 -> b_?OperatorQ};
  ir2 = {op1 -> a, op2 -> b};
  
  (* Rules for a single spin operator *)
  
  rule1  = Thread[(FockSpin[op1[i1___]] /. ir1) -> (l1 /. ir2)];
  rule1a = Thread[(Expand[FockSpin[op1[i1___]]] /. ir1) -> (l1 /. ir2)];
  rule1b = Thread[(Expand[2 FockSpin[op1[i1___]]] /. ir1) -> (2l1 /. ir2)];
  rule1c = Thread[(Expand[I FockSpin[op1[i1___]]] /. ir1) -> (I l1 /. ir2)];
  rule1d = Thread[(Expand[2I FockSpin[op1[i1___]]] /. ir1) -> (2I l1 /. ir2)];
  rule1e = Thread[(Simplify[2I FockSpin[op1[i1___]]] /. ir1) -> (2I l1 /. ir2)];
  rule1f = Thread[(Simplify[-2I FockSpin[op1[i1___]]] /.
        ir1) -> (-2I l1 /. ir2)];
  
  (* Rules for products of spin operators *)
  
  rule2 = Thread[
    Flatten[Expand[
        4Outer[Multiply, FockSpin[op1[i1___]], FockSpin[op2[i2___]]]] /. 
        ir1, 1] ->      
      Flatten[Expand[4Outer[Multiply, l1, l2]] /. ir2, 1]]; 

  rule2b = Thread[
    Flatten[Expand[
        Outer[Multiply, FockSpin[op1[i1___]], FockSpin[op2[i2___]]]] /. 
        ir1, 1] ->      
      Flatten[Expand[Outer[Multiply, l1, l2]] /. ir2, 1]];
  
  (* Some symmetrized combinations of spin - spin products *)
  rule2a = {
    (* xx + yy *)
    Rule @@ (rule2[[1]] + rule2[[5]] /. 
        HoldPattern[i_ -> j_] :> Expand[-1/2{z_. i, z j}]),
    (* xy + yx *)
    Rule @@ (rule2[[2]] + rule2[[4]] /. 
        HoldPattern[i_ -> j_] :> Expand[I/2{z_. i, z j}]),
    (* xz + zx *)
    Rule @@ (rule2[[3]] + rule2[[7]] /. 
        HoldPattern[i_ -> j_] :> Expand[{z_. i, z j}]),
    (* yz + zy *)
    Rule @@ (rule2[[6]] + rule2[[8]] /. 
        HoldPattern[i_ -> j_] :> Expand[-I{z_. i, z j}])
   };
  
  (* Rules for combining the components of spin operator pairs *)
  rule3 = {Expand[z_. HardDot[l1, l2] /. 
        Join[ir1, {i1 -> i1___, i2 -> i2___}]] ->
      (z HoldForm[FockSpinSpin[op1[i1], op2[i2]]] /. ir2)};
  
  Join[rule3, 
    rule1, rule1a, rule1b, rule1c, rule1d, rule1e, rule1f, 
    rule2, rule2b, rule2a]
 ]


(*** Simplifications Involving FockSum ***)

FockSumSimplify::usage = "FockSumSimplify[expr] attempts to simplify the expression expr involving FockSum. It is better to apply individual simplification rules separately, since the rules in each block can have conflicting effects as regards the complexity of the expression that is being simplified."

FockSumFullSimplify::usage = "FockSumFullSimplify[expr] attempts to simplify an expression involving symbolic sums. It first calls funcSumFullSimplifyClassic, then applies additional rules to furher simplify the resulting expression."

FockSumSimplify[expr_] := Simplify[
  expr, 
  TransformationFunctions -> doFockSumSimplify
 ]

doFockSumSimplify := Join[
  { Automatic,
    funcSimplifyBasic,
    funcSumSimplify1,
    funcSumSimplify2,
    funcSumSimplify3,
    funcSumSimplify4 },
  Sequence @@ Map[
    fRulesToFunctions, 
    { rulesFockSumExpand,
      rulesFockSumCollect,
      rulesSumSimplifyBasic}
   ]
 ]

FockSumFullSimplify[expr_] := FullSimplify[
  expr, 
  TransformationFunctions ->
    Prepend[doFockSumSimplify, funcSumFullSimplifyClassic]
 ]

(* Transform a list of rules to a list of functions that apply these rules.
   Such functions can be used as transformation functions in Simplify. *)
fRulesToFunctions[rules_List] := Map[Function[expr, expr //. #] &, rules]

funcSumSimplify1[expr_] := Module[
  {ex},
  ex = Expand[expr];
  ex = FockSumExpand[ex];
  ex = Simplify[ex];
  ex = FockSumCollect[ex]
 ]

funcSumSimplify2[expr_] := Module[
  {ex},
  ex = FockSumExpand[expr];
  ex = Simplify[ex];
  ex = FockSumCollect[ex]
 ]

funcSumSimplify3[expr_] := Module[
  {ex},
  ex = funcSumSimplifyBasic[expr];
  ex = funcSimplifyBasic[ex]
 ]

funcSumSimplify4[expr_] := Module[
  {ex},
  ex = FockSumCollect[expr];
  ex = Simplify[ex];
  ex = funcSumSimplifyBasic[ex]
 ]

(* Tries to simplify sums, in particular, by handling KroneckerDelta
   functions. *)

funcSumSimplifyBasic[expr_] := expr //. rulesSumSimplifyBasic

rulesSumSimplifyBasic = {
  FockSum[KroneckerDelta[n1_, n2_] a_., ls_List] /; MemberQ[ls, n1] :>
    FockSum[a //. {n1 -> n2}, Complement[ls, {n1}]],
  
  FockSum[KroneckerDelta[n1_, n2_] a_., ls_List] /; MemberQ[ls, n2] :>
    FockSum[a //. {n2 -> n1}, Complement[ls, {n2}]],
  
  HoldPattern[FockSum[a1_ + a2_, x:{i___, n1_, n2_, j___}]] /;
    (FreeQ[a1, n2] && FreeQ[a2, n1]) :>
    FockSum[1, {n2}] FockSum[a1, {i, n1, j}] +
    FockSum[1, {n1}] FockSum[a2, {i, n2, j}],
  
  HoldPattern[FockSum[a_ b_., {i___, n1_, j___}]] /; 
    (FreeQ[a, n1] && flavorFreeQ[b, {i, j}]) :>
    FockSum[a, {i, j}] FockSum[b, {n1}],

  HoldPattern[FockSum[a_ (b_ + c_), x:{i___, n1_, j___}]] /; 
    (FreeQ[a, n1] && flavorFreeQ[b, {i, j}]) :>
    FockSum[a c, x] + FockSum[a, {i, j}] FockSum[b, {n1}] 
 }

(* Tries to simplify an expression involving symbolic summations. The
   heuristic approach used turns out to work very well in practice. *)

funcSumFullSimplifyClassic[expr_] := Module[
  {ex},
  ex = Expand[expr];
  ex = sumCollect[ex];
  ex = Simplify[ex];
  ex = sumSimplifyKD[ex];
  ex = SimplifyKD[ex];
  ex = Simplify[ex];

  (* We must also expand within sum[] *)
  ex = sumExpand[ex];
  ex = Simplify[ex];
  ex = sumSimplify[ex];
  ex = Simplify[ex];

  (* and then collect again *)
  ex = sumCollect[ex];
  ex = Simplify[ex]
]

Protect[ Evaluate @ $symbs ]

End[]

Q3Protect[]

EndPackage[]
