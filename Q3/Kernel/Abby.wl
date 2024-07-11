(* -*- mode:math -*- *)
BeginPackage["Q3`"]

{ Supplement, SupplementBy, Common, CommonBy, SignatureTo };
{ Pairings, Unpaired };
{ Choices, ListPartitions, Successive, FirstLast, Inbetween };
{ ShiftLeft, ShiftRight,
  TrimLeft, TrimRight };
{ KeyGroupBy, KeyReplace, CheckJoin };
{ ReplaceRules, ReplaceRulesBy };
{ PseudoDivide, ZeroQ };
{ CountsFor };
{ IntegerParity, IntegerPowerQ };
{ RandomPick };
{ IntervalSize };

{ Unless };

{ Chain, ChainBy };
{ GraphLocalComplement, GraphPivot, GraphNeighborhoodSans };
{ Bead, GreatCircle };

{ MapThrough };

{ ApplyThrough,
  ChopThrough, SimplifyThrough, FullSimplifyThrough,
  ReplaceAllThrough };

{ LeftBrace, RightBrace, OverBrace, UnderBrace };

{ BinaryToGray, GrayToBinary,
  GrayToInteger, IntegerToGray,
  BitReflect,
  GraySequence, GraySubsets };

{ Primed, DoublePrimed };

{ MatrixObject };

{ LevelsPlot };
{ PanedText };


Begin["`Private`"]

(**** <Pairings> ****)

Unpaired::usage = "Unpaired[a] represents an unpaired element a."

Pairings::usage = "Pairings[list] generates all possible pairings of the elements in list.\nSee also ListPartitions and the built-in function Groupings."

Pairings::odd = "There are an odd number of elements in ``."

Pairings[a_List] := (
  Message[Pairings::odd, a]; 
  Pairings[Append[a, "__None__"]] /. 
    {{any_, "__None__"} -> Unpaired[any]} /.
    {{pre___, any_Unpaired, post___} -> {pre, post, any}}
) /; OddQ @ Length[a]

Pairings[a:{_, _}] := {a}

Pairings[a_List] := Module[
  { pp = Thread[{First @ a, Rest @ a}] },
  Catenate @ Map[pushPair[#, Supplement[a, #]]&, pp]
] /; DuplicateFreeQ[a]

Pairings[a_List] := Module[
  { jj = Range @ Length @ a,
    pp },
  pp = Pairings[jj];
  Map[Part[a, #]&, pp, {3}]
] /; Not @ DuplicateFreeQ[a]

pushPair[a:{_, _}, b:{_, _}] := {{a, b}}

pushPair[a:{_, _}, b_List] := Map[Join[{a}, #]&, Pairings[b]]

(**** </Pairings> ****)


Choices::usage = "Choices[list] gives a list of all possible choices of varying numbers of elements from list.\nChoices[list, n] gives all possible choices of at most n elements.\nChoices[list, {n}] gives the choices of exactly n elements.\nChoices[list, {m, n}] gives all possible choices containing between m and n elements.\nUnlike Subsets, it allows to choose duplicate elements.\nSee also: Subsets, Tuples."

Choices[a_List] := Choices[a, {0, Length @ a}]

Choices[a_List, n_Integer] := Choices[a, {0, n}]

Choices[a_List, {m_Integer, n_Integer}] :=
  Catenate @ Table[Choices[a, {j}], {j, m, n}]

Choices[a_List, {n_Integer}] := Union[Sort /@ Tuples[a, n]]


ListPartitions::usage = "ListPartitions[list] gives a list of all possible ways to partition 'list' into smaller lists.\nListPartitions[list, spec] gives partitions corresponding to the specification spec. For spec, see IntegerPartitions."

ListPartitions[data_List, spec___] := Module[
  { parts = IntegerPartitions[Length @ data, spec] },
  parts = Flatten[Permutations /@ parts, 1];
  TakeList[data, #]& /@ parts
]
(* NOTE: Permutations /@ parts is necessary to find all possible
   decompositions of the integer Length[list]. *)


Supplement::usage = "Supplement[a, b, c, \[Ellipsis]] returns the elements in a that are not in any of b, c, \[Ellipsis]. It is similar to the builtin Complement, but unlike Complement, treats a as a List (not Mathematical set). That is, the order is preserved.\nMathematica 13.1 introduced an experimental function DeleteElements with the same feature."

Supplement[a_List, b__List] := DeleteCases[ a, Alternatives @@ Union[b], 1 ]
(* Implementation 3: Fast and versatile. *)

(* Supplement[a_List, b__List] := a /. Thread[Union[b] -> Nothing] *)

(* Implementation 2: Faster than the obvious approach as in Implementation 1
   below.  However, it works only when a and b are simple arrays (not allowed
   to include sublists, in which case unexpected results will arise). *)

(* Supplement[a_List, b_List] := Select[a, ! MemberQ[b, #] &] *)
(* Implementation 1: Straightforward, but slow. *)


SupplementBy::usage = "SupplementBy[a, b, c, \[Ellipsis], f] returns the elements in a that do not appear in any of sets on b, c, \[Ellipsis] with all the tests made after applying f on a, b, c, \[Ellipsis] .\nLike Supplement, the order is preserved."

SupplementBy[a_List, b__List, f_] := Module[
  { aa = f /@ a,
    form = Alternatives @@ Map[f, Union[b]] },
  aa = Map[Not @ MatchQ[#, form]&, aa];
  Pick[a, aa]
 ]

Common::usage = "Common[a, b, c, \[Ellipsis]] returns the elements of a that appear in all subsequent lists.\nIt is similar to the built-in function Intersection, but treats the first argument as a List (not mathematical sets) and hence preserves the order."

Common[a_List, b__List] := Cases[ a, Alternatives @@ Intersection[b], 1 ]
(* Implementation 3: Fast and versatile. *)

(* Common[a_List, b_List] := Select[a, MemberQ[b,#]& ] *)
(* Implementation 1: Straightforward, but slow. *)

CommonBy::usage = "CommonBy[a, b, c, \[Ellipsis], func] returns the elements of a that appear in all of b, c, \[Ellipsis] with all the tests made after applying func.\nLike Common, the order is preserved."
  
CommonBy[a_List, b__List, func_] := Module[
  { aa = func /@ a,
    ff },
  ff = Alternatives @@ Intersection @@ Map[func, {b}, {2}];
  aa = Map[MatchQ[#, ff]&, aa];
  Pick[a, aa]
 ]

SignatureTo::usage = "SignatureTo[a, b] returns the signature of the permutation that converts the list a to b, where the two lists are assumed to differ only in the order of their elements."
SignatureTo[a_, b_] := 
  Signature @ PermutationList @ FindPermutation[a, b] /;
  Length[a] == Length[b]


Successive::usage = "Successive[f, {x1,x2,x3,\[Ellipsis]}] returns {f[x1,x2], f[x2,x3], \[Ellipsis]}.\nSuccessive[f, list, n] applies f on n successive elements of list.\nSuccessive[f, list, 2] is equivalent to Successive[f,list].\nSuccessive[f, list, 1] is equivalent to Map[f, list].\nSuccessive[f, list, n, d] applies f on n succesive elements and jumps d elements to repeat."

Successive[f_, a_List] := f @@@ Transpose @ {Most @ a, Rest @ a}

Successive[f_, a_List, n_Integer?Positive] := f @@@ Drop[
  Transpose@NestList[RotateLeft, a, n-1],
  1-n
 ]

Successive[f_, a_List, n_Integer?Positive, d_Integer?Positive] :=
  f @@@ Part[
    Drop[Transpose@NestList[RotateLeft, a, n-1], 1-n],
    Span[1, All, d]
   ]


FirstLast::usage = "FirstLast[expr] returns the first and last elements of expr."

FirstLast[expr_] := {First[expr], Last[expr]}


Inbetween::usage = "Inbetween[expr] returns expr with the first and last elements removed."

Inbetween[expr_] := Rest @ Most @ expr


ShiftLeft::usage = "ShiftLeft[list, n] shifts the elements in list by n positions to the left and pad n 0s on the right.\nSimilar to RotateLeft, but does not cycle the elements.\nIf n is omitted, it is assumed to be 1."

ShiftLeft[a_List, n_Integer, x_:0] := PadRight[Drop[a,n], Length[a], x] /; n>0

ShiftLeft[a_List, n_Integer, x_:0] := PadLeft[Drop[a,n], Length[a], x] /; n<0

ShiftLeft[a_List, 0, x_:0] := a

ShiftLeft[a_List] := ShiftLeft[a, 1, 0]


ShiftRight::usage = "ShiftRight[list, n] shifts the elements in list by n positions to the right and pad n 0s on the left.\nSimilar to RotateRight, but does not cycle the elements.\nIf n is omitted, it is assumed to be 1."

ShiftRight[a_List, n_Integer, x_:0] := PadLeft[Drop[a,-n], Length[a], x] /; n>0

ShiftRight[a_List, n_Integer, x_:0] := PadRight[Drop[a,-n], Length[a], x] /; n<0

ShiftRight[a_List, 0, x_:0] := a

ShiftRight[a_List] := ShiftRight[a, 1, 0]


TrimLeft::usage = "TrimLeft[list] returns a list by trimming 0 from the left.\nTrimLeft[list, n] prevents the list from getting shorter than n."

TrimLeft[a_?VectorQ, n_Integer : 0] := Module[
  { new = a },
  While[Length[new] > n && ZeroQ[First@new], new = Rest[new]];
  new
]


TrimRight::usage = "TrimRight[list] returns a list by trimming 0 from the right.\nTrimRight[list, n] prevents the list from getting shorter than n."

TrimRight[a_?VectorQ, n_Integer : 0] := Module[
  { new = a },
  While[ZeroQ[Length[new] > n && Last@new], new = Most[new]];
  new
]


(**** <KeyGroupBy> ****)

KeyGroupBy::usage = "KeyGroupBy[assoc, f] gives an Association that groups key$j->value$j into different Associations associated with distinct keys f[key$j].\nKeyGroupBy[assoc, f->g] groups key$j->g[value$j] according to f[key$j].\nKeyGroupBy[assoc, f->g, post] applies function post to Associations that are generated.\nKeyGroupBy[assoc, f, post] is equivalent to KeyGroupBy[assoc, f->Indeity, post]."

KeyGroupBy[assoc_Association, f_] := 
  KeyGroupBy[assoc, f -> Identity, Identity]

KeyGroupBy[assoc_Association, f_ -> g_] := 
  KeyGroupBy[assoc, f -> g, Identity]

KeyGroupBy[assoc_Association, f_, post_] := 
  KeyGroupBy[assoc, f -> Identity, post]

KeyGroupBy[assoc_Association, f_ -> g_, post_] := Merge[
  KeyValueMap[(f[#1] -> Rule[#1, g[#2]])&, assoc],
  post @* Association
]

(**** </KeyGroupBy> ****)


(**** <KeyReplace> ****)

KeyReplace::usage = "KeyReplace[assoc, {key1 -> new1, key2 -> new2, ...}] replace key1 with new1, key2 with new2, ... in association assoc.\nKeyReplace[{key1 -> val1, key2 -> val2, ...}, {key1 -> new1, key2 -> new2, ...}] is similar but returns a list rather than an association."

KeyReplace[any_, rr:(_Rule|_RuleDelayed)] :=
  KeyReplace[any, {rr}]

KeyReplace[aa_Association, kk:{(_Rule|_RuleDelayed)...}] :=
  AssociationThread[Keys[aa] /. kk, Values @ aa]

KeyReplace[aa:{___Rule}, kk:{(_Rule|_RuleDelayed)...}] :=
  Thread @ Rule[Keys[aa] /. kk, Values @ aa]

(**** </KeyReplace> ****)


(**** <ReplaceRules> ****)

ReplaceRules::usage = "ReplaceRules[{key1 -> val1, key2 -> val2, \[Ellipsis]}, key -> val] replaces the value corresponding to key by val.\nSee also FilterRules."

ReplaceRules[opts_List?OptionQ, key_ -> val_] :=
 Reverse @ Normal @ ReplacePart[Association @ Reverse @ Flatten @ opts, Key[key] -> val]

ReplaceRules[head_[args___, opts___?OptionQ], key_ -> val_] :=
  With[
    { new = ReplaceRules[{opts}, key -> val] },
    If[ new == {},
      head[args, opts],
      head[args, new, opts]
    ]
  ]


ReplaceRulesBy::usage = "ReplaceRulesBy[{key1 -> val1, key2 -> val2, \[Ellipsis]}, key -> func] replaces the value corresponding to key by func[val].\nSee also FilterRules."

ReplaceRulesBy[opts_List?OptionQ, key_ -> fun_] := With[
  { new = Association @ Flatten @ opts },
  Reverse @ Normal @ ReplacePart[
    Association @ Reverse @ Flatten @ opts, 
    Key[key] :> fun @ Lookup[new, key]
  ]
]

ReplaceRulesBy[head_[args___, opts___?OptionQ], key_ -> fun_] :=
  With[
    { new = ReplaceRulesBy[{opts}, key -> fun] },
    If[ new == {},
      head[args, opts],
      head[args, new, opts]
    ]
  ]

(**** </ReplaceRules> ****)


(**** <CheckJoin> ****)

CheckJoin::usage = "CheckJoin[assc1,assc2,\[Ellipsis]] checks whether any key appears multiple times before joining associations assc1, assc2, \[Ellipsis]."

CheckJoin::dupl = "Duplicate keys in ``; keeping the first value for each of the duplicate keys."

CheckJoin[aa__Association] := Merge[ {aa},
  (If[Length[#] > 1, Message[CheckJoin::dupl, {aa}]]; First[#])& ]

(**** </CheckJoin> ****)


Unless::usage = "Unless[condition, result] gives result unless condition evaluates to True, and Null otherwise."

Unless::retrn = "`` includes Return, which may not function as you expect. See the help documentation on Unless."

SetAttributes[Unless, HoldRest]

Unless[condition_, out_] := (
  Message[Unless::retrn, Hold @ out];
  If[Not[condition], out];
 ) /; Not @ FreeQ[Hold[out], _Return]
(* NOTE: There is an important different between Unless[test, expr] and
   If[Not[test], expr] when expr includes Return[...]. See the documentation
   on Unless. *)

Unless[condition_, out_] := If[Not[condition], out]


PseudoDivide::usage = "PseudoDivide[x, y] returns x times the PseudoInverse of y."

SetAttributes[PseudoDivide, Listable]

PseudoDivide[x_, 0] = 0

PseudoDivide[x_, 0.] = 0.

PseudoDivide[x_, 0. + 0. I] = 0. + 0. I

PseudoDivide[x_, y_] := x/y


(**** <ZeroQ> ****)

ZeroQ::usage = "ZeroQ[x] returns True if x approximately equals to zero.\nZeroQ[x, \[Delta]] returns True if |x| \[LessEqual] \[Delta]."

ZeroQ::tolnn = "Tolerence specification `` must be a non-negative number."

ZeroQ[x_] := TrueQ[Chop[x] == 0]

ZeroQ[x_, del_?NonNegative] := TrueQ[Chop[x, del] == 0]

ZeroQ[x_, del_] := (
  Message[ZeroQ::tolnn, del];
  ZeroQ[x, Abs @ del]
)

(**** </ZeroQ> ****)


(**** <CountsFor> ****)

CountsFor::usage = "CountsFor[list, {k1,k2,\[Ellipsis]}] gives an association whose keys are k1, k2, \[Ellipsis], and whose values are the number of times those keys appear in list.\nCountsFor[{k1,k2,\[Ellipsis]}] represents the operator form of CountsFor that can be applied to a list.\nCounts is almost the same as Counts, but keys are specified explicitly."

CountsFor[var_List][obj_List] := CountsFor[obj, var]

CountsFor[obj_List, var_List] := 
 Join[AssociationThread[var -> 0], Counts @ obj]

(**** </CountsFor> ****)


(**** <IntegerParity> ****)

IntegerParity::usage = "IntegerParity[n] returns 1 if n is an even integer and -1 if n is odd."

SetAttributes[IntegerParity, Listable]

IntegerParity[n_Integer] := 1 - 2*Mod[n, 2]

(**** </IntegerParity> ****)


(**** <IntegerPowerQ> ****)

IntegerPowerQ::usage = "IntegerPowerQ[b, n] returns True if n is an integer power of b.\nIntegerPower[n] is equivalent to IntegerPower[10, n]."

SetAttributes[IntegerPowerQ, Listable]

IntegerPowerQ[n_Integer] := IntegerQ[Log[10, n]]

IntegerPowerQ[b_Integer, n_Integer] := IntegerQ[Log[b, n]]
(* NOTE: This is 3 times faster than using IntegerQ[Log2[n]], and is twice faster than using DigitCount[n,b,1]==1. *)

IntegerPowerQ[_, _] = False

(**** </IntegerPowerQ> ****)


(**** <RandomPick> ****)

RandomPick::usage = "RandomPick[{e1, e2, \[Ellipsis]}, p] picks each element ek with probability p and returns the list of picked elements.\nRandomPick[{e1, e2, \[Ellipsis]}, p, n] repeats n times and returns the collected elements."

RandomPick[list_List, p_?NumericQ, n_Integer] :=
  Table[RandomPick[list, p], n]

RandomPick[list_List, p_?NumericQ] :=
  Pick[list, Thread[RandomReal[{0, 1}, Length @ list] < p]]

(**** </RandomPick> ****)


(**** <IntervalSize> ****)

IntervalSize::usage = "IntervalSize[interval] returns the total size of interval."

IntervalSize[int_Interval] := -Total @ MapApply[Subtract, List @@ int]

(**** </IntervalSize> ****)


(**** <Chain> ****)

Chain::usage = "Chain[a, b, \[Ellipsis]] constructs a chain of links connecting a, b, \[Ellipsis] consecutively."

Chain[] = {}

Chain[a:Except[_List]] = {}

Chain[a:Except[_List], b:Except[_List]] := {Rule[a, b]}

Chain[m_List] := 
  Flatten[Chain /@ Transpose[m]] /; ArrayQ[m, Except[1]]

Chain[m_List, b_] := Flatten @ { Chain@m, Chain[Last@m, b] } /;
  ArrayQ[m, Except[1]]

Chain[m_?VectorQ, b_] := Flatten @ Map[Chain[#, b]&, m]

Chain[a_, m_List] := Flatten @ { Chain[a, First@m], Chain@m } /;
  ArrayQ[m, Except[1]]

Chain[a_, m_?VectorQ] := Map[Chain[a, #] &, m]

Chain[a__, m_List, b__] :=
  Flatten @ { Chain[a, First@m], Chain@m, Chain[Last@m, b] } /;
  ArrayQ[m, Except[1]]

Chain[a_, b_, c__] := Flatten @ { Chain[a, b], Chain[b, c] }

Chain[aa_List] := Chain @@ aa


ChainBy::usage = "ChainBy[a, b, \[Ellipsis], func] constructs a chain of links connecting a, b, \[Ellipsis] consecutively with each link created by means of func."

ChainBy[args___, func_] := func @@@ Chain[args]

(**** </Chain> ****)


GraphLocalComplement::usage = "GraphLocalComplement[g, v] gives the local complement of graph g according to vertex g.\nThe local complement of a graph g according to vertex v, denoted by g*v, is a graph that has the same vertices as g, but all the neighbors of of v are connected if and only if they are not connected in g."

GraphLocalComplement[g_Graph, v_, opts___?OptionQ] := Module[
  { nbr = GraphNeighborhoodSans[g, v],
    new },
  new = GraphUnion[GraphDifference[g, nbr], GraphComplement @ nbr];
  Graph[ VertexList @ new, EdgeList @ new, opts,
    VertexCoordinates -> Thread[VertexList[g] -> GraphEmbedding[g]] ]
 ]


GraphNeighborhoodSans::usage = "GraphNeighborhoodSans[g, v] returns the graph neighborhood of vertex v in graph g excluding v and edges connecting it."

GraphNeighborhoodSans[g_Graph, v_] := With[
  { nbr = NeighborhoodGraph[g, v] },
  Graph[
    DeleteCases[VertexList @ nbr, v],
    Complement[
      EdgeList @ nbr,
      EdgeList[ nbr,
        UndirectedEdge[v, _] | DirectedEdge[v, _] | DirectedEdge[_, v] ]
     ]
   ]
 ]


GraphPivot::usage = "GraphPivot[g, {v, w}] returns the graph pivot of graph g along the edge connecting vertices v and w.\nThe graph pivot of g along the edge between v and w is the graph g*v*w*v."

GraphPivot[g_, {v_, w_}, opts___?OptionQ] := Module[
  { new = Fold[GraphLocalComplement, g, {v, w, v}],
    cc = AssociationThread[VertexList[g] -> GraphEmbedding[g]] },
  {cc[v], cc[w]} = {cc[w], cc[v]};
  Graph[ VertexList @ new, EdgeList @ new, opts,
    VertexCoordinates -> cc ]
]


Bead::usage = "Bead[pt] or Bead[{pt1, pt2, \[Ellipsis]}] is a shortcut to render bead-like small spheres of a small scaled radius Scaled[0.01]. It has been motivated by Tube.\nBead[pt] is equvalent to Sphere[pt, Scaled[0.01]].\nBead[{p1, p2, \[Ellipsis]}] is equivalent to Sphere[{p1, p2, \[Ellipsis]}, Scaled[0.01]].\nBead[spec, r] is equivalent to Sphere[spec, r]."

Bead[pnt:{_, _, _}, r_:Scaled[0.01]] := Sphere[pnt, r]

(*
Bead[pnt:{_?NumericQ, _?NumericQ, _?NumericQ}, r_:Scaled[0.01]] :=
  Sphere[pnt, r]
 *)

Bead[pnt:{{_?NumericQ, _?NumericQ, _?NumericQ}..}, r_:Scaled[0.01]] :=
  Sphere[pnt, r]

Bead[Point[spec_?MatrixQ], r_:Scaled[0.01]] := Bead[spec, r]

Bead[Line[spec_?MatrixQ], r_:Scaled[0.01]] := Bead[spec, r]

Bead[Line[spec:{__?MatrixQ}], r_:Scaled[0.01]] := Bead[#,r]& /@ spec


GreatCircle::usage = "GreateCircle[center, apex, radius, {a1, a2, da}] returns Line corresponding to the great arc centered at center in the plane normal to apex - center from angle a1 to a2 in steps of da.\nGreatCircle[center, {u, v}, radius, {a1, a2, da}] corresponds to a great arc of radius centered at center in the plane containing center, u and v from angle a1 to a2 in step of da.\nGreatCircle[center, {u, v}] assumes raidus given by Norm[u-center] and angle by Vector[u-center,v-center]."

GreatCircle[] := GreatCircle[{0, 0, 0}, {0, 0, 1}, 1, {0, 2 Pi, 0.01}]

GreatCircle[center:{_, _, _}, apex:{_, _, _}] :=
  GreatCircle[center, apex, 1, {0, 2 Pi}]

GreatCircle[
  center:{_, _, _},
  apex:{_?NumericQ, _?NumericQ, _?NumericQ},
  radius_?NumericQ ] :=
  GreatCircle[center, apex, radius, {0, 2 Pi}]

GreatCircle[
  center:{_, _, _},
  apex:{_?NumericQ, _?NumericQ, _?NumericQ},
  radius_?NumericQ,
  {a1_, a2_, da_:0.01}
 ] := Module[
  { mat = RotationMatrix @ {{0, 0, 1}, apex - center},
    dat },
  dat = Table[
    radius*{Cos[ang], Sin[ang], 0},
    {ang, a1, a2, da}
   ];
  Line[(center + mat . #)& /@ dat]
 ]

GreatCircle[center_ -> {vec:{_, _, _}, wec:{_, _, _}}] := GreatCircle[
  center -> N @ {vec, wec},
  Norm @ N[vec-center],
  {0, VectorAngle[N[vec-center], N[wec-center]]}
 ]

GreatCircle[
  Rule[
    center:{_?NumericQ, _?NumericQ, _?NumericQ},
    { vec:{_?NumericQ, _?NumericQ, _?NumericQ},
      wec:{_?NumericQ, _?NumericQ, _?NumericQ} }
   ],
  spec___
 ] := GreatCircle[{vec, center, wec}, spec]

GreatCircle[
  { vec:{_?NumericQ, _?NumericQ, _?NumericQ},
    center:{_?NumericQ, _?NumericQ, _?NumericQ},
    wec:{_?NumericQ, _?NumericQ, _?NumericQ} }
 ] := GreatCircle[{vec, center, wec}, Norm @ N[vec-center], {0, 2 Pi}]

GreatCircle[
  { vec:{_?NumericQ, _?NumericQ, _?NumericQ},
    center:{_?NumericQ, _?NumericQ, _?NumericQ},
    wec:{_?NumericQ, _?NumericQ, _?NumericQ} },
  radius:(Automatic|_?NumericQ),
  {a1_?NumericQ, a2_?NumericQ, da_:0.01}
 ] := Module[
   { ax = N[vec-center],
     az = Cross[N[vec-center], N[wec-center]],
     ay, mat, dat, rad },
   ay = Cross[az, ax];
   mat = Transpose @ {
     Normalize[ax],
     Normalize[ay],
     Normalize[az]
    };
   rad = If[radius === Automatic, Norm[ax], radius];
   dat = Table[
     rad * {Cos[th], Sin[th], 0},
     {th, a1, a2, da}
    ];
   Line[(center + mat . #)& /@ dat]
  ]


(**** <MapThrough> ****)

MapThrough::usage = "MapThrough[{f,g,\[Ellipsis]}, {x,y,\[Ellipsis]}] gives {f[x],g[y],\[Ellipsis]}.\nMapThrough[functions, expr, levelspec] operates at the level of expr indicated by spec.\nThe level specificiation is the same as in Map.\nSee also Through, Thread, Apply, Map, MapThread, and MapApply."

MapThrough[ff_List, expr_, spec___] :=
  First @ Map[MapThread[Construct, {ff, #}]&, {expr}, spec]

(**** </MapThrough> ****)


(***** <ApplyThrough> *****)

ApplyThrough::usage = "ApplyThrough[f, expr] applies function f through special objects such as Association and SparseArray in expr, which usually do not work on the specifically represented form of data.\nApplyThrough[f] is an operator form."

ApplyThrough[func_][expr_] := ApplyThrough[func, expr]

ApplyThrough[func_, aa_Association] := Map[func, aa]

ApplyThrough[func_, aa_SparseArray] := 
  SparseArray[func @ ArrayRules @ aa, Dimensions @ aa]

ApplyThrough[func_, expr_] := func @ ReplaceAll[
  func[expr],
  { aa_Association :> ApplyThrough[func, aa],
    aa_SparseArray :> ApplyThrough[func, aa] }
 ]


nameThrough::usage = "nameThrough[\"name\"] defines new function \"nameThrough\"."

SetAttributes[nameThrough, Listable];

nameThrough[op_Symbol] := nameThrough[SymbolName @ op]

(* NOTE: It must be With[...]; Block nor Module works here. *)
nameThrough[name_String] := With[
  { full = Symbol @ StringJoin["Q3`", name, "Through"],
    func = Symbol[name]},
  full::usage = 
    SymbolName[full] <> "[expr] applies " <> name <> 
    " through special objects such as Association and SparseArray in expr, which usually do not allow for access to internal data.";
  full[expr_] := ApplyThrough[func, expr];
  SetAttributes[full, ReadProtected]
 ]

(* Aliases for some frequently used functions. *)
nameThrough @ {Chop, Simplify, FullSimplify};


ReplaceAllThrough::usage = "ReplaceAllThrough[expr, rules] applies ReplaceAll[ruels] through special objects such as Associatin and SparseArray in expr, which usually do not allow for access to internal data."

ReplaceAllThrough[aa_Association, rules_] := ReplaceAll[rules] /@ aa

ReplaceAllThrough[aa_SparseArray, rules_] :=
  SparseArray @ ReplaceAll[ArrayRules @ aa, rules]

ReplaceAllThrough[expr_, rules_] := ReplaceAll[
  ReplaceAll[expr, rules],
  { aa_Association :> ReplaceAllThrough[aa, rules],
    aa_SparseArray :> ReplaceallThrough[aa, rules] }
 ]

ReplaceAllThrough[rules_][expr_] := ReplaceAllThrough[expr, rules]

(***** </ApplyThrough> *****)


(**** <LeftBrace> ****)

LeftBrace::usage = "LeftBrace[y] returns the left brace spanning from -y to y."

Options[LeftBrace] = {
  "Width" -> 0.1
 }

LeftBrace[y_, OptionsPattern[]] := Module[
  { width = OptionValue["Width"],
    pts },
  pts = {
    {-width, 0},
    {-width/2, width/4},
    {-width/2, width/2},
    {-width/2, y - width/2},
    {-width/2, y - width/4},
    {0, y}
   };
  BSplineCurve /@ {pts, Transpose[Transpose[pts]*{1, -1}]}
 ]

LeftBrace[x_, {ymin_, ymax_}, opts___?OptionQ] := Map[
  TranslationTransform[Mean @ {{x, ymin}, {x, ymax}}], 
  LeftBrace[Abs[(ymax - ymin)/2], opts],
  {2}
 ]

LeftBrace[{xmin_, ymin_}, {xmax_, ymax_}, opts___?OptionQ] :=
  LeftBrace[xmin, {ymin, ymax}, opts] /; xmin == xmax

LeftBrace[{xmin_, ymin_}, {xmax_, ymax_}, opts___?OptionQ] := Module[
  { center = Mean @ {{xmin, ymin}, {xmax, ymax}},
    dir = {xmax-xmin, ymax-ymin} },
  Map[
    TranslationTransform[center] @* RotationTransform[{{0, 1}, dir}],
    LeftBrace[Norm[dir]/2, opts],
    {2}
   ]
 ]

RightBrace::usage = "RightBrace[y] returns the right brace spanning from -y to y."

RightBrace[y_, opts___?OptionQ] := Map[
  ReflectionTransform[{1, 0}],
  LeftBrace[y, opts],
  {2}
 ]

RightBrace[x_, {ymin_, ymax_}, opts___?OptionQ] := Map[
  TranslationTransform[Mean @ {{x, ymin}, {x, ymax}}], 
  RightBrace[Abs[(ymax - ymin)/2], opts],
  {2}
 ]

RightBrace[{xmin_, ymin_}, {xmax_, ymax_}, opts___?OptionQ] :=
  RightBrace[xmin, {ymin, ymax}, opts] /; xmin == xmax

RightBrace[{xmin_, ymin_}, {xmax_, ymax_}, opts___?OptionQ] := Module[
  { center = Mean @ {{xmin, ymin}, {xmax, ymax}},
    dir = {xmax-xmin, ymax-ymin} },
  Map[
    TranslationTransform[center] @* RotationTransform[{{0, 1}, dir}],
    RightBrace[Norm[dir]/2, opts],
    {2}
   ]
 ]

(**** </LeftBrace> ****)


Primed::usage = "Primed[a] represents another object closely related to a."

DoublePrimed::usage = "DoublePrimed[a] represents another object closely related to a."

SetAttributes[{Primed, DoublePrimed}, Listable]

Format @ Primed[a_] := Interpretation[Superscript[a,"\[Prime]"], Primed @ a]

Format @ DoublePrimed[a_] :=
  Interpretation[Superscript[a,"\[DoublePrime]"], DoublePrimed @ a]


(***** <LevelsPlot> *****)

LevelsPlot::usage = "LevelsPlot[{y1,y2,\[Ellipsis]}] generates a plot of levels at values y1, y2, \[Ellipsis]."

Options[LevelsPlot] = {
  "Size" -> 1,
  "Gap" -> 0.5,
  "Labels" -> None,
  "DataLabels" -> None,
  "DataStyles" -> None
 };

LevelsPlot[data:{__?NumericQ},
  opts:OptionsPattern[{LevelsPlot, Graphics, Plot}]] :=
  LevelsPlot[{data}, {0}, {1}, opts]

LevelsPlot[data:{__?ListQ},
  opts:OptionsPattern[{LevelsPlot, Graphics, Plot}]] :=
  LevelsPlot[data, {0}, {1}, opts]

LevelsPlot[data:{__?ListQ}, locale:{__?NumericQ},
  opts:OptionsPattern[{LevelsPlot, Graphics, Plot}]] :=
  LevelsPlot[data, locale, {1}, opts]

LevelsPlot[data:{__?ListQ}, locale:{__?NumericQ}, offset:{__Integer},
  opts:OptionsPattern[{LevelsPlot, Graphics, Plot}]] :=
  Module[
    { wid = OptionValue["Size"],
      gap = OptionValue["Gap"],
      sty = OptionValue["DataStyles"],
      tag = OptionValue["DataLabels"],
      txt = OptionValue["Labels"],
      off = padCyclic[offset, Length @ data],
      min, new, loc, lines, links, ticks, texts },
    loc = padAccumulate[locale, Length @ data, wid + gap];
    lines = MapThread[makeLines, {loc, loc+wid, data}];

    If[ sty === Automatic || sty === None, Null,
      sty = padCyclic[sty, Length @ data];
      lines = Thread[{sty, lines}];
     ];

    new = MapThread[Part[#1, #2;;]&, {data, off}];
    min = Min[Length /@ new];
    new = Take[#, min]& /@ new;
    
    links = {
      MapThread[Thread[{#1, #2}]&, {Most @ (loc+wid), Most @ new}],
      MapThread[Thread[{#1, #2}]&, {Rest @ loc, Rest @ new}]
     };
    links = If[ links == {{}, {}},
      Nothing,
      Line /@ Catenate @ Transpose[links, 1 <-> 3]
     ];

    ticks = If[ tag === None,
      None,
      tag = padCyclic[tag, Length @ data];
      Thread[{loc+wid/2, tag, 0}]
     ];

    texts = If[ txt === None,
      Nothing,
      txt = padCyclic[txt, Length @ data];
      makeLabels @@@ Thread[{loc+wid/2, data, txt}]
     ];

    Graphics[
      { {Thick, lines},
        {Dashed, links},
        texts },
      FilterRules[{opts}, Options @ Graphics],
      Frame -> {{True, False}, {True, False}},
      FrameStyle -> {{Directive[Black,Large], None}, {White, None}},
      FrameTicks -> {{Automatic, None}, {ticks, None}},
      FrameTicksStyle -> Directive[Large, Black],
      ImageSize -> Medium
     ]
   ]

padCyclic[set_, len_] := Module[
  { new },
  new =  If[ListQ @ set, set, List @ set];
  PadRight[new, len, new]
 ]

padAccumulate[set_, len_, span_] := If[ len > Length[set],
  Join[ set,
    Max[set] + Accumulate @ Table[span, len-Length[set]] ],
  Take[set, len]
 ]

makeLines[xmin_, xmax_, val:{__?NumericQ}] :=
  Line /@ Transpose @ {Thread @ {xmin, val}, Thread @ {xmax, val}}


makeLabels[x_, val:{__?NumericQ}, None] := {}

makeLabels[x_, val:{__?NumericQ}, txt_List] := Module[
  { new, loc },
  new = padCyclic[txt, Length @ val];
  loc = Thread[{x, val}];
  MapThread[Text[#1, #2, Bottom]&, {new, loc}]
 ]
(* NOTE: txt may include Graphics[...] such as from MaTeX. *)

(***** </LevelsPlot> ****)


(**** <MatrixObject> ****)

MatrixObject::usage = "MatrixObject[{{m11,m12,\[Ellipsis]}, {m21,m22,\[Ellipsis]}, \[Ellipsis]}] represents a dense matrix.\nIt may be useful to display a dense matrix in a compact form."

MatrixObject /:
MakeBoxes[MatrixObject[mat_List?MatrixQ], fmt_] :=
  BoxForm`ArrangeSummaryBox[
    MatrixObject, mat, None,
    { BoxForm`SummaryItem @ { "Type: ", "Dense" },
      BoxForm`SummaryItem @ { "Dimensions: ", Dimensions[mat] }
    },
    { BoxForm`SummaryItem @ { "Elements: ", MatrixForm @ Chop @ mat[[;;UpTo[4], ;;UpTo[4]]] }
    },
    fmt,
    "Interpretable" -> Automatic
  ]

MatrixObject[mat_SparseArray?MatrixQ] = mat

MatrixObject[mat_SymmetrizedArray?MatrixQ] = mat

(**** </MatrixObject> ****)


(**** <PanedText> ****)

PanedText::usage = "PanedText[expr] displays with expr in a paned area. See also Text."

Options[PanedText] = {
  "Style" -> {},
  "Angle" -> 0,
  "Alignment" -> {0, 0}, (*Center*)
  "PaneSize" -> {2, 1},
  "PanePosition" -> {0, 0},
  "PaneAlignment" -> {0, 0}, (*Center*)
  "Paned" -> False
};

PanedText[expr_, OptionsPattern[]] := Module[
  { sty, ang, adj, pos, size, off, txt },
  { sty, ang, adj, pos, size, off } = OptionValue[Automatic, #]& /@ 
    { "Style", "Angle", "Alignment",
      "PanePosition", "PaneSize", "PaneAlignment" };
  txt = Text[Style[expr, sty], pos + 0.5*size*(adj-off), adj, {Cos @ ang, Sin @ ang}];
  If[ OptionValue["Paned"],
    Module[
      { frm, dsk },
      frm = { EdgeForm[Gray], Opacity[0], 
        Rectangle[pos - 0.5*size*(1 + off), pos + 0.5*size*(1 - off)] };
      dsk = {Gray, Disk[pos, 0.1]};
      {frm, dsk, txt}
    ],
    txt
  ]
]

(**** </PanedText> ****)


(**** <doAssureList> ****)

doAssureList::usage = "doAssureList[] ..."

doAssureList[None] = {} (* cf. doForceList *)

doAssureList[a_?ListQ] = a

doAssureList[a_] = List[a]


doAssureList[None, _Integer] = {} (* cf. doForceList *)

doAssureList[a_?ListQ, n_Integer] := PadRight[a, n, a]

doAssureList[a_, n_Integer] := Table[a, n]

(**** </doAssureList> ****)


(**** <doForceList> ****)

doForceList::usage = "doForceList[] ..."

doForceList[a_?ListQ] = a

doForceList[a_] = List[a]


doForceList[a_?ListQ, n_Integer] := PadRight[a, n, a]

doForceList[a_, n_Integer] := Table[a, n]

(**** </doForceList> ****)

End[]

EndPackage[]
