(* -*- mode: Mathematica -*- *)

BeginPackage["QuantumMob`Q3`", {"System`"}]

{ DualSchurBasis };

Begin["`Private`"]

DualSchurBasis::usage = "DualSchurBasis[n, d] returns an association of Schur basis of n qudits of dimension d."

DualSchurBasis[ss:{__?SpeciesQ}] :=
  DualSchurBasis[FlavorCap @ ss] /; Not[FlavorCapQ @ ss]

DualSchurBasis[ss:{__?SpeciesQ}] := Module[
  { cbs = Basis[ss], 
    sbs },
  sbs = DualSchurBasis[Length @ ss, Dimension @ First @ ss];
  Map[Dot[#, cbs]&, sbs]
]

DualSchurBasis[n_Integer, d_Integer] := Module[
  { ss = YoungShapes[n, d],
    tt, bs },
  tt = PadRight[First /@ ss, {Length @ ss, d}];
  tt = Catenate[Permutations /@ tt];
  bs = Outer[DualSchurBasis, ss, tt, 1];
  Join @@ Flatten[bs]
]


DualSchurBasis[shape_YoungShape, d_Integer] := Module[
  { contents = YoungContents[shape, d] },
  Join @@ Map[DualSchurBasis[shape, #]&, contents]
]

DualSchurBasis[content:{__Integer}] := Module[
  { shapes = YoungShapes[content] },
  Join @@ Map[DualSchurBasis[#, content]&, shapes]
]


DualSchurBasis[shape_YoungShape, content:{__Integer}] := Module[
  { dim = Length[content],
    sub = YoungSubgroup[content],
    rep, pbs, trv, prj, mat, tag, pos },

  {tag, pos} = DualSchurBasisNames[shape, content];

  (* irreducible represenations *)
  rep = YoungNormalRepresentation[shape];

  (* permutation/transversal basis *)
  pbs = Flatten @ MapThread[ConstantArray, {Range[dim]-1, content}];
  pbs = Permutations[pbs];

  (* transversal elements *)
  trv = Map[FindPermutation, pbs];
  trv = Map[rep, trv];

  (* projections *)
  sub = GroupElements[sub];
  prj = Mean[rep /@ sub];
  prj = prj[[All, pos]];

  (* NOTE: Somehow, Dot returns the result in a dense array. *)
  mat = SparseArray @ Dot[trv, prj];
  mat = Transpose[Conjugate[mat], {3, 1, 2}];
  mat = SimplifyThrough @ Map[Normalize, mat, {2}];

  (* permutation/transversal basis in the computation basis *)
  pbs = 1 + Map[FromDigits[#, dim]&, pbs];
  pbs = One[ Power[dim, YoungDegree @ shape] ][[pbs]];

  AssociationThread[tag -> SparseArray /@ Flatten[mat . pbs, 1]]
] /; DominatesQ[First @ shape, ReverseSort @ content]

DualSchurBasis[shape_YoungShape, content:{__Integer}] := Association[]


DualSchurBasisNames::usage = "DualSchurBasisNames[shape, content] returns {names, poslist}, where names is a list of labels referring to the irreducible basis vectors and poslist is the list of positions of standard Young tableaux that properly combines with content to generate a Weyl tableau."

(* labels of the irrep basis vectors *)
DualSchurBasisNames[shape_YoungShape, content:{__Integer}] := Module[
  { d = Length[content],
    yy = YoungTableaux[shape],
    ww = WeylTableaux[shape, content],
    kk },
  kk = Map[YoungRefersTo[#, d]&, ww];
  kk = Map[FirstPosition[yy, _?(#)]&, kk];
  { Tuples[{yy, ww}], Flatten[kk] }
] /; YoungDegree[shape] == Total[content]

End[]

EndPackage[]
