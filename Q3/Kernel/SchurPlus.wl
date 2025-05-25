(* -*- mode: Mathematica -*- *)

BeginPackage["QuantumMob`Q3`", {"System`"}]

{ DualSchurBasis };

Begin["`Private`"]

DualSchurBasis::usage = "DualSchurBasis[n, d] returns an association of Schur basis of n qudits of dimension d."

DualSchurBasis[n_Integer, d_Integer] := Module[
  { ss = YoungShapes[n, d],
    tt, bs },
  tt = PadRight[First /@ ss, {Length @ ss, d}];
  tt = Catenate[Permutations /@ tt];
  bs = Outer[DualSchurBasis, ss, tt, 1];
  Join @@ Flatten[bs]
]


DualSchurBasis[shape_YoungShape, d_Integer] := Module[
  { types = YoungTypes[shape, d] },
  Join @@ Map[DualSchurBasis[shape, #]&, types]
]

DualSchurBasis[type:{__Integer}] := Module[
  { shapes = YoungShapes[type] },
  Join @@ Map[DualSchurBasis[#, type]&, shapes]
]


DualSchurBasis[shape_YoungShape, type:{__Integer}] := Module[
  { dim = Length[type],
    sub = YoungSubgroup[type],
    rep, pbs, trv, prj, mat, tag, pos },

  {tag, pos} = DualSchurBasisNames[shape, type];

  (* irreducible represenations *)
  rep = YoungNormalRepresentation[shape];

  (* permutation/transversal basis *)
  pbs = Flatten @ MapThread[ConstantArray, {Range[dim]-1, type}];
  pbs = Permutations[pbs];

  (* transversal elements *)
  trv = Map[FindPermutation, pbs];
  trv = Map[rep, trv];

  (* projections *)
  sub = GroupElements[sub];
  prj = Mean[rep /@ sub];
  prj = prj[[All, pos]];

  mat = Dot[trv, prj];
  mat = Transpose[Conjugate[mat], {3, 1, 2}];
  mat = Map[Simplify @* Normalize, mat, {2}];

  (* permutation/transversal basis in the computation basis *)
  pbs = 1 + Map[FromDigits[#, dim]&, pbs];
  pbs = One[ Power[dim, YoungDegree @ shape] ][[pbs]];

  AssociationThread[tag -> Flatten[mat . pbs, 1]]
] /; DominatesQ[First @ shape, ReverseSort @ type]

DualSchurBasis[shape_YoungShape, type:{__Integer}] := Association[]


DualSchurBasisNames::usage = "DualSchurBasisNames[shape, types] returns {names, positions}, where names is a list of labels referring to the irreducible basis vectors and positions is the list of positions of standard Young tableaux that properly combines with type to generate a Weyl tableau."

(* labels of the irrep basis vectors *)
DualSchurBasisNames[shape_YoungShape, type:{__Integer}] := Module[
  { d = Length[type],
    yy = YoungTableaux[shape],
    ww = WeylTableaux[shape, type],
    kk },
  kk = Map[YoungRefersTo[#, d]&, ww];
  kk = Map[FirstPosition[yy, _?(#)]&, kk];
  { Tuples[{yy, ww}], Flatten[kk] }
] /; YoungDegree[shape] == Total[type]

End[]

EndPackage[]
