(* -*- mode:math -*- *)

BeginPackage[ "Q3`Lindblad`",
  { "Q3`Abel`",
    "Q3`Cauchy`",
    "Q3`Pauli`",
    "Q3`Quisso`",
    "Q3`Fock`",
    "Q3`Wigner`"
   }
 ]

{ LindbladSolve };

{ OperatorBasis };

Begin["`Private`"]

OperatorBasis[n_] := Module[
  { zz = ConstantArray[0, n],
    aa = ConstantArray[1, n],
    bs },
  bs = Join[
    {Normalize @ aa},
    Table[ Normalize @ ReplacePart[zz, {j -> 1, -j -> -1}], {j, 1, n/2}]
   ];
  Join[bs,
    Table[
      Normalize @ ReplacePart[zz,
        { j -> 1,
          -j -> 1,
          j+1 -> -1,
          -(j+1) -> -1
         }
       ],
      {j, 1, n/2-1}
     ]
   ]
 ]

LindbladSolve::usage = "LindbladSolve[...] returns the solution of the Lindblad equation ..."

LindbladSolve[ham_, op_List] := Module[
  { ss = NonCommutativeSpecies @ Flatten @ {ham, op},
    a, b },
  
  expressions;
  Return[a]
 ]

End[]

EndPackage[]
