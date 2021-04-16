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


LindbladSolve::usage = "LindbladSolve[...] returns the solution of the Lindblad equation ..."

LindbladSolve[ham_, op_List] := Module[
  { ss = NonCommutativeSpecies @ Flatten @ {ham, op},
    a, b },
  
  expressions;
  Return[a]
 ]

End[]

EndPackage[]
