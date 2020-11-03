(* -*- mode:math -*- *)
(* Mahn-Soo Choi *)
(* $Date: 2020-11-04 02:04:59+09 $ *)
(* $Revision: 1.3 $ *)

BeginPackage["Q3`"]

If[ $VersionNumber < 12,
  Version::old = "Q3 requires Mathematica 12 or later.";
  Message[Version::old];
 ]

Begin["`Private`"]

End[]

EndPackage[]


Get["Q3`Cauchy`"]
Get["Q3`Pauli`"]
Get["Q3`Quisso`"]
Get["Q3`Fock`"]
Get["Q3`Wigner`"]
Get["Q3`Dicke`"]

