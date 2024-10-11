(* -*- mode:math -*- *)

If[ $VersionNumber < 12.3,
  Version::old = "Q3 requires Mathematica 12.3 or later.";
  Message[Version::old];
];

BeginPackage["Q3`"]

Unprotect["`*"];
ClearAll["`*"];

Begin["`Private`"]

ClearAll["`*"];

End[]

EndPackage[]


(**** <Packages Loading> ****)

Get["Q3`Abba`"];
Get["Q3`Abby`"];
Get["Q3`Abel`"];
Get["Q3`Chebyshev`"];
Get["Q3`Wimmer`"];
Get["Q3`Cauchy`"];
Get["Q3`Pauli`"];
Get["Q3`Weyl`"];
Get["Q3`Quisso`"];
Get["Q3`QuantumCircuit`"];
Get["Q3`Kraus`"];
Get["Q3`Gray`"];
Get["Q3`Gottesman`"];
Get["Q3`Clifford`"];
Get["Q3`Grassmann`"];
Get["Q3`Fock`"];
Get["Q3`Wick`"];
Get["Q3`Nambu`"];
Get["Q3`Wigner`"];
Get["Q3`Dicke`"];
Get["Q3`VonNeumann`"];
Get["Q3`Young`"];
Get["Q3`YoungFourier`"];
Get["Q3`Schur`"];
Get["Q3`QSP`"];
Get["Q3`QML`"];
Get["Q3`Einstein`"]; (* should be loaded last *)
Get["Q3`Custom`"];

(**** </Packages Loading> ****)


BeginPackage["Q3`"]

Begin["`Private`"]

SetAttributes[Evaluate @ Names["`*"], ReadProtected];

End[]

SetAttributes[Evaluate @ Protect["`*"], ReadProtected];

(* Users are allowed to change global variables. *)
Unprotect["`$*"];

(* Too dangerous to change these global variables. *)
Protect[$GarnerPatterns, $ElaborationPatterns];

EndPackage[]
