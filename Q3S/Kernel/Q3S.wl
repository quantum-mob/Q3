(* -*- mode:math -*- *)

If[ $VersionNumber < 13.1,
  Version::old = "Q3 requires Mathematica 13.1 or later.";
  Message[Version::old];
];
$ContextAliases["Q3`"] = "QuantumMob`Q3S`";


BeginPackage["QuantumMob`Q3S`", {"System`"}]

Unprotect["`*"];
ClearAll["`*"];

Q3General::legacy = "A legacy version of Q3 is removed, and instead new QuantumMob/Q3S is installed."

Begin["`Private`"]

ClearAll["`*"];

If[ Length[PacletFind @ "Q3"] > 0,
  Message[Q3General::legacy];
  PacletUninstall["Q3"]
];

End[]

EndPackage[]


(**** <Packages Loading> ****)

Get["QuantumMob`Q3S`Abba`"];
Get["QuantumMob`Q3S`Abby`"];
Get["QuantumMob`Q3S`Abel`"];
Get["QuantumMob`Q3S`Gauss`"];
Get["QuantumMob`Q3S`Chebyshev`"];
Get["QuantumMob`Q3S`Wimmer`"];
Get["QuantumMob`Q3S`Cauchy`"];
Get["QuantumMob`Q3S`Pauli`"];
Get["QuantumMob`Q3S`Weyl`"];
Get["QuantumMob`Q3S`Quisso`"];
Get["QuantumMob`Q3S`QuantumCircuit`"];
Get["QuantumMob`Q3S`Kraus`"];
Get["QuantumMob`Q3S`Gray`"];
Get["QuantumMob`Q3S`Gottesman`"];
Get["QuantumMob`Q3S`Clifford`"];
Get["QuantumMob`Q3S`Grassmann`"];
Get["QuantumMob`Q3S`Fock`"];
Get["QuantumMob`Q3S`Nambu`"];
Get["QuantumMob`Q3S`Wick`"];
Get["QuantumMob`Q3S`Wigner`"];
Get["QuantumMob`Q3S`Dicke`"];
Get["QuantumMob`Q3S`VonNeumann`"];
Get["QuantumMob`Q3S`Young`"];
Get["QuantumMob`Q3S`YoungFourier`"];
Get["QuantumMob`Q3S`Schur`"];
Get["QuantumMob`Q3S`QSP`"];
Get["QuantumMob`Q3S`QML`"];
Get["QuantumMob`Q3S`Einstein`"]; (* should be loaded last *)
Get["QuantumMob`Q3S`Custom`"];


(**** </Packages Loading> ****)


BeginPackage["QuantumMob`Q3S`"]

Begin["`Private`"]

SetAttributes[Evaluate @ Names["`*"], ReadProtected];

End[]

SetAttributes[Evaluate @ Protect["`*"], ReadProtected];

(* Users are allowed to change global variables. *)
Unprotect["`$*"];

(* Too dangerous to change these global variables. *)
Protect[$GarnerPatterns, $ElaborationPatterns];

EndPackage[]
