(* -*- mode:math -*- *)

BeginPackage["QuantumMob`Q3`", {"System`"}]

If[ $VersionNumber < 13.1,
  Version::old = "Q3 requires Mathematica 13.1 or later.";
  Message[Version::old];
];

If[$VersionNumber < 14.2, System`LightDarkSwitched = Identity];
(* NOTE: PlaybookTools defines $PlaybookBannerColor using LightDarkSwitched, which was introduced in Mathematica 14.2. This affects the Q3/Playbook and Q3/PlaybookDraft stylesheets. *)


Unprotect["`*"];
ClearAll["`*"];

Q3General::legacy = "A legacy version of Q3 is removed, and instead new QuantumMob/Q3 is installed."

Begin["`Private`"]

ClearAll["`*"];

If[ Length[PacletFind @ "Q3"] > 0,
  Message[Q3General::legacy];
  PacletUninstall["Q3"]
];

End[]

EndPackage[]


(**** <Packages Loading> ****)

Get["QuantumMob`Q3`Abba`"];
Get["QuantumMob`Q3`Abby`"];
Get["QuantumMob`Q3`Abel`"];
Get["QuantumMob`Q3`Gauss`"];
Get["QuantumMob`Q3`Chebyshev`"];
Get["QuantumMob`Q3`Wimmer`"];
Get["QuantumMob`Q3`Cauchy`"];
Get["QuantumMob`Q3`Pauli`"];
Get["QuantumMob`Q3`Weyl`"];
Get["QuantumMob`Q3`Quisso`"];
Get["QuantumMob`Q3`QuantumCircuit`"];
Get["QuantumMob`Q3`Kraus`"];
Get["QuantumMob`Q3`Gray`"];
Get["QuantumMob`Q3`Gottesman`"];
Get["QuantumMob`Q3`Clifford`"];
Get["QuantumMob`Q3`Grassmann`"];
Get["QuantumMob`Q3`Fock`"];
Get["QuantumMob`Q3`Nambu`"];
Get["QuantumMob`Q3`Wick`"];
Get["QuantumMob`Q3`Wigner`"];
Get["QuantumMob`Q3`Dicke`"];
Get["QuantumMob`Q3`VonNeumann`"];
Get["QuantumMob`Q3`Young`"];
Get["QuantumMob`Q3`YoungFourier`"];
Get["QuantumMob`Q3`Schur`"];
Get["QuantumMob`Q3`SchurPlus`"];
Get["QuantumMob`Q3`Haar`"]
Get["QuantumMob`Q3`QSP`"];
Get["QuantumMob`Q3`QML`"];
Get["QuantumMob`Q3`Einstein`"]; (* should be loaded last *)
Get["QuantumMob`Q3`Custom`"];

(**** </Packages Loading> ****)


BeginPackage["QuantumMob`Q3`"]

Begin["`Private`"]

SetAttributes[Evaluate @ Names["`*"], ReadProtected];

End[]

SetAttributes[Evaluate @ Protect["`*"], ReadProtected];

(* Users are allowed to change global variables. *)
Unprotect["`$*"];

(* Too dangerous to change these global variables. *)
Protect[$GarnerPatterns, $ElaborationPatterns];

EndPackage[]
