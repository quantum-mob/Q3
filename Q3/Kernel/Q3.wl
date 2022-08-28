(* -*- mode:math -*- *)

If[ $VersionNumber < 12.3,
  Version::old = "Q3 requires Mathematica 12.3 or later.";
  Message[Version::old];
 ]

Q3`Q3Clear["Q3`Private`"];
Q3`Q3Clear["Q3`"];

BeginPackage["Q3`"]

`Q3`$Version = StringJoin[
  "Q3/", $Input, " v",
  StringSplit["$Revision: 2.49 $"][[2]], " (",
  StringSplit["$Date: 2022-08-17 17:57:47+09 $"][[2]], ") ",
  "Mahn-Soo Choi"
 ];

{ Q3General };

{ Q3Info, Q3Release, Q3RemoteRelease,
  Q3Update, Q3CheckUpdate, Q3Assure, Q3Purge };

{ Q3Clear, Q3Unprotect, Q3Protect };


Begin["`Private`"]

Q3General::usage = "Q3General is a symbol to which general messages concerning Q3 are attached.\nIt is similar to built-in symbol General."

Q3General::beta = "You are using a beta version of Q3 locally installed in `1` while v`2` is available from the server."

Q3General::faulty = "The Q3 application has not been installed properly. Go to `` for the instruction." 

Q3General::obsolete = "Symbol `` is obsolete. Use `` instead."

Q3General::excised = "Symbol `` has been excised."

Q3General::renamed = "Symbol `` has been renamed ``."

Q3General::changed = "The patterns for the sequence of arguments for `1` have been changed: `2`"

Q3General::angle = "An angle should come first in the sequence of arguments for ``. Effective since Q3 v1.2.0."


Q3Clear::usage = "Q3Clear[context] first unprotects all symbols defined in the context of context, and then CleaAll all non-variable symbols -- those the name of which does not start with '$'.\nQ3Clear is for internal use."

Q3Clear[] := Q3Clear[$Context]

Q3Clear[context_String] := Module[
  { vars = Names[context <> "$*"],
    symb = Names[context <> "*"] },
  Unprotect[Evaluate @ symb];
  symb = Complement[symb, vars];
  ClearAll @@ Evaluate[symb]
 ]


Q3Unprotect::usage = "Q3Unprotect[context] unprotects all symbols in the specified context.\nQ3Unprotect is for internal use."

Q3Unprotect[] := Q3Unprotect[$Context]

Q3Unprotect[context_String] :=
  Unprotect @ Evaluate @ Names[context <> "$*"]


Q3Protect::usage = "Q3Protect[context] protects all symbols in the specified context. In addition, it sets the ReadProtected attribute to all non-variable symbols -- those the name of which does not start with the character '$'.\nQ3Protect is for internal use."

Q3Protect[] := Q3Protect[$Context]

Q3Protect[context_String] := Module[
  { vars = Names[context <> "$*"],
    symb = Names[context <> "*"] },
  symb = Complement[symb, vars];
  SetAttributes[Evaluate @ symb, ReadProtected];
  Protect[Evaluate @ symb]
 ]


Q3Info::usage = "Q3Info[] prints the information about the Q3 release and versions of packages included in it."

Q3Info[] := Module[
  { pac = PacletObject @ "Q3",
    pkg = Symbol /@ Names["Q3`*`$Version"],
    ver },
  If[ FailureQ @ pac,
    Message[Q3General::faulty,
      Hyperlink["https://github.com/quantum-mob/Q3/blob/main/INSTALL.md"]
     ];
    Return[pac]
   ];
  
  If[ Not @ StringContainsQ[pac @ "Location", "/Paclets/Repository/Q3-"],
    Message[Q3General::beta, pac @ "Location", Q3RemoteRelease[]]
   ];

  ver = "Q3 Application v" <> pac["Version"];  
  pkg = Join[{ver}, pkg];
  Echo @ StringJoin @ Riffle[pkg, "\n"];
 ]

Q3Release::usage = "Q3Release[] returns a string containing the release version of Q3. If it fails to find and open the paclet of Q3, then it returns Failure."

Q3Release[] := Module[
  { pac = PacletObject @ "Q3",
    remote },
  If[FailureQ @ pac, Return @ pac];
  pac["Version"]
 ]

Q3RemoteRelease::usage = "Q3RemoteRelease[] returns a string containing the release version of Q3 at the GitHub repository."

Q3RemoteRelease[] := Module[
  { pac = PacletFindRemote @ "Q3" },
  If[pac == {}, $Failed, First[pac] @ "Version"]
 ]


(***** <Paclet Server> ****)

$serverURL = "https://github.com/quantum-mob/PacletServer/raw/main"

serverRegisteredQ[url_:$serverURL] := Module[
  { ps = PacletSites[] },
  MemberQ[ Through[ps["URL"]], url ]
 ]

serverRegister[url_:$serverURL] :=
  PacletSiteUpdate @ PacletSiteRegister[url, "Quantum Mob Paclet Server"]

serverEnsure[] := If[serverRegisteredQ[], Null, serverRegister[]]

pacletVersion[pp:{__PacletObject}] := pacletVersion[First @ pp]

pacletVersion[pac_PacletObject] := pac["Version"]

versionNumber[vv:{__String}] := versionNumber[First @ vv]

versionNumber[ver_String] := With[
  { new = StringSplit[ver, "."] },
  If[ AllTrue[new, DigitQ],
    ToExpression @ new,
    ver
   ]
 ]

(***** </Paclet Server> ****)


Q3Assure::usage = "Q3Assure[version] checks whether Q3 has the specified version or later."

Q3Assure[version_?StringQ] := With[
  { vv = ToExpression @ StringSplit[version, "."],
    cc = ToExpression @ StringSplit[Q3Release[], "."] },
  If[ Or @@ Thread[vv > cc],
    PrintTemporary["Q3 v" <> version <> " or later is required and Q3 is being updated."];
    If[FailureQ @ Q3Update[], $Failed, Get["Q3`"]]
   ]
 ]


Q3CheckUpdate::usage = "Q3CheckUpdate[] checks if there is a newer release of Q3 in the GitHub repository."

Q3CheckUpdate[] := Module[
  { pac, new },
  serverEnsure[];
  pac = PacletFind["Q3"];
  new = PacletFindRemote["Q3", UpdatePacletSites->True];
  If[ pac=={}, Return[$Failed], pac = pacletVersion[pac] ];
  If[ new=={}, Return[$Failed], new = pacletVersion[new] ];
  If[ OrderedQ @ {versionNumber @ new, versionNumber @ pac},
    Print["You are using the latest release v", pac, " of Q3."],
    Print["Q3,v", new, " is now available -- you are using v",
      pac, ".\nUse Q3Update to install the update."]
   ]
 ]


Q3Update::usage = "Q3Update[] installs the latest update of Q3 from the GitHub repository.\nIt accepts all the options for PacletInstall -- ForceVersionInstall and AllowVersionUpdate in particular."

Q3Update[opts___?OptionQ] := (
  serverEnsure[];
  PacletInstall["Q3", opts, UpdatePacletSites->True]
 )


Q3Purge::ussage = "Q3Purge[] uninstalls all but the lastest version of Q3."

Q3Purge::noq3 = "Q3 is not found."

Q3Purge[] := Module[
  { pacs = PacletFind["Q3"],
    vers, mssg },
  If[ pacs == {},
    Message[Q3Purge::noq3];
    Return[{Null}]
   ];
  vers = Map[#["Version"]&, pacs];
  mssg = StringJoin[
    "Are you sure to remove old versions ",
    StringRiffle[Rest @ vers, ", "],
    " of Q3?"
   ];
  PacletUninstall @ Rest @ pacs
 ]

End[]

EndPackage[]


(**** <Packages Loading> ****)

(* NOTE 2021-04-16 on v12.2.0: Just to load the package, one can put these in
   the second argument of BeginPackage["Q3`", {...}]. In this case, however,
   the symbols defined in those contexts are not listed/showed in the
   "AutoPopupEable" feature.
   *)

Get["Q3`Abel`"];
Get["Q3`Cauchy`"];
Get["Q3`Pauli`"];
Get["Q3`Quisso`"];
Get["Q3`Quville`"];
Get["Q3`Kraus`"];
Get["Q3`Gray`"];
Get["Q3`Gottesman`"];
Get["Q3`Grassmann`"];
Get["Q3`Fock`"];
Get["Q3`Wigner`"];
Get["Q3`Dicke`"];
Get["Q3`VonNeumann`"];
Get["Q3`Young`"];
Get["Q3`Schur`"];
Get["Q3`Knuth`"];
Get["Q3`Einstein`"]; (* should be loaded last *)
Get["Q3`Custom`"];

(**** </Packages Loading> ****)


BeginPackage["Q3`"]

(* $ElaborationRules is too messay to show the value. *)
SetAttributes[$ElaborationPatterns, ReadProtected];

(* Too dangerous to allow users to change these. *)
Protect[$GarnerPatterns, $ElaborationPatterns];

EndPackage[]

Q3`Q3Protect["Q3`"];
