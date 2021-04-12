(* -*- mode:math -*- *)

If[ $VersionNumber < 12,
  Version::old = "Q3 requires Mathematica 12 or later.";
  Message[Version::old];
 ]

BeginPackage[ "Q3`",
  { "Q3`Abel`",
    "Q3`Cauchy`",
    "Q3`Pauli`",
    "Q3`Quisso`",
    "Q3`Grassmann`",
    "Q3`Fock`",
    "Q3`Wigner`",
    "Q3`Dicke`",
    "Q3`Einstein`"
   }
 ]

Q3Clear[];

{ Q3General };

{ Q3Clear, Q3Protect };

{ Q3Info, Q3Release, Q3RemoteRelease,
  Q3Update, Q3CheckUpdate, Q3Purge };


Begin["`Private`"]
`Version = StringJoin[
  $Input, " v",
  StringSplit["$Revision: 2.1 $"][[2]], " (",
  StringSplit["$Date: 2021/04/11 10:07:49 $"][[2]], ") ",
  "Mahn-Soo Choi"
 ];
End[]


Begin["`Private`"]

Q3General::usage = "Notice is a symbol to which general messages concerning Q3 are attached.\nIt is similar to General, but its Context is Q3."

Q3General::obsolete = "The symbol `` is OBSOLETE. Use `` instead."

Q3General::newUI = "An angle should come first. The order of the input arguments of `` has been changed since Q3 v1.2.0."


Q3Clear::usage = "Q3Clear[ctxt] first unprotects all symbols defined in the context of ctxt and then CleaAll all non-variable symbols -- those the name of which does not start with '$'.\nQ3Clear is for internal use."

Q3Clear[] := Q3Clear@Context[]

Q3Clear[context_String] := (
  Unprotect @ Evaluate[context <> "*"];
  ClearAll @@ Names @ RegularExpression[context <> "[^`$]*"]
 )


Q3Protect::usage = "Q3Protect[context] protects all symbols in the specified context. In addition, it sets the ReadProtected attribute to all non-variable symbols -- those the name of which does not start with the character '$'.\nQ3Protect is for internal use."

Q3Protect[] := Q3Protect[$Context]

Q3Protect[context_String] := Module[
  { vars = Names[context <> "$*"],
    symb = Names[context <> "*"] },
  symb = Complement[symb, vars];
  SetAttributes[Evaluate @ symb, ReadProtected];
  Protect[Evaluate @ symb]
 ]


Q3Info::usage = "Q3Info[] prints the information about the Q3 release and versions of packages in it."

Q3Info[] := Module[
  { pac = Q3Release[],
    pkg = Symbol /@ Names["Q3`*`Version"] },
  If[ FailureQ[pac],
    pac = "Q3 Application has not been installed properly.",
    pac = "Q3 Application v" <> pac;
   ];
  pkg = Join[{pac}, pkg];
  Print @ StringJoin @ Riffle[pkg, "\n"];
 ]

Q3Release::usage = "Q3Release[] returns a string containing the release version of Q3. If it fails to find and open the paclet of Q3, then it returns Failure."

Q3Release[] := Module[
  { pac = PacletObject @ "Q3" },
  If[ FailureQ[pac], pac, pac["Version"] ]
 ]

Q3RemoteRelease::usage = "Q3RemoteRelease[] returns a string containing the release version of Q3 at the GitHub repository."

Q3RemoteRelease[] := Module[
  { pac = PacletFindRemote @ "Q3" },
  If[ pac == {}, $Failed, First[pac]["Version"] ]
 ]


(***** <Paclet Server> ****)

$serverURL = "https://github.com/quantum-mob/PacletServer/raw/main"

serverRegisteredQ[url_:$serverURL] := Module[
  { ps = PacletSites[] },
  MemberQ[ Through[ps["URL"]], url ]
 ]

serverRegister[url_:$serverURL] :=
  PacletSiteUpdate @ PacletSiteRegister[url, "Quantum Mob Paclet Server"]

serverEnsure[] := If[ serverRegisteredQ[], Null, serverRegister[] ]

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
  PacletInstall["Q3", opts]
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

Q3Protect[]

EndPackage[]
