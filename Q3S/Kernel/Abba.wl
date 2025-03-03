(* ::Package:: *)

(* -*- mode:math -*- *)
BeginPackage["QuantumMob`Q3S`"]

{ Q3General };

{ Q3Info, Q3Release, Q3RemoteRelease,
  Q3Update, Q3CheckUpdate, Q3Assure, Q3Purge };

Q3::summary = "A symbolic quantum simulation framework on quantum information systems, quantum many-body systems, and quantum spin systems. First released to the public in 2020.";


Begin["`Private`"]

Q3General::usage = "Q3General is a symbol to which general messages concerning Q3 are attached.\nIt is similar to built-in symbol General."

Q3General::local = "You are using a locally installed beta version of Q3 while v`` is available from the server."

Q3General::setup = "The QuantumMob/Q3S has not been installed properly. Go to `` for the installation guide." 

Q3General::obsolete = "Symbol `` is obsolete. Use `` instead."

Q3General::excised = "Symbol `` has been excised."

Q3General::renamed = "Symbol `` has been renamed ``."

Q3General::deprecated = "Symbol `` is deprecated."

Q3General::changed = "The patterns for the arguments sequence of `1` have been changed: `2`"

Q3General::angle = "An angle should come first in the sequence of arguments for ``. Effective since Q3 v1.2.0."


(**** <Q3Info> ****)

Q3Info::usage = "Q3Info[] prints the information about the Q3 release and versions of packages included in it."

Q3Info[] := Module[
  { pac = PacletObject @ "QuantumMob/Q3S" },
  If[ FailureQ @ pac,
    Message[Q3General::setup,
      Hyperlink["https://github.com/quantum-mob/Q3/blob/main/INSTALL.md"]
    ];
    Return[pac]
  ];
  
  If[ Not @ StringContainsQ[
      pac @ "Location",
      FileNameJoin @ {"Paclets", "Repository"}
    ],
    Message[Q3General::local, Q3RemoteRelease[]]
  ];

  StringJoin["Q3 v", pac["Version"], " ", Q3::summary]
]

(**** </Q3Info> ****)


Q3Release::usage = "Q3Release[] returns a string containing the release version of Q3. If it fails to find and open the paclet of Q3, then it returns Failure."

Q3Release[] := Module[
  { pac = PacletObject @ "QuantumMob/Q3S",
    remote },
  If[FailureQ @ pac, Return @ pac];
  pac["Version"]
]


Q3RemoteRelease::usage = "Q3RemoteRelease[] returns a string containing the release version of Q3 at the GitHub repository."

Q3RemoteRelease[] := Module[
  { pac = PacletFindRemote @ "QuantumMob/Q3S" },
  If[pac == {}, $Failed, First[pac] @ "Version"]
]


(***** <Paclet Server> ****)

$serverURL = "https://github.com/quantum-mob/PacletRepository/raw/main"

serverRegisteredQ[url_:$serverURL] := Module[
  { ps = PacletSites[] },
  MemberQ[ Through[ps["URL"]], url ]
]

serverRegister[url_:$serverURL] :=
  PacletSiteUpdate @ PacletSiteRegister[url, "Quantum Mob Paclet Server"]

serverAssure[] := If[serverRegisteredQ[], Null, serverRegister[]]

pacletVersion[pp:{__PacletObject}] := pacletVersion[First @ pp]

pacletVersion[pac_PacletObject] := pac["Version"]

versionNumber[vv:{__String}] := versionNumber[First @ vv]

versionNumber[ver_String] := With[
  { new = StringSplit[ver, "."] },
  If[AllTrue[new, DigitQ], ToExpression @ new, ver]
]

(***** </Paclet Server> ****)


Q3Assure::usage = "Q3Assure[version] checks whether Q3 has the specified version or later."

Q3Assure[version_?StringQ] := With[
  { vv = ToExpression @ StringSplit[version, "."],
    cc = ToExpression @ StringSplit[Q3Release[], "."] },
  If[ Not[OrderedQ @ {vv, cc}],
    PrintTemporary["Q3 v" <> version <> " or later is required and Q3 is being updated."];
    If[FailureQ @ Q3Update[], $Failed, Get["QuantumMob`Q3S`"]]
  ]
]


Q3CheckUpdate::usage = "Q3CheckUpdate[] checks if there is a newer release of Q3 in the GitHub repository."

Q3CheckUpdate::fresh = "You are using the latest release v`` of Q3."

Q3CheckUpdate[] := Module[
  { pac, new },
  PrintTemporary["Checking for updates ..."];
  PacletDataRebuild[];
  serverAssure[];
  pac = PacletFind["QuantumMob/Q3S"];
  new = PacletFindRemote["QuantumMob/Q3S", UpdatePacletSites -> True];
  If[ pac=={}, Return[$Failed], pac = pacletVersion[pac] ];
  If[ new=={}, Return[$Failed], new = pacletVersion[new] ];
  If[ OrderedQ @ {versionNumber @ new, versionNumber @ pac},
    ToString @ StringForm[Q3CheckUpdate::fresh, pac],
    PrintTemporary["Q3,v", new, " is now available; you are using v", pac, "."];
    Q3Update[]
  ]
]


Q3Update::usage = "Q3Update[] installs the latest update of Q3 from the GitHub repository.\nIt accepts all the options for PacletInstall -- ForceVersionInstall and AllowVersionUpdate in particular."

Q3Update[opts___?OptionQ] := (
  PrintTemporary["Installing an update ..."];
  PacletDataRebuild[];
  serverAssure[];
  PacletInstall["QuantumMob/Q3S", opts, UpdatePacletSites -> True]
)


Q3Purge::ussage = "Q3Purge[] uninstalls all but the lastest version of Q3."

Q3Purge::noq3 = "Q3 is not found."

Q3Purge[] := Module[
  { pacs = PacletFind["QuantumMob/Q3S"],
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
