#!/usr/bin/env wolframscript
(* -*- mode:math -*- *)
(* Mahn-Soo Choi *)
(* $Date: 2021-02-25 09:17:50+09 $ *)
(* $Revision: 1.5 $ *)

(* USASGE: ./Q3MakePaclet.wls *)
(* USASGE: /usr/local/bin/wolframscript -file Q3MakePaclet.wls *)


cwd = DirectoryName[$InputFileName];
appDir = FileNameDrop[cwd, -1];
pacletDir = FileNameJoin @ {appDir, "build", "Q3"};

(* targetDir = FileNameJoin @ {appDir, "build"}; *)

gitDir = "/Users/Shared/GitHub"
targetDir = FileNameJoin @ {gitDir, "PacletServer", "Paclets"};

paclet = CreatePacletArchive[pacletDir, targetDir];

If[ FailureQ[paclet],
  Print["Something is wrong and a paclet archive could not be created."],
  Print[paclet, " has been created successfully."]
 ];

Print["Building PalcetSite files."];

siteDir = FileNameJoin @ {gitDir, "PacletServer"};

PacletManager`BuildPacletSiteFiles[siteDir];
