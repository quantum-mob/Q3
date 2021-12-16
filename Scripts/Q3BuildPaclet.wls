#!/usr/bin/env wolframscript
(* -*- mode:math -*- *)
(* Mahn-Soo Choi *)
(* $Date: 2021-12-16 17:40:49+09 $ *)
(* $Revision: 1.3 $ *)

(* USASGE: ./Q3MakePaclet.wls *)
(* USASGE: /usr/local/bin/wolframscript -file Q3MakePaclet.wls *)


cwd = DirectoryName[$InputFileName];
appDir = FileNameDrop[cwd, -1];

buildDir = "/Users/Shared/Q3App";
pacletDir = FileNameJoin @ {buildDir, "Q3"};

gitDir = "/Users/Shared/GitHub"
targetDir = FileNameJoin @ {gitDir, "PacletServer", "Paclets"};

(* << PacletTools` *)

(* paclet = PacletBuild[pacletDir, targetDir]; *)
(* It is difficult for me to use this method. *)

paclet = CreatePacletArchive[pacletDir, targetDir];

If[ FailureQ[paclet],
  Print["Something is wrong and a paclet archive could not be created."],
  Print[paclet, " has been created successfully."]
 ];

Print["Building PalcetSite files."];

siteDir = FileNameJoin @ {gitDir, "PacletServer"};

PacletManager`BuildPacletSiteFiles[siteDir];
