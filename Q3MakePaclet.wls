#!/usr/bin/env wolframscript
(* -*- mode:math -*- *)
(* Mahn-Soo Choi *)
(* $Date: 2021-02-16 13:31:11+09 $ *)
(* $Revision: 1.4 $ *)

(* USASGE: ./Q3MakePaclet.wls *)
(* USASGE: /usr/local/bin/wolframscript -file Q3MakePaclet.wls *)

cwd = DirectoryName[$InputFileName];
pacletFolder = FileNameJoin @ {cwd, "build", "Q3"};
targetFolder = FileNameJoin @ {cwd, "build"};

paclet = CreatePacletArchive[pacletFolder, targetFolder];

If[ FailureQ[paclet],
  Print["Something is wrong and a paclet archive could not be created."],
  Print[paclet, " has been created successfully."]
 ];
