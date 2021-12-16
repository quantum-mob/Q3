#!/usr/bin/env wolframscript -v
(* -*- mode:math -*- *)
(* Mahn-Soo Choi *)
(* $Date: 2021-12-16 17:02:50+09 $ *)
(* $Revision: 1.4 $ *)

(* USASGE: ./Q3BuildDocumentation.wls *)
(* USASGE: /usr/local/bin/wolframscript -file Q3BuildDocumentation.wls *)


cwd = DirectoryName[$InputFileName];
appRoot = FileNameDrop[cwd, -1];
pacletPath = FileNameJoin @ {appRoot, "Q3"};

buildDir = "/Users/Shared/Q3App";

<<PacletTools`

PacletDocumentationBuild[pacletPath, buildDir]

(* End *)
