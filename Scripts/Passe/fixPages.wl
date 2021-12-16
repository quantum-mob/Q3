(* -*- mode:math -*- *)
(* Mahn-Soo Choi *)
(* $Date: 2021-02-28 22:04:22+09 $ *)
(* $Revision: 1.12 $ *)

(* USASGE: ./Q3MakePaclet.wls *)
(* USASGE: /usr/local/bin/wolframscript -file Q3MakePaclet.wls *)

pacletName = "Q3";

cwd = DirectoryName[$InputFileName];
appDir = FileNameDrop[cwd, -1];
pacletDir = FileNameJoin @ {appDir, pacletName};
documentationDir = FileNameJoin @ {pacletDir, "Documentation", "English"};

guidesDir = FileNameJoin @ {documentationDir, "Guides"};
symbolsDir = FileNameJoin @ {documentationDir, "ReferencePages", "Symbols"};
tutorialsDir = FileNameJoin @ {documentationDir, "Tutorials"};


SetAttributes[Unless, HoldRest];
Unless[condition_, out_] := If[Not[condition], out];


notebookBackup[nb_NotebookObject, opts___?OptionQ] := CopyFile[
  NotebookFileName[nb],
  NotebookFileName[nb]<>"~",
  opts,
  OverwriteTarget -> True
 ]


fixStyleSheet[nb_NotebookObject] := Module[
  { sty, new },
  sty = StyleDefinitions /. Options[nb, StyleDefinitions];
  new = sty /. {
    "FunctionPageStyles.nb" -> "FunctionPageStylesExt.nb",
    "TechNotePageStyles.nb" -> "TechNotePageStylesExt.nb",
    "TutorialPageStyles.nb" -> "TechNotePageStylesExt.nb",
    "GuidePageStyles.nb" -> "GuidePageStylesExt.nb"
   };
  Unless[ sty == new,
    Print[sty, "\n\t-> ", new];
    Unless[ FailureQ @ notebookBackup[nb],
      FrontEndExecute[SetOptions[nb, StyleDefinitions -> new]];
      NotebookSave[nb]
     ]
   ];
  new
 ]


fixPacletName::nopaclet = "No cell with label Paclet Name in ``."

fixPacletName[nb_NotebookObject] := Module[
  { obj, dat },

  NotebookRead /@ Cells[nb]; (* I don't know why, but this is necessary.*)
  
  obj = Cells[nb, CellLabel -> "Paclet Name"];
  If[ Length[obj] == 0,
    Message[fixPacletName::nopaclet, NotebookFileName[nb]];
    Return[]
   ];

  obj = First[obj];
  dat = NotebookRead[obj];
  
  Unless[ First[dat] == "Q3",
    Unless[ FailureQ @ notebookBackup[nb],
      Print[NotebookFileName[nb], ": ", First @ dat];
      NotebookWrite[obj, ReplacePart[dat, 1 -> "Q3"]];
      NotebookSave[nb]
     ];
   ];
 ]


fixMoreAbout[nb_NotebookObject] := Module[
  { cells, obj, new, data },
  cells = Cells[ nb,
    CellStyle -> (
      "MoreAbout" | "GuideMoreAbout" | "TutorialMoreAbout" |
      "Tutorials" | "RelatedTutorials" | "GuideTutorial"
     )
   ];
  If[ Length[cells] == 0,
    Return[],
    $temporaryOut = PrintTemporary @ NotebookFileName[nb];
   ];

  Table[
    data = NotebookRead[obj];
    new  = data /. {
      (* guides *)
      "paclet:Q3/guide/Quisso" -> "paclet:Q3/guide/QuissoPackageGuide",
      "paclet:Q3/guide/Pauli" -> "paclet:Q3/guide/PauliPackageGuide",
      "paclet:Q3/guide/Wigner" -> "paclet:Q3/guide/WignerPackageGuide",
      "paclet:Q3/guide/Grassmann" -> "paclet:Q3/guide/GrassmannPackageGuide",
      "paclet:Q3/guide/Fock" -> "paclet:Q3/guide/FockPackageGuide",
      "paclet:Q3/guide/Cauchy" -> "paclet:Q3/guide/CauchyPackageGuide",
      "paclet:Q3/guide/Dicke" -> "paclet:Q3/guide/DickePackageGuide",
      (* tutorials *)
      "paclet:Q3/tutorial/Quisso" -> "paclet:Q3/tutorial/QuissoQuickStart",
      "paclet:Q3/tutorial/Pauli" -> "paclet:Q3/tutorial/PauliQuickStart",
      "paclet:Q3/tutorial/Wigner" -> "paclet:Q3/tutorial/WignerQuickStart",
      "paclet:Q3/tutorial/Grassmann" -> "paclet:Q3/tutorial/GrassmannQuickStart",
      "paclet:Q3/tutorial/Fock" -> "paclet:Q3/tutorial/FockQuickStart",
      "paclet:Q3/tutorial/Cauchy" -> "paclet:Q3/tutorial/CauchyQuickStart",
      "paclet:Q3/tutorial/Dicke" -> "paclet:Q3/tutorial/DickeQuickStart",
      "paclet:Q3/tutorial/Q3" -> "paclet:Q3/tutorial/Q3QuickStart"
     };
    Unless[ data === new,
      PrintTemporary[data, "\t-->\t", new];
      notebookBackup[nb];
      NotebookWrite[obj, new];
      NotebookSave[nb]
     ],
    {obj, cells}
   ];
 ]


$pkgs = {"Cauchy", "Dicke", "Fock", "Pauli", "Quisso", "Wigner"};
  
$pttn = Alternatives @@ Join[
  StringJoin["paclet:Q3/guide/",#]& /@ $pkgs,
  StringJoin["paclet:Q3/tutorial/",#]& /@ $pkgs,
  { "paclet:Q3/tutorial/Q3Overview" }
 ];

$rule = Join[
  Thread[
    Map[StringJoin["paclet:Q3/guide/",#]&, $pkgs] ->
      Map[StringJoin["paclet:Q3/guide/",#, "PackageGuide"]&, $pkgs]
   ],
  Thread[
    Map[StringJoin["paclet:Q3/tutorial/",#]&, $pkgs] ->
      Map[StringJoin["paclet:Q3/tutorial/",#, "QuickStart"]&, $pkgs]
   ],
  { "paclet:Q3/tutorial/Q3Overview" ->
      "paclet:Q3/tutorial/Q3ReferenceManual" }
 ];

fixButtonData[nb_NotebookObject] := Module[
  { data, news, this },
  data = NotebookGet[nb];

  this = Options[#, ButtonData]& /@ Cases[data, _ButtonBox, Infinity];
  this = Select[Flatten @ Values[this], StringQ];
  this = Cases[this, $pttn];
  If[ Length[this] < 1,
    PrintTemporary["No URI to fix in ", NotebookFileName[nb]];
    Return[]
   ];

  PrintTemporary[NotebookFileName[nb], ": ", this];
  news = data /. $rule;
  If[ news === data, Return[] ];

  notebookBackup[nb];
  NotebookPut[news, nb];
  NotebookSave[nb];
 ]


(* ****** *)

files = FileNames["*.nb", {tutorialsDir}];
files = FileNames["*.nb", {guidesDir}];
files = FileNames["*.nb", {symbolsDir}];
files = FileNames["*.nb", {documentationDir}, 3];

(* files = files[[;;20]]; *)
  

fixPages[] := Check[
  $temporaryOut = PrintTemporary["Start"];
  Scan[
    Function[ file,
      (* Print["\nWorking on ", file]; *)
      Module[
        { nb },
        nb = NotebookOpen[file, Visible -> False];
        (* NOTE: Do NOT put Visible -> False. If you do, the cell groups are
           screwed up. *)
        Unless[ FailureQ[nb],
          (* fixStyleSheet[nb]; *)
          (* fixPacletName[nb]; *)
          (* fixMoreAbout[nb]; *)
          fixButtonData[nb];
         ];
        NotebookClose[nb];
       ]
     ],
    files
   ],
  $Failed
 ]
