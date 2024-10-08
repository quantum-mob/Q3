(* -*- mode:math -*- *)
BeginPackage["PlaybookTools`"]

Unprotect["`*"];
ClearAll["`*"];

{ PlaybookDeploy };
{ PlaybookCheckIn, PlaybookCheckOut };
  
(* See also MakeContents from AuthorTools`. *)
{ PlaybookContents,
  PlaybookContentsLine,
  $PlaybookContentsName = "Table of Contents" };

{ PlaybookEpilog };

{ PlaybookBanner, $PlaybookBannerTitle,
  ToggleBanner, SetBanner, UnsetBanner };

{ $ParagraphDelimiter };


Begin["`Private`"]

ClearAll["`*"];


(**** <ParagraphDelimiterPut> ****)

(* NOTE: This function is not used anylonger; it used to be used by the Playbook stylesheet. *)

ParagraphDelimiterPut::usage = "ParagraphDelimiterPut[] either replaces the current cell of the Paragraph style with the delimiter cell or insert the delimiter cell at the current position."

ParagraphDelimiterPut[] := With[
  { obj = EvaluationCell[] },
  If[ FailureQ[obj],
    NotebookWrite[EvaluationNotebook[], $ParagraphDelimiter],
    If[ MemberQ[CurrentValue[obj, "CellStyle"], "ParagraphDelimiter"],
      Return[],
      NotebookWrite[EvaluationNotebook[], "~"]
    ]
  ]
]
(* NOTE: This must be consistent with the Playbook style sheet *)

(**** </ParagraphDelimiterPut> ****)


$ParagraphDelimiter::usage = "A horizontal delimiter cell like the one in the Wolfram documentation.\nCellPrint[$ParagraphDelimiter] put it in the evaluation notebook."

$ParagraphDelimiter = Cell[ "\t", "Text", "ParagraphDelimiter",
  TabFilling -> "\[LongDash]\[NegativeThickSpace]",
  TabSpacings -> Scaled[1],
  CellMargins -> {{Inherited, Inherited}, {Inherited, 10}},
  ShowCellBracket -> Automatic,
  CellGroupingRules -> {"SectionGrouping", 70},
  FontColor -> GrayLevel[0.85]
];


(**** <PlaybookDeploy> ****)

PlaybookDeploy::usage = "PlaybookDeploy[\"filename.nb\"] generates a public-release version \"filename.playbook.nb\" of source notebook \"filename.nb\".\nPlaybookDeploy[\"source.nb\", \"destination.nb\"] generates \"destination.nb\" for the public use.\nPlaybookDeploy[\"source.nb\", dir] generates dir/\"source.playbook.nb\" for the public use."

PlaybookDeploy::folder = "`` must be a valid folder."

PlaybookDeploy::nocopy = "Could not copy file `` to ``."

PlaybookDeploy::noopen = "Could not open file ``."

Options[PlaybookDeploy] = {
  "DeleteOutput" -> False,
  "PrintHandout" -> False,
  "FoldSections" -> True
}

PlaybookDeploy[opts:OptionsPattern[]] := With[
  { file = NotebookFileName[] },
  fileDeploy[file, playbookFileName @ file, opts]
 ]

PlaybookDeploy[file_String, opts:OptionsPattern[]] :=
  fileDeploy[file, playbookFileName @ file, opts]

PlaybookDeploy[file_String, dir_String, opts:OptionsPattern[]] :=
  fileDeploy[file, playbookFileName[file, dir], opts]


playbookFileName::usage = "playbookFileName[file] returns the file name of the deployed version of file."

playbookFileName[file_String] := Module[
  { dir, new },
  dir = DirectoryName[file];
  new = StringJoin @ {FileBaseName @ file, ".playbook.", FileExtension @ file};
  ExpandFileName @ If[dir == "", new, FileNameJoin @ {dir, new}]
 ]

playbookFileName[file_String, dst_String] :=
  If[ DirectoryQ[dst],
    playbookFileName @ FileNameJoin @ {dst, FileNameTake @ file},
    ExpandFileName[dst]
  ]


fileDeploy::usage = "fileDepoly[src, dst] does the actual job of deploying src to dst."

fileDeploy[src_String, dst_String, OptionsPattern[PlaybookDeploy]] := Module[
  { pdf, nb },
  Print["Deploying ", src];
  If[ FailureQ[nb = NotebookOpen[src]],
    Message[PlaybookDeploy::noopen, dst];
    Return[$Failed],
    NotebookSave[nb];
  ];
  
  Print["\tCopying to ", dst, " ..."];
  If[ FailureQ @ CopyFile[src, dst, OverwriteTarget -> True],
    Message[PlaybookDeploy::nocopy, src, dst];
    Return[$Failed]
  ];

  If[ FailureQ[nb = NotebookOpen[dst, Visible -> False]],
    Message[PlaybookDeploy::noopen, dst];
    Return[$Failed]
  ];

  Print["\tSetting the stylesheet to \"PlaybookNub.nb\" for printing (if at all) ..."];
  SetOptions[nb, StyleDefinitions -> "PlaybookNub.nb"];
  
  Print["\tSetting the banner as \"", $PlaybookBannerTitle, "\" for printing (if at all) ..."];
  SetBanner[nb, $PlaybookBannerTitle, "Deployed" -> True];
  (* NOTE: Even if the PlabybookNub stylesheet sets the banner, this line is still necessary because the user may want to set $PlaybookBannerTitle to a custom value. *)
  
  PlaybookTrim[nb];
  NotebookSave[nb];

  If[ OptionValue["PrintHandout"], PlaybookPrint[nb] ];
  
  If[ OptionValue["DeleteOutput"], PlaybookClean[nb] ];

  If[ OptionValue["FoldSections"],
    PlaybookFold[nb, {"Subsubsection", "Subsection", "Section"}]
  ];

  Print["\tSaving ", dst];
  SetOptions[nb, Visible -> True, Saveable -> False];
  NotebookSave[nb];
  NotebookClose[nb];
  Return[dst]
]

(**** </PlaybookDeploy> ****)


(**** <PlaybookCheckIn> ****)

PlaybookCheckIn::usage = "PlaybookCheckIn[] swiches the current notebook to the editting mode."

PlaybookCheckIn[] := With[
  { nb = EvaluationNotebook[] },
  NotebookDelete[EvaluationCell[]];
  SetOptions[nb, StyleDefinitions -> "Playbook.nb", Saveable -> True];
]


PlaybookCheckOut::usage = "PlaybookCheckOut[] swiches the current notebook to the deployed mode."

PlaybookCheckOut[] := With[
  { nb = EvaluationNotebook[] },
  NotebookDelete[EvaluationCell[]];
  SetOptions[nb, StyleDefinitions -> "PlaybookNub.nb", Saveable -> False];
  NotebookSave[nb];
]

(**** </PlaybookCheckIn> ****)



(**** <PlaybookPrint> ****)

PlaybookPrint::usage = "PlaybookPrint[nb] prints notebook nb to a PDF file."

PlaybookPrint[nb_NotebookObject] :=
  PlaybookPrint[nb, NotebookFileName @ nb]

PlaybookPrint[nb_NotebookObject, dst_String] := Module[
  { pdf },
  pdf = FileNameJoin @ {
    DirectoryName @ dst,
    StringJoin @ {FileBaseName @ dst, ".pdf"}
  };

  Print["\tPreparing ", NotebookFileName @ nb, " for printing ..."];
  (* Open all cell groups *)
  SelectionMove[nb, All, Notebook];
  FrontEndTokenExecute[nb, "SelectionOpenAllGroups"];
  SelectionMove[nb, Before, Notebook];
  NotebookSave[nb];

  Print["\tPrinting to ", pdf, " ..."];
  NotebookPrint[nb, pdf];

  Print["\t\t... done!"];
  Return[pdf]
]

(**** </PlaybookPrint> ****)


(**** <PlaybookFold> ****)

PlaybookFold::usage = "PlaybookFold[nb, styles] collapse all cell groups of styles in notebook nb."

PlaybookFold[nb_NotebookObject, style_String] := NotebookPut[
  ReplaceAll[
    NotebookGet[nb],
    CellGroupData[cc:{Cell[_, style, ___], ___Cell}, ___] :> 
      CellGroupData[cc, Closed]
   ],
  nb
 ]

PlaybookFold[nb_NotebookObject, styles:{__String}] :=
  Scan[PlaybookFold[nb, #]&, styles]

(**** </PlaybookFold> ****)


(**** <PlaybookClean> ****)

PlaybookClean::usage = "PlaybookClean[nb, styles] delete all cells of styles in notebook nb."

PlaybookClean[nb_NotebookObject, style_String:"Output"] := (
  Print["\tDeleting Cells of style ", style, " ..."];
  NotebookFind[nb, style, All, CellStyle, AutoScroll -> False];
  If[Length[SelectedCells @ nb] > 0, NotebookDelete[nb]]
 )

PlaybookClean[nb_NotebookObject, styles:{__String}] :=
  Scan[PlaybookClean[nb, #]&, styles]

(**** </PlaybookClean> ****)


(**** <PlaybookTrim> ****)

PlaybookTrim::usage = "PlaybookTrim[nb] deletes cells and cell groups with CellTags PlaybookEpilog.\nPlaybookTrim[nb, cell] deletes the particular cell or cell group."

PlaybookTrim[nb_NotebookObject] := (
  SelectionMove[nb, Before, Notebook, AutoScroll -> False];
  If[ FailureQ @
      NotebookFind[nb, "PlaybookEpilog", All, CellTags, AutoScroll -> False],
    Print["\tNo epilogue to delete!"];
    Return[],
    Print["\tExamining ", Length @ SelectedCells @ nb, " cell(s) in Epilog ..."];
    Scan[PlaybookTrim[nb, #]&, SelectedCells @ nb]
   ]
 )

PlaybookTrim[nb_NotebookObject, cell_CellObject] := With[
  { cc = (
      SelectionMove[cell, All, CellGroup, AutoScroll -> False];
      SelectedCells[nb]
    ) 
  },
  If[ First[CurrentValue[First @ cc, "CellStyle"]] == "Section",
    Print["\tDeleting ", Length @ cc, " cell(s) in Epilog ..."];
    NotebookDelete[cc],
    Print["\tDeleting the Epilog section head ..."];
    NotebookDelete[cell]
  ]
]

(**** </PlaybookTrim> ****)


(**** <PlaybookEpilog> ****)

PlaybookEpilog::usage = "PlaybookEpilog[nb] puts the Epilog section with CellTag \"PlaybookEpilog\" in notebook nb.\nPlaybookEpilog[] puts it in the selected notebook."

PlaybookEpilog[] := PlaybookEpilog @ SelectedNotebook[]

PlaybookEpilog[nb_NotebookObject] := Module[
  { cc },
  cc = Cell @ CellGroupData @ {
    Cell["Epilog", "Section", CellTags -> {"PlaybookEpilog"}],
    Cell[BoxData @ RowBox @ {"SetFolder", "[", "]"}, "Input"],
    Cell[BoxData @ RowBox @ {"PlaybookDeploy", "[", 
        RowBox @ {
          RowBox[{"\"\<PrintHandout\>\"", "->", "True"}], ",", " ", 
          RowBox[{"\"\<DeleteOutput\>\"", "->", "True"}], ",", " ", 
          RowBox[{"\"\<FoldSections\>\"", "->", "True"}]}, "]"}, "Input"],
    $ParagraphDelimiter,
    Cell[BoxData @ RowBox @ {"SystemOpen", "[", 
        RowBox[{"NotebookFolder", "[", "]"}], "]"}, "Input"]
  };
  NotebookDelete[EvaluationCell[]];
  NotebookWrite[nb, cc]
]

(**** </PlaybookEpilogy> ***)


(**** <PlaybookContents> ****)

PlaybookContents::usage = "PlaybookContents[] puts the table of contents of the selected notebook.\nIf there already exits the table of contents, then it replaces it with an updated one."

PlaybookContents[] := PlaybookContents @ SelectedNotebook[]

PlaybookContents[nb_NotebookObject] := Module[
  { cc, toc, obj },
  cc = PlaybookContentsLine @
    Cells[nb, CellStyle -> {"Section", "Subsection", "Subsubsection"}];
  If[cc == {}, Return[]];

  toc = Cell @ CellGroupData @
    Prepend[cc, Cell[$PlaybookContentsName, "OutlineSection"]];
  
  cc = Cells[ nb, CellStyle ->
      { "OutlineSection",
        "Outline1", "Outline2", "Outline3", "Outline4" } ];
  If[Length[cc] > 0, NotebookDelete[cc]];
  
  obj = First @ Cells[nb, CellStyle -> "Section"];
  SelectionMove[obj, Before, Cell];
  NotebookWrite[nb, toc];
 ]


PlaybookContentsLine::usage = "PlaybookContentsLine[cellObj] constructs a contents line in a button out of cellObj. If necessary, it sets the CellTags of cellObj with a unique tag."

PlaybookContentsLine::noid = "The cell has no ID. Turn on the CreateID option of the notebook."

SetAttributes[PlaybookContentsLine, Listable];

PlaybookContentsLine[obj_CellObject] := Cell[
  TextData @ ButtonBox[ theCellContents[obj],
    BaseStyle -> "Link",
    ButtonFunction -> (NotebookFind[SelectedNotebook[], #, All, CellID]&),
    ButtonData -> ToString@CurrentValue[obj, CellID] ],
  First[CurrentValue[obj, CellStyle]] /. theStyleMapping
 ]

theCellContents[obj_CellObject] := theCellContents[NotebookRead @ obj]

theCellContents[cell_Cell] := theCellContents[First @ cell]

theCellContents[in_TextData] := First[in]

theCellContents[in_] := in

theStyleMapping = {
  "Section" -> "Outline1",
  "Subsection" -> "Outline2",
  "Subsubsection" -> "Outline3"
 };

(**** </PlaybookContents> ****)


ToggleBanner::usage = "ToggleBanner[nb, title] toggles on or off the banner of notebook nb.\nToggleBanner[] applies to SelectedNoteboook[] with default banner $PlaybookBannerTitle."

ToggleBanner[title_String:$PlaybookBannerTitle, opts___?OptionQ] := Module[
  { nb = SelectedNotebook[],
    banner },
  banner = DockedCells /. Options[nb, DockedCells];
  If[ banner === {} || banner === None,
    SetBanner[nb, title, opts],
    UnsetBanner[nb, opts]
   ]
 ]



(**** <PlaybookBanner> ****)

$PlaybookBannerTitle::usage = "$PlaybookBannerTitle returns the title of the plaaybook banner."

$PlaybookBannerTitle = "Q3: Symbolic Quantum Simulation";


PlaybookBanner::usage = "PlaybookBanner[title] returns a cell to be used as the playbook banner."

Options[PlaybookBanner] = { "Deployed" -> False }

PlaybookBanner[title_String:$PlaybookBannerTitle, opts:OptionsPattern[{PlaybookBanner, Cell}]] := 
  If[ OptionValue["Deployed"],
    (* for readers *)
    Module[
      { logo, data },
      logo = Thumbnail[
        Import[PacletObject["Q3"]["AssetLocation", "Q3 Emblem Medium"]],
        Medium
      ];
      data = RowBox @ {ToBoxes @ logo, "|", "  ", title};
      Cell[ BoxData[data], "DockedCell",
        FilterRules[{opts}, Options[Cell]],
        CellFrameMargins -> {{22, 0}, {0, 0}},
        Background -> GrayLevel[0.9],
        FontVariations -> {"CapsType" -> "SmallCaps"},
        FontSize -> 14
      ]
    ],
    (* for authors *)
    Cell[ title, "DockedCell",
      FilterRules[{opts}, Options[Cell]],
      CellFrameMargins -> {{22, 8}, {12, 12}},
      Background -> GrayLevel[0.9],
      FontVariations -> {"CapsType" -> "SmallCaps"},
      FontSize -> 14
    ]
  ]

(**** </PlaybookBanner> ****)


(**** <SetBanner> ****)

SetBanner::usage = "SetBanner[\"title\"] adds a banner of \"title\" to the top of the current notebook by setting the DockedCells option.\nSetBanner has the same options as Cell."

SetBanner[file_String, title_String, opts___?OptionQ] :=
  SetBanner[NotebookOpen[file], title, opts]

SetBanner[title_String:$PlaybookBannerTitle, opts___?OptionQ] :=
  SetBanner[EvaluationNotebook[], title, opts]

SetBanner[nb_NotebookObject, title_String:$PlaybookBannerTitle, opts___?OptionQ] :=
  SetOptions[
    nb, 
    DockedCells -> PlaybookBanner[title, opts],
    PageFooters -> {
      { Cell[$PlaybookBannerTitle, "Footer", CellMargins -> 4], None, None },
      { None, None, Cell[$PlaybookBannerTitle, "Footer", CellMargins -> 4] }
    },
    PageFooterLines -> {True, True}
  ]


UnsetBanner::usage = "UnsetBanner[] removes the banner of the current notebook."

UnsetBanner[] := UnsetBanner @ EvaluationNotebook[]

UnsetBanner[file_String] := UnsetBanner @ NotebookOpen[file]

UnsetBanner[nb_NotebookObject] := SetOptions[nb, DockedCells -> {}]

(**** </SetBanner> ****)


SetAttributes[Evaluate @ Names["`*"], ReadProtected];

End[]


SetAttributes[Evaluate @ Protect["`*"], ReadProtected];

(* Users are allowed to change variables. *)
Unprotect["`$*"];

(* Too dangerous to allow users to change these. *)
Protect[$ParagraphDelimiter];

EndPackage[]
