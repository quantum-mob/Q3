(* -*- mode:math -*- *)
(* Mahn-Soo Choi *)
(* $Date: 2023-03-12 21:32:20+09 $ *)
(* $Revision: 1.3 $ *)

BeginPackage["Q3`"]

{ PlaybookDeploy,
  $PlaybookBanner = "Quantum Playbook" };


{ InsertParagraphDelimiter,
  $ParagraphDelimiter };


{ ToggleBanner, SetBanner, UnsetBanner };


Begin["`Private`"]

(**** <InsertParagraphDelimiter> ****)

InsertParagraphDelimiter::usage = "InsertParagraphDelimiter[] either replaces the current cell of the Paragraph style with the delimiter cell or insert the delimiter cell at the current position."

InsertParagraphDelimiter[] := With[
  { obj = EvaluationCell[] },
  If[ FailureQ[obj],
    NotebookWrite[EvaluationNotebook[], $ParagraphDelimiter],
    If[ MemberQ[CurrentValue[obj, "CellStyle"], "ParagraphDelimiter"],
      Return[],
      NotebookWrite[EvaluationNotebook[], "\t"]
     ]
   ]
 ]
(* NOTE: This must be consistent with the Playbook style sheet *)


$ParagraphDelimiter::usage = "A horizontal delimiter cell like the one in the Wolfram documentation.\nCellPrint[$ParagraphDelimiter] put it in the evaluation notebook."

$ParagraphDelimiter = Cell[ "\t", "Text", "ParagraphDelimiter",
  TabFilling -> "\[LongDash]\[NegativeThickSpace]",
  TabSpacings -> Scaled[1],
  CellMargins -> {{Inherited, Inherited}, {Inherited, 10}},
  ShowCellBracket -> Automatic,
  CellGroupingRules -> {"SectionGrouping", 70},
  FontColor -> GrayLevel[0.85]
 ];

(**** </InsertParagraphDelimiter> ****)


(**** <PlaybookDeploy> ****)

Uneditable::usage = "Uneditable[style] makes cells of style uneditable.";

SetAttributes[Uneditable, Listable]

Uneditable[style_String, more___?OptionQ] := 
  Cell[StyleData[style], Editable -> False, more]


$PlaybookStyle::usage =  "$PlaybookStyle returns the style definition of a playbook to be deployed.";

$PlaybookStyle = Notebook[
  Join[
    List @ Cell @ StyleData[StyleDefinitions -> "Default.nb"],
    Uneditable @ {
      "Title", "Subtitle", "Chapter",
      "Section", "Subsection", "Subsubsection",
      "Text", "Code", "Item", "Subitem", "Subsubitem",
      "DisplayFormula" },
    { Cell[
        StyleData["ParagraphDelimiter", StyleDefinitions -> StyleData["Text"]],
        Editable -> False,
        Evaluatable -> False ],
      Cell[ StyleData["Picture"],
        CellMargins -> {{80, 10}, {7, 7}},
        Editable -> False,
        PageWidth -> Infinity,
        PageBreakBelow -> False,
        CellGroupingRules -> "GraphicsGrouping",
        CellHorizontalScrolling -> True,
        GraphicsBoxOptions -> {ImageSize -> Medium},
        Graphics3DBoxOptions -> {ImageSize -> Medium} ],
      Cell[ StyleData["Picture", "Printout"],
        PageWidth -> PaperWidth,
        CellMargins -> {{73, Inherited}, {Inherited, 5}},
        Magnification -> 0.65 ],
      Cell[ StyleData["Caption"],
        CellMargins -> {{66, 10}, {7, 3}},
        Editable -> False,
        CellGroupingRules -> "GraphicsGrouping",
        PageBreakAbove -> False,
        FontFamily -> "Verdana",
        FontSize -> 11 ]
     }
   ],
  Visible -> False,
  StyleDefinitions -> "Default.nb"
 ];


PlaybookDeploy::usage = "PlaybookDeploy[filename] saves the notebook specified by the filename in the playbooks folder with proper options."

PlaybookDeploy::nocopy = "Could not copy file `` to ``."

PlaybookDeploy::noopen = "Could not open file ``."

PlaybookDeploy::nosty = "Could not find a style sheet of ``."

Options[PlaybookDeploy] = {
  "Destination" -> FileNameJoin @
    {$HomeDirectory, "Math/Apples/QuantumPlaybook/Chapters"},
  "DeleteOutput" -> False,
  "CollapseGroup" -> False
 }

PlaybookDeploy[file_String, OptionsPattern[]] := Module[
  { dst = OptionValue["Destination"],
    new, nb },
  new = FileNameJoin @ {dst, FileNameTake[file]};

  Print["Copying ", file, " to ", dst, "/ ..."];

  If[ FailureQ @ CopyFile[file, new, OverwriteTarget -> True],
    Message[PlaybookDeploy::nocopy, file, new];
    Return[$Failed]
   ];

  If[ FailureQ[nb = NotebookOpen @ new],
    Message[PlaybookDeploy::noopen, new];
    Return[$Failed]
   ];

  SetBanner[nb, $PlaybookBanner];
  If[OptionValue["DeleteOutput"], CleanNotebook[nb]];
  If[OptionValue["CollapseGroup"],
    CollapseGroup[nb, {"Subsubsection", "Subsection", "Section"}]];
  SetOptions[nb, Saveable -> False, StyleDefinitions -> $PlaybookStyle];
  NotebookSave[nb, new];
  NotebookClose[nb];
 ]


CleanNotebook::usage = "CleanNotebook[nb, styles] delete all cells of styles in notebook nb."

CleanNotebook[nb_NotebookObject, style_String:"Output"] :=
  ( NotebookFind[nb, style, All, CellStyle];
    NotebookDelete[nb] )

CleanNotebook[nb_NotebookObject, styles:{__String}] :=
  Scan[CleanNotebook[nb, #]&, styles]


CollapseGroup::usage = "CollapseGroup[nb, styles] collapse all cell groups of styles in notebook nb."

CollapseGroup[nb_NotebookObject, style_String:"Section"] :=
  ( NotebookFind[nb, style, All, CellStyle];
    FrontEndTokenExecute[nb, "OpenCloseGroup"] )

CollapseGroup[nb_NotebookObject, styles:{__String}] :=
  Scan[CollapseGroup[nb, #]&, styles]

(**** </PlaybookDeploy> ****)


ToggleBanner::usage = "ToggleBanner[nb, title] toggles on or off the banner of notebook nb.\nToggleBanner[] applies to SelectedNoteboook[] with default banner $PlaybookBanner."

ToggleBanner[title_String:$PlaybookBanner, opts___?OptionQ] := Module[
  { nb = SelectedNotebook[],
    banner },
  banner = DockedCells /. Options[nb, DockedCells];
  If[ banner === {} || banner === None,
    SetBanner[nb, title, opts],
    UnsetBanner[nb, opts]
   ]
 ]


SetBanner::usage = "SetBanner[\"title\"] adds a banner of \"title\" to the top of the current notebook by setting the DockedCells option.\nSetBanner has the same options as Cell."

SetBanner[file_String, title_String, opts___?OptionQ] :=
  SetBanner[NotebookOpen[file], title, opts]

SetBanner[title_String:$PlaybookBanner, opts___?OptionQ] :=
  SetBanner[EvaluationNotebook[], title, opts]

SetBanner[nb_NotebookObject, title_String:$PlaybookBanner, opts___?OptionQ] :=
  SetOptions[
    nb, 
    DockedCells -> Cell[
      title, "Text", opts,
      Background -> GrayLevel[0.9],
      FontSize -> 12,
      CellFrameMargins -> {{22, 8}, {8, 8}}
     ],
    PageFooters -> {
      { Cell[$PlaybookBanner, "Footer", CellMargins -> 4], None, None },
      { None, None, Cell[$PlaybookBanner, "Footer", CellMargins -> 4] }
     },
    PageFooterLines -> {True, True}
   ]


UnsetBanner::usage = "UnsetBanner[] removes the banner of the current notebook."

UnsetBanner[] := UnsetBanner @ EvaluationNotebook[]

UnsetBanner[file_String] := UnsetBanner @ NotebookOpen[file]

UnsetBanner[nb_NotebookObject] := SetOptions[nb, DockedCells -> {}]

End[]

EndPackage[]
