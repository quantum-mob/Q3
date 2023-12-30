(* -*- mode:math -*- *)
(* Mahn-Soo Choi *)
(* $Date: 2023-12-21 23:22:22+09 $ *)
(* $Revision: 1.49 $ *)

BeginPackage["PlaybookTools`"]

Unprotect["`*"];
ClearAll["`*"];

{ PlaybookDeploy,
  $PlaybookBanner = "Q3: Symbolic Quantum Simulation" };

{ ParagraphDelimiterPut,
  $ParagraphDelimiter };

(* See also MakeContents from AuthorTools`. *)
{ PlaybookContents,
  PlaybookContentsLine,
  $PlaybookContentsName = "Table of Contents" };

{ PlaybookEpilog };

{ ToggleBanner, SetBanner, UnsetBanner };


Begin["`Private`"]

ClearAll["`*"];


(**** <ParagraphDelimiterPut> ****)

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


$ParagraphDelimiter::usage = "A horizontal delimiter cell like the one in the Wolfram documentation.\nCellPrint[$ParagraphDelimiter] put it in the evaluation notebook."

$ParagraphDelimiter = Cell[ "\t", "Text", "ParagraphDelimiter",
  TabFilling -> "\[LongDash]\[NegativeThickSpace]",
  TabSpacings -> Scaled[1],
  CellMargins -> {{Inherited, Inherited}, {Inherited, 10}},
  ShowCellBracket -> Automatic,
  CellGroupingRules -> {"SectionGrouping", 70},
  FontColor -> GrayLevel[0.85]
 ];

(**** </ParagraphDelimiterPut> ****)


(**** <PlaybookDeploy> ****)

Uneditable::usage = "Uneditable[style] makes cells of style uneditable.";

SetAttributes[Uneditable, Listable]

Uneditable[style_String, more___?OptionQ] := 
  Cell[StyleData[style], Editable -> False, more]


$PlaybookStyle::usage =  "$PlaybookStyle returns the style definition of a playbook to be deployed.";

$PlaybookStyle = Notebook[
  Join[
    List @ Cell @ StyleData[StyleDefinitions -> "Playbook.nb"],
    Uneditable @ {
      "Title", "Subtitle", "Chapter",
      "Section", "Subsection", "Subsubsection",
      "Text", "Code", "Item", "Subitem", "Subsubitem",
      "DisplayFormula", "Picture", "Caption",
      "OutlineSection", "Outline1", "Outline2", "Outline3", "Outline4" }
   ],
  StyleDefinitions -> "Playbook.nb"
 ];


PlaybookDeploy::usage = "PlaybookDeploy[filename] saves the notebook specified by the filename in the playbooks folder with proper options."

PlaybookDeploy::folder = "`` must be a valid folder."

PlaybookDeploy::nocopy = "Could not copy file `` to ``."

PlaybookDeploy::noopen = "Could not open file ``."

Options[PlaybookDeploy] = {
  "DeleteOutput" -> False,
  "PrintHandout" -> False,
  "FoldSections" -> False
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
  new = StringJoin @ {FileBaseName @ file, ".Playbook.", FileExtension @ file};
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
  
  Print["Copying to ", dst];
  If[ FailureQ @ CopyFile[src, dst, OverwriteTarget -> True],
    Message[PlaybookDeploy::nocopy, src, dst];
    Return[$Failed]
   ];

  If[ FailureQ[nb = NotebookOpen[dst, Visible -> False]],
    Message[PlaybookDeploy::noopen, dst];
    Return[$Failed]
   ];

  SetBanner[nb, $PlaybookBanner];
  DeleteEpilog[nb];

  If[ OptionValue["PrintHandout"], PlaybookPrint[nb] ];
  
  If[ OptionValue["DeleteOutput"], PlaybookClean[nb] ];

  If[ OptionValue["FoldSections"],
    PlaybookFold[nb, {"Subsubsection", "Subsection", "Section"}]
   ];

  Print["Saving ", dst];
  SetOptions[ nb,
    Visible -> True,
    Saveable -> False,
    StyleDefinitions -> $PlaybookStyle ];
  NotebookSave[nb];
  NotebookClose[nb];
 ]


PlaybookPrint::usage = "PlaybookPrint[nb] prints notebook nb to a PDF file."

PlaybookPrint[nb_NotebookObject] :=
  PlaybookPrint[nb, NotebookFileName @ nb]

PlaybookPrint[nb_NotebookObject, dst_String] := Module[
  { pdf },
  pdf = FileNameJoin @ {
    DirectoryName @ dst,
    StringJoin @ {FileBaseName @ dst, ".pdf"}
   };
  Print["Printing to ", pdf, "..."];
  (* For some unknown reason, the following two lines are required;
     otherwise, NotebookPrint misses some images and typographic math
     expressions. *)
  SetOptions[nb, Visible -> True, StyleDefinitions -> $PlaybookStyle];

  (* Open all cell groups *)
  SelectionMove[nb, All, Notebook];
  FrontEndTokenExecute[nb, "SelectionOpenAllGroups"];

  NotebookSave[nb];
  (* For some unknown reason, TaskWait is required; otherwise, NotebookPrint
     misses some images and typographic math expressions. *)
  TaskWait @ SessionSubmit @ NotebookPrint[nb, pdf];
  Print["\t... done!"];
 ]


PlaybookClean::usage = "PlaybookClean[nb, styles] delete all cells of styles in notebook nb."

PlaybookClean[nb_NotebookObject, style_String:"Output"] := (
  Print["Deleting Cells of style ", style];
  NotebookFind[nb, style, All, CellStyle, AutoScroll -> False];
  If[Length[SelectedCells @ nb] > 0, NotebookDelete[nb]]
 )

PlaybookClean[nb_NotebookObject, styles:{__String}] :=
  Scan[PlaybookClean[nb, #]&, styles]


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


DeleteEpilog::usage = "DeleteEpilog[nb] deletes cells and cell groups with CellTags DeleteEpilog.\nDeleteEpilog[nb, cell] deletes the particular cell or cell group."

DeleteEpilog[nb_NotebookObject] := (
  SelectionMove[nb, Before, Notebook, AutoScroll -> False];
  (* Print["Examinig ", NotebookFileName @ nb]; *)
  (* For some unknown reason, the above line or similar is
     necessary. Otherwise, NotebookFind below does not work properly. *)
  If[ FailureQ @
      NotebookFind[nb, "PlaybookEpilog", All, CellTags, AutoScroll -> False],
    Print["No epilogue to delete!"];
    Return[],
    Print["Examining ", SelectedCells @ nb, " for deletion."];
    Scan[DeleteEpilog[nb, #]&, SelectedCells @ nb]
   ]
 )

DeleteEpilog[nb_NotebookObject, cell_CellObject] := With[
  { cc = (
      SelectionMove[cell, All, CellGroup, AutoScroll -> False];
      SelectedCells[nb] ) },
  If[ First[CurrentValue[First @ cc, "CellStyle"]] == "Section",
    Print["Deleting ", cc];
    NotebookDelete[cc],
    Print["Deleting ", cell];
    NotebookDelete[cell]
   ]
 ]

(**** </PlaybookDeploy> ****)


(**** <PlaybookEpilog> ****)

PlaybookEpilog::usage = "PlaybookEpilog[nb] puts the Epilog section with CellTag \"PlaybookEpilog\" in notebook nb.\nPlaybookEpilog[] puts it in the selected notebook."

PlaybookEpilog[] := PlaybookEpilog @ SelectedNotebook[]

PlaybookEpilog[nb_NotebookObject] := Module[
  { cc },
  cc = Cell @ CellGroupData @ {
    Cell["Epilog", "Section", CellTags -> {"PlaybookEpilog"}],
    Cell[BoxData @ RowBox @ {"WorkHere", "[", "]"}, "Input"],
    Cell[BoxData @ RowBox @ {"PlaybookDeploy", "[", 
        RowBox @ {
          RowBox[{"\"\<PrintHandout\>\"", "->", "True"}], ",", " ", 
          RowBox[{"\"\<DeleteOutput\>\"", "->", "True"}], ",", " ", 
          RowBox[{"\"\<FoldSections\>\"", "->", "True"}]}, "]"}, "Input"],
    $ParagraphDelimiter,
    Cell[BoxData @ RowBox @ {"SystemOpen", "[", 
        RowBox[{"NotebookFolder", "[", "]"}], "]"}, "Input"]
   };
  NotebookWrite[nb, cc];
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


SetAttributes[Evaluate @ Names["`*"], ReadProtected];

End[]


SetAttributes[Evaluate @ Protect["`*"], ReadProtected];

(* Users are allowed to change variables. *)
Unprotect["`$*"];

(* Too dangerous to allow users to change these. *)
Protect[$ParagraphDelimiter];

EndPackage[]
