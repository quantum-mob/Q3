(* -*- mode:math -*- *)
(* Mahn-Soo Choi *)
(* $Date: 2023-06-20 11:47:08+09 $ *)
(* $Revision: 1.24 $ *)

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
  Visible -> False,
  StyleDefinitions -> "Playbook.nb"
 ];


PlaybookDeploy::usage = "PlaybookDeploy[filename] saves the notebook specified by the filename in the playbooks folder with proper options."

PlaybookDeploy::baddst = "Unrecognized destinatoin ``."

PlaybookDeploy::nocopy = "Could not copy file `` to ``."

PlaybookDeploy::noopen = "Could not open file ``."

Options[PlaybookDeploy] = {
  "Destination" -> Automatic,
  "DeleteOutput" -> False,
  "PrintHandout" -> False,
  "CollapseGroup" -> False
 }

PlaybookDeploy[opts:OptionsPattern[]] :=
  PlaybookDeploy[NotebookFileName[], OptionValue @ "Destination", opts]

PlaybookDeploy[file_String, opts:OptionsPattern[]] :=
  PlaybookDeploy[file, OptionValue @ "Destination", opts]

PlaybookDeploy[file_String, dst_, OptionsPattern[]] := Module[
  { new, pdf, nb },
  new = ExpandFileName @ Which[
    dst === Automatic,
    FileNameJoin @ DeleteCases[
      { DirectoryName[file],
        StringJoin @ {FileBaseName[file], ".Playbook.nb"} },
      "" ],
    DirectoryQ[dst],
    FileNameJoin @ {dst, FileNameTake @ file},
    StringQ[dst], dst,
    True, Message[Playbook::baddst, dst]; Return[$Failed]
   ];
  Print[file, " --> ", new];

  If[ FailureQ @ CopyFile[file, new, OverwriteTarget -> True],
    Message[PlaybookDeploy::nocopy, file, new];
    Return[$Failed]
   ];

  If[ FailureQ[nb = NotebookOpen @ new],
    Message[PlaybookDeploy::noopen, new];
    Return[$Failed]
   ];

  SetBanner[nb, $PlaybookBanner];
  DeleteEpilogue[nb];
  If[ OptionValue["DeleteOutput"],
    CleanNotebook[nb] ];
  If[ OptionValue["CollapseGroup"],
    CollapseGroup[nb, {"Subsubsection", "Subsection", "Section"}] ];
  SetOptions[nb, Saveable -> False, StyleDefinitions -> $PlaybookStyle];
  NotebookSave[nb, new];
  If[ OptionValue["PrintHandout"],
    SelectionMove[nb, All, Notebook];
    FrontEndTokenExecute[nb, "SelectionOpenAllGroups"];
    pdf = StringJoin @ {
      FileNameJoin @ {DirectoryName @ new, FileBaseName @ new},
      ".pdf"
     };
    Print[file, " --> ", pdf];
    Export[pdf, nb]
   ];
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


DeleteEpilogue::usage = "DeleteEpilogue[nb] deletes cells and cell groups with CellTags PlaybookEpilogue.\nDeleteEpilogue[nb, cell] deletes the particular cell or cell group."

DeleteEpilogue[nb_NotebookObject] := (
  Echo[NotebookFileName @ nb];
  If[ FailureQ @ NotebookFind[nb, "PlaybookEpilogue", All, CellTags],
    Echo["No epilogue to delete!"];
    Return[],
    Echo[SelectedCells @ nb, "Checking"];
    Scan[DeleteEpilogue[nb, #]&, SelectedCells @ nb]
   ]
 )

DeleteEpilogue[nb_NotebookObject, cell_CellObject] := With[
  { cc = (SelectionMove[cell, All, CellGroup]; SelectedCells[nb]) },
  If[ First[CurrentValue[First @ cc, "CellStyle"]] == "Section",
    Echo[cc, "Being deleted"];
    NotebookDelete[cc],
    Echo[cell, "Being deleted"];
    NotebookDelete[cell]
   ]
 ]

(**** </PlaybookDeploy> ****)


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
