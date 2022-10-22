(* Paclet Info File *)
(* $Date: 2022-10-20 22:24:54+09 $ *)
(* $Revision: 2.91 $ *)

Paclet[
  "Name" -> "Q3",
  "Version" -> "2.7.10",
  "WolframVersion" -> "12.1+",
  "Updating" -> Automatic,
  "Extensions" -> {
    { "Kernel",
      "Root" -> "Kernel",
      "Context" -> { "Q3`" }
      (* Context specifies the package context or list of contexts.
         The list is also used by FindFile.
         The list also causes documentation links to be added to usage
         messages when documentation is present. *)
     },
    { "Documentation",
      "Language" -> "English",
      "MainPage" -> "Guides/Q3" },
    { "FrontEnd",
      "Prepend" -> True }
    (* Enables subdirectories within the FrontEnd to be handled,
       e.g. FrontEnd/Palettes, FrontEnd/StyleSheets, FrontEnd/SystemResources,
       FrontEnd/TextResources. These items will be recognized by the Front
       End, e.g. palettes will show up in the Palettes menu. *)
   },
  "Description" -> "Mathematica application to help study quantum information processing, quantum many-body systems, and quantum spin systems",
  "Creator" -> "Mahn-Soo Choi (Korea University)",
  "URL" -> "https://github.com/quantum-mob/Q3",
  "Category" -> { "Physics", "Quantum Physics" },
  "Keywords" -> { "quantum information", "quantum computation",
    "quantum many-body systems", "quantum spins" },
  "Support" -> "quantum.mob21@gmail.com"
 ]
