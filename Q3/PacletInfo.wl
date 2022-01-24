(* Paclet Info File *)
(* $Date: 2022-01-19 08:16:18+09 $ *)
(* $Revision: 2.19 $ *)

Paclet[
  "Name" -> "Q3",
  "Version" -> "2.3.4",
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
      "MainPage" -> "Guides/Q3" }
   },
  "Description" -> "Mathematica application to help study quantum information processing, quantum many-body systems, and quantum spin systems",
  "Creator" -> "Mahn-Soo Choi (Korea University)",
  "URL" -> "https://github.com/quantum-mob/Q3",
  "Category" -> { "Physics", "Quantum Physics" },
  "Keywords" -> { "quantum information", "quantum computation",
    "quantum many-body systems", "quantum spins" },
  "Support" -> "quantum.mob21@gmail.com"
 ]
