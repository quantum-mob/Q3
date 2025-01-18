Paclet[
  "Name" -> "Q3",
  "Version" -> "3.8.2",
  "WolframVersion" -> "12.3+",
  "Updating" -> Automatic,
  "Loading" -> "Startup",
  "Extensions" -> {
    { "Kernel",
      "Root" -> "Kernel",
      "Context" -> { "Q3`" },
      (* Context specifies the package context or list of contexts.
         The list is also used by FindFile.
         The list also causes documentation links to be added to usage
         messages when documentation is present. *)
      "Symbols" -> { "Let", "Q3Info", "Q3CheckUpdate", "Q3Update", "Q3Assure" }
      (* Symbols supplies a set of symbols that the paclet provides. If the
         Loading is set to Automatic, autoloading will be set up for everyone
         of these symbols. *)
    },
    { "Kernel",
      "Root" -> "PlaybookTools/Kernel",
      "Context" -> { "PlaybookTools`" },
      (* Context specifies the package context or list of contexts.
         The list is also used by FindFile.u
         The list also causes documentation links to be added to usage
         messages when documentation is present. *)
      "Symbols" -> { "ParagraphDelimiterPut", "$ParagraphDelimiter" }
      (* Symbols supplies a set of symbols that the paclet provides. If the
         Loading is set to Automatic, autoloading will be set up for everyone
         of these symbols. *)
    },
    { "Documentation",
      "Language" -> "English",
      "MainPage" -> "Tutorials/Q3QuickStart" },
    { "FrontEnd",
      "Prepend" -> True },
    (* Enables subdirectories within the FrontEnd to be handled,
       e.g. FrontEnd/Palettes, FrontEnd/StyleSheets, FrontEnd/SystemResources,
       FrontEnd/TextResources. These items will be recognized by the Front
       End, e.g. palettes will show up in the Palettes menu. *)
    { "Asset",
      (* Similar to the old-style Resource extension. *)
      (* The documented way to extract the named asset from Asset extensions
         is pacletObj["AssetLocation", "assetname"]. *)
      "Root" -> "Assets/Images",
      "Assets" -> {
        {"Q3 Emblem Medium", "EmblemQ3M.png"},
        {"Q3 Emblem Small",  "EmblemQ3S.png"},
        {"Q3 Emblem Black Medium", "EmblemQ3BlackM.jpg"},
        {"Q3 Emblem Black Small",  "EmblemQ3BlackS.jpg"}
      }
    }
  },
  "Description" -> "A Wolfram Language framework for quantum symbolic simulations on quantum information systems, quantum many-body systems, and quantum spin systems. First released to the public in 2020.",
  "Creator" -> "Mahn-Soo Choi (Korea University)",
  "URL" -> "https://github.com/quantum-mob/Q3",
  "Category" -> { "Physics", "Quantum Physics" },
  "Keywords" -> { "quantum information", "quantum computation",
    "quantum many-body systems", "quantum spins" },
  "Support" -> "quantum.mob21@gmail.com"
]
