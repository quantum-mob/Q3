(* ::Package:: *)

PacletObject[
  <|
    "Name" -> "QuantumMob/Q3",
    "PrimaryContext" -> "QuantumMob`Q3`",
    "Description" -> "A symbolic quantum simulation framework on quantum information systems, quantum many-body systems, and quantum spin systems",
    "Creator" -> "Mahn-Soo Choi",
    "PublisherID" -> "QuantumMob",
    "License" -> "GPL-3.0-only",
    "Version" -> "4.2.0",
    "WolframVersion" -> "13.1+",
    "Updating" -> "Automatic",
    "Loading" -> "Startup",
    (* "Loading" -> "Automatic", *)
    "Extensions" -> {
      {
        "Kernel",
        "Root" -> "Kernel",
        "Context" -> {"QuantumMob`Q3`"},
        "Symbols" -> {
          "QuantumMob`Q3`Q3Assure",
          "QuantumMob`Q3`Q3CheckUpdate",
          "QuantumMob`Q3`Q3Info",
          "QuantumMob`Q3`Q3Purge"
        }
      },
      {
        "Documentation",
        "Language" -> "English",
        "MainPage" -> "Guides/Q3"
      },
      {
        "FrontEnd",
        "Prepend" -> True 
      },
      {
        "Asset",
        "Root" -> "Asset/Images",
        "Assets" -> {
          {"Q3 Emblem Medium", "EmblemQ3M.png"},
          {"Q3 Emblem Small", "EmblemQ3S.png"},
          {
            "Q3 Emblem Black Medium",
            "EmblemQ3BlackM.jpg"
          },
          {
            "Q3 Emblem Black Small",
            "EmblemQ3BlackS.jpg"
          }
        }
      }
    },
    "Category" -> {"Physics", "Quantum Physics"},
    "Keywords" -> {
      "quantum computation",
      "quantum information",
      "quantum many-body systems",
      "quantum spins"
    },
    "URL" -> "https://github.com/quantum-mob/Q3",
    "Support" -> "quantum.mob21@gmail.com"
  |>
]
