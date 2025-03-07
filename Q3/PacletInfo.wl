(* ::Package:: *)

PacletObject[
  <|
    "Name" -> "QuantumMob/Q3",
    "PrimaryContext" -> "QuantumMob`Q3`",
    "Description" -> "A symbolic quantum simulation framework on quantum information systems, quantum many-body systems, and quantum spin systems",
    "Creator" -> "Mahn-Soo Choi",
    "URL" -> "https://github.com/quantum-mob/Q3",
    "License" -> "GPL-3.0-only",
    "PublisherID" -> "QuantumMob",
    "Version" -> "4.1.1",
    "WolframVersion" -> "13.1+",
    "Updating" -> "Automatic",
    "Loading" -> "Startup",
    (* "Loading" -> "Automatic", *)
    "Category" -> {"Physics", "Quantum Physics"},
    "Extensions" -> {
      {
        "Kernel",
        "Root" -> "Kernel",
        "Context" -> {"QuantumMob`Q3`"},
        "Symbols" -> {
          "QuantumMob`Q3`Q3Assure",
          "QuantumMob`Q3`Q3CheckUpdate",
          "QuantumMob`Q3`Q3Info",
          "QuantumMob`Q3`Q3Release",
          "QuantumMob`Q3`Q3RemoteRelease",
          "QuantumMob`Q3`Q3Update"
        }
      },
      {
        "Documentation",
        "Language" -> "English",
        "MainPage" -> "Guides/Q3"
      },
      {"FrontEnd", "Prepend" -> True},
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
    "Keywords" -> {
      "quantum computation",
      "quantum information",
      "quantum many-body systems",
      "quantum spins"
    },
    "Support" -> "quantum.mob21@gmail.com"
  |>
]
