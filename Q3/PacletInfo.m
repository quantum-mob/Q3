(* Paclet Info File *)

(* created 2021/02/11*)

Paclet[
  Name -> "Q3",
  Version -> "1.6.7",
  WolframVersion -> "12+",
  MathematicaVersion -> "12+",
  Description -> "Mathematica application to help study quantum information processing, quantum many-body systems, and quantum spin systems.",
  Creator -> "Mahn-Soo Choi (Korea University)",
  Extensions -> {
    { "Documentation",
      Language -> "English" },
    { "Kernel",
      Root -> ".",
      Context -> {
        "Q3`", "Q3`Cauchy`", "Q3`Pauli`", "Q3`Grassmann`",
        "Q3`Quisso`", "Q3`Fock`", "Q3`Wigner`"
       }
      (* Context specifies the package context or list of contexts . Used by
         FindFile. Also causes documentation links to be added to usage
         messages when documentation is present. *)
     }
   },
  URL -> "https://github.com/quantum-mob/Q3App",
  Category -> "Physics",
  Keywords -> {
    "Quantum Computation",
    "Quantum Many-Body Systems",
    "Quantum Spins"
   }
]


