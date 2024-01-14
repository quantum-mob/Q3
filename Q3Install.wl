(* -*- mode:math -*- *)
(* Mahn-Soo Choi *)
(* $Date: 2021-04-04 11:07:47+09 $ *)
(* $Revision: 2.1 $ *)

Module[
  { ps },
  ps = PacletSiteRegister[
    "https://github.com/quantum-mob/PacletRepository/raw/main",
    "Quantum Mob Paclet Server"
   ];
  PacletSiteUpdate[ps];
  PacletInstall["Q3"]
 ]
