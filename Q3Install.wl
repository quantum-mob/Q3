(* -*- mode:math -*- *)
(* Mahn-Soo Choi *)
(* $Date: 2021-04-04 03:48:50+09 $ *)
(* $Revision: 2.0 $ *)

Module[
  { ps },
  ps = PacletSiteRegister[
    "https://github.com/quantum-mob/PacletServer/raw/main",
    "Quamtum Mob Paclet Server"
   ];
  PacletSiteUpdate[ps];
  PacletInstall["Q3"]
 ]
