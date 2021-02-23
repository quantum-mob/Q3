(* -*- mode:math -*- *)
(* Mahn-Soo Choi *)
(* $Date: 2021-02-22 10:00:17+09 $ *)
(* $Revision: 1.3 $ *)


Module[
  { jsn, url },

  jsn = Import[
    "https://api.github.com/repos/quantum-mob/Q3App/releases/latest", 
    "JSON"
   ];
  url = Lookup[First @ Lookup[jsn, "assets"], "browser_download_url"];
  
  Print["Installing Q3 directly from GitHub. It may take serveral minutes or longer depending on your network conditions and your computer. Please be patient."];
  
  PacletInstall[url]
 ]
