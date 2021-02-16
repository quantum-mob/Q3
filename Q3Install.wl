(* -*- mode:math -*- *)
(* Mahn-Soo Choi *)
(* $Date: 2021-02-16 11:42:21+09 $ *)
(* $Revision: 1.2 $ *)


Q3Install[opts___?OptionQ] := Module[
  { jsn, url },

  jsn = Import[
    "https://api.github.com/repos/quantum-mob/Q3App/releases/latest", 
    "JSON"
   ];
  url = Lookup[First @ Lookup[jsn, "assets"], "browser_download_url"];
  
  Print["Installing Q3 directly from GitHub. It may take serveral minutes or longer depending on your network conditions and your computer. Please be patient."];
  
  PacletInstall[url, opts]
 ]
