# Installation Guide

## Automatic Installation

```Mathematica
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
```

## Semi-Automatic Installation


## Manual Installation

1. Download the whole folder as a ZIP file.

2. Unzip the ZIP file to extract the files and subfolders.

3. Move (or copy) the folder Q3 to either

   ```
   $UserBaseDirectory/Applications/ (recommended)
   ```

   or
   
   ```
   $BaseDirectory/Applications/
   ```

   Here `$UserBaseDirectory` is the Mathematica(R) symbol, the value of which you can check on your Mathematica.

## NOTE

After installing the application, the first time you search a keyword in Wolfram Language Documentation Center (help window) Mathematica builds the search index of the new documentation files. It can take a few seconds to minutes depending on your computer. It happens only once (everytime you update the application) though.
