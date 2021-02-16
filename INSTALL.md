# Installation Guide

## Automatic Installation

1. First, make sure to remove the old copy of `Q3` that you manually installed (older than `Q3 v1.5.1`), and restart your Mathematica.

2. Just copy the following code and run it on your Mathematica front end.

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

3. Finally, run the following command on your Mathematica front end.

```Mathematica
Q3Install[]
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
