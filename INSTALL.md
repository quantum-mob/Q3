# Installation Guide

You can install Q3 in two methods: The first is based on the `paclet` system that has recently been introduced by Wolfram Research. It is not only fully automatic but also convenient to get updates later on. Obviously, it requires a stable network connection -- a moderate speed of network is usually enough. The other method is to download and copy the files to a proper folder -- just the traditional method. If your network is unstable or unreliable, then this is the only option for you.

## Automatic Installation from Remote Server (recommended)

1. First, make sure to remove the old copy of `Q3` that you manually installed (older than `Q3 v1.5.1`), and restart your Mathematica.

2. Copy the following code and run it on your Mathematica front end.
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
   That's all!


The additional steps below are for maintaining updates.

- Later on, you can check an update of Q3 by the following command.
  ```Mathematica
  Q3CheckUpdate[]
  ```

- When a newer release is available on the server, you can update Q3 with this command.
  ```Mathematica
  Q3Update[]
  ```
  Depending on the situation, you may need to give an option `AllowVersionUpdate` or `ForceVersionInstall` to `Q3Update`. See the Help Documentation for `Q3Update` for more details.


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

   After installing the application in this method, the first time you search a keyword in Wolfram Language Documentation Center (help window) Mathematica builds the search index of the new documentation files. It can take a few seconds to minutes depending on your computer. It happens only once (everytime you update the application) though.
