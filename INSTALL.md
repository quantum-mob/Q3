# Installation Guide

You can install Q3 in two methods: The first is based on the `paclet` system that has recently been introduced by Wolfram Research. It is not only fully automatic but also convenient to get updates later on. The other method is to download and copy the files to a proper folder -- just the traditional method.

## Automatic Installation from Remote Server (recommended)

Q3 supports the paclet mechanism of Mathematica packages. It allows remote installation and update. To install remotely, please follow these steps:

1. First, make sure to remove the old copy of `Q3` that you manually installed (older than `Q3 v1.5.1`), and restart your Mathematica. Note also that this method requires **Mathematica v12.2 (or later)**.

2. Copy the following code, and run it on your Mathematica front end (Notebook interface).
   ```Mathematica
   Module[
     { ps },
     ps = PacletSiteRegister[
       "https://github.com/quantum-mob/PacletRepository/raw/main",
       "Quantum Mob Paclet Server"
      ];
     PacletSiteUpdate[ps];
     PacletInstall["Q3"]
   ]
   ```
   That's all!


## Keeping Q3 Updated

Once installed, Q3 will automatically check for updates and install the newest update (if any). This feature has been introducted in v1.7.3. If you have an older version, you have to manually update Q3 to the most recent one (see the instruction below).

If you want to check for updates and install them manually, follow these instructions:

- You can check for updates of Q3 by the following command.
  ```Mathematica
  Q3CheckUpdate[]
  ```

- When a newer release is available on the server, you can install it with this command.
  ```Mathematica
  Q3Update[]
  ```  
  You may like to give an option `ForceVersionInstall->True` to `Q3Update`. See the Help Documentation for `Q3Update` for more details.

## Uninstall

If you do not want Q3 any longer, then you can uninstall it by evaluating the following code:

```Mathematica
PacletUninstall["Q3"]
```

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
