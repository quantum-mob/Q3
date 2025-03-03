# Installation Guide

You can install Q3S in two methods: The first is based on the `paclet` system that has recently been introduced by Wolfram Research. It is not only fully automatic but also convenient to get updates later on. The other method is to download and copy the files to a proper folder -- just the traditional method.

## Automatic Installation from Remote Server (recommended)

Q3S supports the *Wolfram Languate Paclet* mechanism of Mathematica packages. It allows remote installation and update.

To install Q3S remotely, please follow these steps:
Copy the following code, and run it on your Mathematica front end (Notebook interface).
```Mathematica
Module[
  { ps },
  ps = PacletSiteRegister[
    "https://github.com/quantum-mob/PacletRepository/raw/main",
    "Quantum Mob Paclet Repository"
  ];
  PacletSiteUpdate[ps];
  PacletInstall["QuantumMob/Q3S"]
]
```
That's all!


## Keeping Q3S Updated

Once installed (using the automatic installation method), Q3S will automatically check for updates and install the newest update (if any). This feature has been introducted in v1.7.3. If you have an older version, you have to manually update Q3S to the most recent one (see the instruction below).

If you want to check for updates and install them manually, follow these instructions:

- You can check for updates of Q3S by the following command.
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
PacletUninstall["QuantumMob/Q3S"]
```

## Manual Installation with Paclet Archive File

You can download a paclet archive file, and install Q3S from it.

1. Get a Wolfram Language Paclet file of Q3S from the [Releases](https://github.com/quantum-mob/Q3/releases). Each release has the "Assets" section, which includes a paclet archive file (with file extension ".paclet" such as "QuantumMob__Q3S-4.0.5.paclet"), zip source file and tar.gz source file.

2. Put it in one of the folders in the search path (see Mathematica built-in symbol `$Path` as well as function `SetDirectory`).

3. On Mathematica, execute
    ```Mathematica
    PacletInstall[File["<filename>"]]
    ```
    Replace `<filename>` in the above with the filename of the paclet archive file (enclosed in the quotation marks).

4. Check your installation.
    ```Mathematica
    PacletFind["QuantumMob/Q3S"]
    ```

## Manual Installation of Nightly Version

If you want to try a beta version of Q3S (it might be buggy), following these steps:

1. Download the whole [`Q3S`](https://github.com/quantum-mob/Q3/tree/main/Q3S)foler as a ZIP file.

2. Unzip the ZIP file.

3. Move (or copy) the `Q3S` folder to either

   ```
   $UserBaseDirectory/Applications/ (recommended)
   ```

   or
   
   ```
   $BaseDirectory/Applications/
   ```

   Here, `$UserBaseDirectory` is a Mathematica(R) symbol, the value of which you can check on your Mathematica.
