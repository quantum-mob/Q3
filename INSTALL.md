# Installation Guide

You can install Q3 in two methods: The first is based on the `paclet` mechanism that has recently been introduced. It is not only fully automatic but also convenient to get updates later on. The other method is to download and copy the files to a proper folder -- just the traditional method.

## Automatic Installation from Remote Server (recommended)

Q3 supports the *Wolfram Languate Paclet* mechanism. It allows remote installation and update.

To install Q3 remotely, please follow these steps:
Copy the code below, and run it on your Mathematica front end (Notebook interface).
```Mathematica
Module[
  { ps },
  ps = PacletSiteRegister[
    "https://github.com/quantum-mob/PacletRepository/raw/main",
    "Quantum Mob Paclet Repository"
  ];
  PacletSiteUpdate[ps];
  PacletInstall["QuantumMob/Q3"]
]
```
That's all!


### Keeping Q3 Updated

Once installed (using the automatic installation method), Q3 will automatically check for updates and install the newest update (if any). This feature has been introducted in Q3 v1.7.3. If you have an older version, you have to manually update Q3 to the most recent one (see the instruction below).

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

### Uninstall

If you do not want Q3 any longer, then you can uninstall it by evaluating the following code:

```Mathematica
PacletUninstall["QuantumMob/Q3"]
```

## Manual Installation with Paclet Archive File

You can download a paclet archive file, and install Q3 from it.

1. Get a Wolfram Language Paclet file of Q3 from the [Releases](https://github.com/quantum-mob/Q3/releases). Each release has the "Assets" section, which includes a paclet archive file (with file extension ".paclet" such as "QuantumMob__Q3-4.1.2.paclet"), zip source file and tar.gz source file.

2. Put it in one of the folders in the search path (see Mathematica built-in symbol `$Path` as well as function `SetDirectory`).

3. On Mathematica, execute
    ```Mathematica
    PacletInstall[File["<filename>"]]
    ```
    Replace `<filename>` in the above with the filename of the paclet archive file (enclosed in the quotation marks).

4. Check your installation.
    ```Mathematica
    PacletFind["QuantumMob/Q3"]
    ```

## Manual Installation of Nightly Version

If you want to try a beta version of Q3 (it might be buggy), following these steps:

1. Download the whole [`Q3`](https://github.com/quantum-mob/Q3/tree/main/Q3)foler as a ZIP file.

2. Unzip the ZIP file.

3. Move (or copy) the `Q3` folder to either

   ```
   $UserBaseDirectory/Applications/ (recommended)
   ```

   or
   
   ```
   $BaseDirectory/Applications/
   ```

   Here, `$UserBaseDirectory` is a Mathematica(R) symbol, the value of which you can check on your Mathematica.
