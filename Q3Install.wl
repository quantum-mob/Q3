Module[
  { ps },
  ps = PacletSiteRegister[
    "https://github.com/quantum-mob/PacletRepository/raw/main",
    "Quantum Mob Paclet Server"
  ];
  PacletSiteUpdate[ps];
  PacletInstall["Q3"]
]
