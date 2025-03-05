Module[
  { ps },
  ps = PacletSiteRegister[
    "https://github.com/quantum-mob/PacletRepository/raw/main",
    "Quantum Mob Paclet Repository"
  ];
  PacletSiteUpdate[ps];
  PacletInstall["QuantumMob/Q3"]
]
