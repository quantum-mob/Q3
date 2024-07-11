(* Tools for Quantum Signal Processing *)
(* Based on the ideas in QSPPACK, https://github.com/qsppack/QSPPACK, by Dong, Wang, Meng, Ni and Lin. *)

BeginPackage["Q3`"]

{ QSP, QSPFind, QSPConvert };

{ $QSPLastError,
  $QSPLastIterations };


Begin["`Private`"]

(**** <QSP> ****)

QSP::usage = "QSP[{phi0, phi1, phi2, \[Ellipsis], phid}] represents the quantum signal processing of degree d with full phase vector {phi0, phi1, phi2, \[Ellipsis], phid}.\nQSP[phases, parity] represents the symmetric quantum signal processing associated with reduced phase vector phases and parity (1 for even and -1 for odd)."

QSP /:
MakeBoxes[func:QSP[{phi_?VectorQ, parity:(-1|1)}, post_:Identity], fmt_] :=
  BoxForm`ArrangeSummaryBox[
    QSP, func, None,
    { BoxForm`SummaryItem @ { "Degree: ", 2*Length[phi] - 1 - (1+parity)/2 },
      BoxForm`SummaryItem @ { "Parity: ", parity }
    },
    { BoxForm`SummaryItem @ { "PostProcessor: ", post },
      BoxForm`SummaryItem @ { "Phases: ", phi[[;;UpTo[12]]] }
    },
    fmt,
    "Interpretable" -> Automatic
  ]

QSP /:
MakeBoxes[func:QSP[full_?VectorQ, post_:Identity], fmt_] :=
  BoxForm`ArrangeSummaryBox[
    QSP, func, None,
    { BoxForm`SummaryItem @ { "Degree: ", Length[full]-1 },
      BoxForm`SummaryItem @ { "Parity: ", 1 - 2*Mod[Length[full]-1, 2] }
    },
    { BoxForm`SummaryItem @ { "PostProcessor: ", post },
      BoxForm`SummaryItem @ { "Phases: ", full[[;;UpTo[12]]] }
    },
    fmt,
    "Interpretable" -> Automatic
  ]


QSP[spec__]["Matrix", xx_List] := Map[QSP[spec]["Matrix", #]&, xx]

QSP[spec__]["Matrix", x_] := theQSP[x, spec]


QSP[spec__][xx_List] := Map[QSP[spec], xx]


QSP[{phi_?VectorQ, parity:(-1|1)}, post_][x_] := post @ QSP[{phi, parity}][x]

QSP[{phi_?VectorQ, parity:(-1|1)}][x_] := Module[
  { rox, mat, vec },
  (* Rotation around the x-axis *)
  rox = {
    {x, I * Sqrt[1-x^2]},
    {I * Sqrt[1-x^2], x}
  };
  (* Rotation around the z-axis *)
  mat = Map[TheRotation[#, 3]&, -2*phi];

  mat = Riffle[mat, {rox}];
  vec = Dot @@ Prepend[mat, {1, 0}];

  If[ parity == 1,
    vec . vec,
    vec . rox . vec
  ]
]
(* NOTE: You could use theQSP below. However, Dot[{1, 0}, mat1, mat2, ..., matn, {1, 0}] is faster than Dot[mat, mat2, ..., matn][[1, 1]]. Although the difference is not so big for 2x2 matrices, it may become significant for large n. *)


QSP[full_?VectorQ, post_][x_] := post @ QSP[full][x]

QSP[full_?VectorQ][x_] := Module[
  { rox, mat, vec },
  rox = {
    {x, I*Sqrt[1-x^2]},
    {I*Sqrt[1-x^2], x}
  };
  mat = Map[TheRotation[#, 3]&, -2*full];
  mat = Riffle[mat, {rox}];
  vec = Dot @@ Prepend[mat, {1, 0}];
  vec . {1, 0}
]
(* NOTE: You could use theQSP below. However, Dot[{1, 0}, mat1, mat2, ..., matn, {1, 0}] is faster than Dot[mat, mat2, ..., matn][[1, 1]]. Although the difference is not so big for 2x2 matrices, it may become significant for large n. *)


theQSP[x_, {phi_?VectorQ, parity:(-1|1)}, ___] := Module[
  { roz, mat },
  rox = {
    {x, I * Sqrt[1-x^2]},
    {I * Sqrt[1-x^2], x}
  };
  mat = Map[TheRotation[#, 3]&, -2*phi];
  mat = Dot @@ Riffle[mat, {rox}];
  If[ parity == 1,
    mat . Transpose[mat],
    mat . rox . Transpose[mat]
  ]
]


theQSP[x_, full_?VectorQ, ___] := Module[
  { rox, roz },
  rox = {
    {x, I*Sqrt[1-x^2]},
    {I*Sqrt[1-x^2], x}
  };
  roz = Map[TheRotation[#, 3]&, -2*full];
  Dot @@ Riffle[roz, {rox}]
]

(**** </QSP> ****)


(**** <QSPConvert> ****)

QSPConvert::usage = "QSPConvert[phi, parity] returns the full list of phases corresponding to the reduced phase vector phi with parity.\nQSPConvert[full] converts the full list of phases to a pair of the corresponding reduced vector and parity."

QSPConvert::symm = "Full phase vector `` is not symmetric."


QSPConvert[{phi_?VectorQ, 1}] := (* even parity *)
  Module[
    { full = Join[phi, Reverse @ Most @ phi] },
    full[[Length @ phi]] *= 2;
    full
  ]

QSPConvert[{phi_?VectorQ, -1}] := (* odd parity *)
  Join[phi, Reverse @ phi]


QSPConvert[full_?VectorQ] := Module[
  { L = Length[full],
    phi },
  If[full =!= Reverse[full], Message[QSPConvert::symm, full]];
  (* L = 2*n - (1+parity_/2; n: the length of the reduced phase vector *)
  If[ OddQ[L], (* even parity *)
    phi = Take[full, (L+1)/2];
    phi[[-1]] /= 2;
    {phi, 1},
    phi = Take[full, L/2];
    {phi, -1}
  ]
]


QSPConvert[QSP[{phi_?VectorQ, parity:(-1|1)}, rest___]] :=
  QSP[QSPConvert[{phi, parity}], rest]

QSPConvert[QSP[full_?VectorQ, rest___]] :=
  QSP[QSPConvert[full], rest]

(**** </QSPConvert> ****)


$QSPLastError::usage = "$QSPLastError returns the lastest error of QSPFind or the similar."

$QSPLastIterations::usage = "$QSPLastIterations returns the lastest number of iterations in QSPFind or the similar."


(**** <QSPFind> ****)

QSPFind::usage = "QSPFind[coeff, parity] finds the quantum signal processing (QSP) that represents the desired polynomial characterized by the reduced list coeff of Chebyshev expansion coefficients and parity.\nQSPFind[{c0, c1, c2, ..., cn}] assumes {c0, c1, c2, ..., cn} to be a full list of Chebyshev expansion coefficients of the desired polynomial of degree n, and automatically converts it to the form QSPFind[coeff, parity. In this case, if the parity is indefinite or indeterminate, $Failed is returned with a warning message."

QSPFind::method = "Unknown method ``; \"ContractionMapping\" is used."

QSPFind::maxitr = "MaxIterations reached."

QSPFind::parity = "The parity in coefficients `` is indefinite or indeterminate."

QSPFind::notyet = "Method `` is not available yet; \"ContractionMapping\" is used."


Options[QSPFind] = {
  Method -> "ContractionMapping", (* "L-BFGS", "Newton" *)
  MaxIterations -> 5*^4, (* the maximum number of iterations *)
  Tolerance -> 1.0*^-9, (* the error tolerance *)
  (* "UseReal" -> False, *)
  (* "FullPhases" -> True, *) (* whether to return reduced phases or full phases *)
  "InitialGuess" -> Automatic,
  "PostProcessor" -> Re
  (* whether to target Re[P] or not, where P is the upper-left corner of the QSP unitary matrix *)
  (* NOTE: For the ContractionMapping emthod, at aleast, this option seems irrelevant; actually, it is confusing. *)
}


QSPFind[ChebyshevSeries[cc_, parity:(-1|1)], opts:OptionsPattern[]] :=
  QSPFind[{cc, parity}, opts]


QSPFind[full_?VectorQ, opts:OptionsPattern[]] := With[
  { aa = full[[1;; ;;2]],
    bb = full[[2;; ;;2]] },
  Which[
    Chop @ Norm[N @ aa, 1] == 0, QSPFind[{bb, -1}, opts],
    Chop @ Norm[N @ bb, 1] == 0, QSPFind[{aa, +1}, opts],
    True, Message[QSPFind::parity, full]; Return[$Failed]
  ]
]

QSPFind[{coeff_?VectorQ, parity:(-1|1)}, opts:OptionsPattern[]] := Module[
  { phi, err, itr },
  {phi, err, itr} = Switch[ OptionValue[Method],
    "ContractionMapping", (* the contraction mapping method *)
    qspFindByCM[{coeff, parity}, opts],
    "BFGS", (* the limited-memory BFGS method *)
    qspFindByBFGS[{coeff, parity}, opts],
    "Newton", (* the Newton method *)
    qspFindByNewton[{coeff, parity}, opts],
    _,
    Message[QSPFind::method, OptionValue[Method]];
    qspFindByCM[{coeff, parity}, opts]
  ];
  $QSPLastError = err;
  $QSPLastIterations = itr;
  QSP[{phi, parity}, OptionValue["PostProcessor"]]
]

(**** </QSPFind> ****)


(**** <qspFindByCM> ****)

qspFindByCM::usage = "qspFindByCM[coeff, parity] finds the QSP using the contraction mapping method."

qspFindByCM[{coeff_List, parity:(-1|1)}, opts:OptionsPattern[QSPFind]] := Module[
  { maxitr = OptionValue[MaxIterations],
    tol = OptionValue[Tolerance],
    itr = 0,
    phi = OptionValue["InitialGuess"],
    deg = 2*Length[coeff] - (3+parity)/2, 
    fun, new, err },
  phi = If[ phi === Automatic,
    Reverse[coeff / 2],
    PadRight[phi, Length @ coeff]
  ];
  While[ True,
    fun = QSP[{phi, parity}, OptionValue["PostProcessor"]];
    new = ChebyshevCoefficients[fun, {Length @ coeff, parity}];
    new -= coeff;
    err = Norm[new, 1];
    If[err < tol, Break[]];
    If[++itr > maxitr, Message[QSPFind::maxitr]; Break[]];
    phi -= Reverse[new / 2];
  ];
  {phi, err, itr}
]

(**** </qspFindByCM> ****)

qspFindByBFGS[args__] := (
  Message[QSPFind::notyet, "BFGS"];
  qspFindbyCM[args]
)

qspFindByNewton[args__] := (
  Message[QSPFind::notyet, "Newton"];
  qspFindbyCM[args]
)

End[]

EndPackage[]
