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


QSP[spec__][xx_List] := Map[QSP[spec], xx]

QSP[spec_, post_][x_] := post @ QSP[spec][x]

QSP[full_?VectorQ][x_] := Dot @@ Join[{{1, 0}}, theQSP[full, x], {{1, 0}}]

QSP[{phi_?VectorQ, +1}][x_] := With[
  { vec = Dot @@ Join[{{1, 0}}, theQSP[{phi, 1}, x]] },
  vec . vec
  (* NOTE: all matrices are symmetric *)
]

QSP[{phi_?VectorQ, -1}][x_] := Module[
  { mat = theQSP[{phi, -1}, x],
    vec },
  vec = Dot @@ Join[{{1, 0}}, Most @ mat];
  vec . Last[mat] . vec
  (* NOTE: all matrices are symmetric *)
]


QSP /:
Gradient[QSP[spec_], xx_List] := Transpose @ Map[Gradient[QSP[spec], #]&, xx]

QSP /:
Gradient[QSP[spec_, post_], x_] := post @ Gradient[QSP[spec], x]


QSP /:
Gradient[QSP[{phi_?VectorQ, parity:(-1|1)}], x_?NumericQ] := Module[
  { mat, new, bra, ket, val, grd, k },
  mat = theQSP[{phi, parity}, x];
  new = If[parity == 1, mat, Most @ mat];
  new = Table[Insert[new, ThePauli[3], 2*k], {k, Length @ phi}];
  bra = {1, 0};
  ket = Dot @@ Join[{bra}, mat];
  grd = I * (
    Map[Dot @@ Join[{bra}, #, {ket}]&, new] +
    Map[Dot @@ Join[{ket}, #, {bra}]&, Reverse /@ new]
  );
  (* NOTE: all matrices are symmetric *)
  val = If[parity == 1, ket . ket, ket . Topple[Last @ mat] . ket];
  {val, grd}
]

QSP /:
Gradient[QSP[full_?VectorQ], x_?NumericQ] := Module[
  { mat, grd, k },
  mat = theQSP[full, x];
  grd = Table[Insert[mat, ThePauli[3], 2*k], {k, Length @ full}];
  grd = I * Map[Dot @@ Join[{{1, 0}}, #, {{1, 0}}]&, grd];
  {Dot @@ Join[{{1, 0}}, mat, {{1, 0}}], grd}
]


QSP /:
Jacobian[qsp:QSP[{phi_?VectorQ, parity:(-1|1)}, ___]] := Module[
  { xx, yy },
  xx = ChebyshevPoints[{Length @ phi, parity}];
  yy = Gradient[qsp, xx];
  theChebyshevFourier[{#, parity}]& /@ yy
]

QSP /:
Jacobian[qsp:QSP[full_?VectorQ, ___]] := Module[
  { xx, yy },
  xx = ChebyshevPoints[Length @ full];
  yy = Gradient[qsp, xx];
  theChebyshevFourier /@ yy
]


QSP /:
Hessian[QSP[spec_], xx_List] := Transpose @ Map[Hessian[QSP[spec], #]&, xx]

QSP /:
Hessian[QSP[spec_, post_], x_] := post @ Hessian[QSP[spec], x]


QSP /:
Hessian[QSP[{phi_?VectorQ, parity:(-1|1)}], x_?NumericQ] := Module[
  { mat, new, bra, ket, val, hss, i, j },
  mat = theQSP[{phi, parity}, x];
  new = If[parity == 1, mat, Most @ mat];
  hss = Table[
    Insert[new, ThePauli[3], {{2*i}, {2*j}}],
    {i, Length @ phi},
    {j, Length @ phi}
  ];
  bra = {1, 0};
  ket = Dot @@ Join[{bra}, mat];
  hss = -(
    Map[Dot @@ Join[{bra}, #, {ket}]&, hss, {2}] +
    Map[Dot @@ Join[{ket}, #, {bra}]&, Map[Reverse, hss, {2}], {2}]
  );
  new = Table[Insert[new, ThePauli[3], 2*i], {i, Length @ phi}];
  new = -Outer[Dot @@ Join[{bra}, #1, #2, {bra}]&, new, Reverse /@ new, 1];
  hss += new + Transpose[new];
  val = If[parity == 1, ket . ket, ket . Topple[Last @ mat] . ket];
  {val, hss}
]

QSP /:
Hessian[QSP[full_?VectorQ], x_?NumericQ] := Module[
  { mat, hss, i, j },
  mat = theQSP[full, x];
  hss = Table[
    Insert[mat, ThePauli[3], {{2*i}, {2*j}}],
    {i, Length @ full},
    {j, Length @ full}
  ];
  hss = -Map[Dot @@ Join[{{1, 0}}, #, {{1, 0}}]&, hss, {2}];
  {Dot @@ Join[{{1, 0}}, mat, {{1, 0}}], hss}
]


QSP /:
Matrix[QSP[spec__], xx_List] := Map[Matrix[QSP[spec], #]&, xx]

QSP /:
Matrix[QSP[full_?VectorQ, ___], x_] := Dot @@ theQSP[full, x]

QSP /:
Matrix[QSP[{phi_?VectorQ, parity:(-1|1)}, ___], x_] := With[
  { mat = theQSP[{phi, parity}, x] },
  Dot @@ If[ parity == 1,
    Join[mat, Reverse @ mat],
    Join[mat, Reverse @ Most @ mat]
  ]
]


theQSP::usage = "theQSP[{phi, parity}, x] or theQSP[full, x] returns the list of matrices involved in the QSP.\nWith out = theQSP[{phi, parity}, x], get the full list by Join[out, Reverse @ out] for parity = 1, and Join[out, Reverse @ Most @ out] for parity = -1."

theQSP[{phi_?VectorQ, parity:(-1|1)}, x_] := Module[
  { rox, mat },
  rox = {
    {x, I * Sqrt[1-x^2]},
    {I * Sqrt[1-x^2], x}
  };
  mat = Map[TheRotation[#, 3]&, -2*phi];
  mat = Riffle[mat, {rox}];
  If[parity == 1, mat, Join[mat, {rox}]]
]

theQSP[full_?VectorQ, x_] := Module[
  { rox, roz },
  rox = {
    {x, I*Sqrt[1-x^2]},
    {I*Sqrt[1-x^2], x}
  };
  roz = Map[TheRotation[#, 3]&, -2*full];
  Riffle[roz, {rox}]
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

QSPFind::method = "Unknown method ``; \"FixedPointIterations\" is used."

QSPFind::maxitr = "MaxIterations reached."

QSPFind::parity = "The parity in coefficients `` is indefinite or indeterminate."

QSPFind::notyet = "Method `` is not available yet; \"FixedPointIterations\" is used."


Options[QSPFind] = {
  Method -> "FixedPointIterations", (* "L-BFGS", "Newton" *)
  MaxIterations -> 5*^4, (* the maximum number of iterations *)
  Tolerance -> 1.0*^-9, (* the error tolerance *)
  "PostProcessor" -> Re, (* an additional operator the apply to the bare QSP polynomial. *)
  "InitialGuess" -> Automatic
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
  { method = OptionValue[Method],
    config = {},
    phi, err, itr },
  If[ ListQ[method],
    config = Rest[method];
    method = First[method]
  ];
  {phi, err, itr} = Switch[ method,
    "FixedPointIterations", (* the fixed point iterations based on contraction mapping theorem *)
    qspFindByFPI[{coeff, parity}, opts],
    "BFGS", (* the limited-memory BFGS (L-BFGS) method *)
    qspFindByBFGS[{coeff, parity}, config, opts],
    "Newton", (* the Newton method *)
    qspFindByNewton[{coeff, parity}, opts],
    "FindMinimum", (* using FindMinimum, a local optimizer *)
    qspFindByFindMinimum[{coeff, parity}, config, Method -> Automatic, opts],
    "NMinimize", (* using NMinimize, a global minimizer *)
    qspFindByNMinimize[{coeff, parity}, config, Method -> Automatic, opts],
    _,
    Message[QSPFind::method, OptionValue[Method]];
    qspFindByFPI[{coeff, parity}, opts]
  ];
  $QSPLastError = err;
  $QSPLastIterations = itr;
  QSP[{phi, parity}, OptionValue["PostProcessor"]]
]

(**** </QSPFind> ****)


(**** <qspFindByFPI> ****)

qspFindByFPI::usage = "qspFindByFPI[{coeff, parity}] finds a QSP by fixed point iterations (FPI) based on the contraction mapping theorem."

qspFindByFPI[{coeff_List, parity:(-1|1)}, opts:OptionsPattern[QSPFind]] := Module[
  { itr = 0,
    max = OptionValue[MaxIterations],
    tol = OptionValue[Tolerance],
    phi = OptionValue["InitialGuess"],
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
    If[++itr > max, Message[QSPFind::maxitr]; Break[]];
    phi -= Reverse[new / 2];
  ];
  {phi, err, itr}
]

(**** </qspFindByFPI> ****)


(**** <qspFindByNewton> ****)

qspFindByNewton::usage = "qspFindByNewton[{coeff, parity}] finds a QSP using the Newton method."

qspFindByNewton[{coeff_List, parity:(-1|1)}, opts:OptionsPattern[QSPFind]] := Module[
  { itr = 0,
    max = OptionValue[MaxIterations],
    tol = OptionValue[Tolerance],
    phi = OptionValue["InitialGuess"],
    val, jac, err },
  phi = If[ phi === Automatic,
    PadRight[{Pi/4.}, Length @ coeff],
    PadRight[phi, Length @ coeff]
  ];
  While[ True,
    {val, jac} = Jacobian @ QSP[{phi, parity}, OptionValue["PostProcessor"]];
    val -= coeff;
    err = Norm[val, 1];
    If[err < tol, Break[]];
    If[++itr > max, Message[QSPFind::maxitr]; Break[]];
    phi -= LinearSolve[jac, val];
  ];
  {phi, err, itr}
]

(**** </qspFindByNewton> ****)


(**** <qspFindByBFGS> ****)

qspFindByBFGS::usage = "qspFindByBFGS[{coeff, parity}] finds a QSP using the limited-memory BFGS method, one of the popular quasi-Newton optimization methods."

Options[qspFindByBFGS] = {
  "MemorySize" -> 200, (* the memory size *)
  "RetractionRate" -> 0.5, (* the retraction rate of the line search problem *)
  "AcceptanceRate" -> 1.0*^-3, (* the acceptance rate of the line search problem *)
  "MinStepSize" -> 1.0*^-5 (* the minimum step size of the line search problem *)
}

qspFindByBFGS[{coeff_List, parity:(-1|1)}, OptionsPattern[{QSPFind, qspFindByBFGS}]] := Module[
  { itr = 0,
    max = OptionValue[MaxIterations],
    tol = OptionValue[Tolerance],
    phi = OptionValue["InitialGuess"],
    pst = OptionValue["PostProcessor"],
    vol = OptionValue["MemorySize"],
    ret = OptionValue["RetractionRate"], (* line serach *)
    acc = OptionValue["AcceptanceRate"], (* line serach *)
    min = OptionValue["MinStepSize"],
    pnt = ChebyshevPoints[{Length @ coeff, parity}],
    val, grd, dir, rho,
    size, step, dvar, dgrd, alfa, beta, expt, k, i, j },
  phi = If[ phi === Automatic,
    PadRight[{Pi/4.}, Length @ coeff],
    PadRight[phi, Length @ coeff]
  ];
  (* storage initialization *)
  k = 0; (* main index *)
  size = 0; (* the current size of memory *)
  dvar = Zero[{vol, Length @ coeff}]; (* step size in variable: x(k+1) - x(k) *)
  dgrd = Zero[{vol, Length @ coeff}]; (* step size in gradient: g[k+1] - g[k] *)
  rho  = Zero[{vol}]; (* inverse scale factor: rho[[i]] := 1 / Dot[dvar[[i]], dgrd[[i]]] *)
  (* objective values and gradients *)
  {val, grd} = Mean /@ qspGradients[phi, {coeff, parity}, pnt, pst];
  While[ True,
    dir = grd; (* the direction to move *)
    alfa = Zero[size];
    Table[
      i = Mod[k-j, vol, 1];
      alfa[[j]] = rho[[i]] * Dot[dvar[[i]], dir];
      dir -= alfa[[j]] * dgrd[[i]],
      {j, size}
    ];
    dir *= 0.5;
    If[parity == 1, dir[[-1]] *= 2];
    Table[
      i = Mod[k-(size+1-j), vol, 1];
      beta = rho[[i]] * Dot[dgrd[[i]], dir];
      dir += (alfa[[-j]] - beta)*dvar[[i]],
      {j, size}
    ];    
    expt = Dot[grd, dir]; (* the expectation value of the approximate inverse Hessian *)

    step = 1; (* the step size of line search *)
    While[ True,
      new = phi - step * dir;
      try = Mean @ qspObjective[new, {coeff, parity}, pnt, pst];
      If[(val - try) > acc * expt * step || step < min, Break[]];
      step *= ret
    ];
    phi = new; (* update phase variables *)
    {val, new} = qspGradients[phi, {coeff, parity}, pnt, pst];
    err = Max[val];
    val = Mean[val]; (* objective value update *)
    new = Mean[new];
    (* index update *)
    k = Mod[k+1, vol, 1];
    (* storage update *)
    size = Min[vol, size+1];
    dvar[[k]] = -step * dir;
    dgrd[[k]] = new - grd;
    rho[[k]]  = 1 / Dot[dvar[[k]], dgrd[[k]]];
    grd = new; (* gradients update *)
    If[err < tol, Break[]];
    If[++itr > max, Message[QSPFind::maxitr]; Break[]];
  ];
  { phi, err, itr }
]

(**** </qspFindByBFGS> ****)


qspObjective::usage = "Regarding the problem of finding a QSP as an optimization problem, qspObjective is the objective function of the optimization problem."

qspObjective[phi_?VectorQ, {cff_?VectorQ, parity:(-1|1)}, xx_?VectorQ, post_] := Module[
  { try = QSP[{phi, parity}, post][xx],
    val = ChebyshevSeries[cff, parity][xx] },
  Power[try - val, 2] / 2
]


qspGradients::usage = "qspGradients is the gradient of the qspObjective with respect to the phase variables."

qspGradients[phi_?VectorQ, {cff_?VectorQ, parity:(-1|1)}, xx_?VectorQ, post_] := Module[
  { val = ChebyshevSeries[cff, parity][xx],
    try, grd },
  {try, grd} = Gradient[QSP[{phi, parity}, post], xx];
  try -= val;
  { Power[try, 2] / 2,
    MapThread[Times, {try, grd}] }
]


(**** <qspFindByFindMinimum> ****)

qspFindByFindMinimum::usage = "qspFindByFindMinimum[{coeff, parity}] finds a QSP using the built-in local optimizer FindMinimum."

qspFindByFindMinimum[{coeff_List, parity:(-1|1)}, opts:OptionsPattern[{QSPFind, FindMinimum}]] := Module[
  { itr = 0,
    ini = OptionValue["InitialGuess"],
    pst = OptionValue["PostProcessor"],
    pnt = ChebyshevPoints[{Length @ coeff, parity}],
    out, var, phi, options },
  options = FilterRules[{opts}, Options @ FindMinimum];
  ini = If[ ini === Automatic,
    PadRight[{Pi/4.}, Length @ coeff],
    PadRight[ini, Length @ coeff]
  ];
  var = Array[phi, Length @ coeff, 0]; (* minimization variables *)
  out = FindMinimum[
    Mean @ qspObjective[var, {coeff, parity}, pnt, pst],
    Transpose @ {var, ini},
    Evaluate @ options,
    Gradient :> Mean @ Last @ qspGradients[var, {coeff, parity}, pnt, pst],
    EvaluationMonitor :> itr++
  ];
  (* NOTE: The Graident option must be given. Otherwise, FindMinimum first
  localizes the values of all variables, then evaluates the function with the
  variables being symbolic, and then repeatedly evaluates the result
  numerically. Typically, the symbolic evaluation is very slow. *)
  { Values @ Last @ out, First @ out, itr }
]

(**** </qspFindByFindMinimum> ****)


(**** <qspFindByNMinimize> ****)
qspFindByNMinimize::usage = "qspFindByNMinimize[{coeff, parity}] finds a QSP using the built-in global optimizer NMinimize."
(* NOTE: Both FindMinimum and NMinimize first localize the values of all
variables, then evaluates the function with the variables being symbolic, and
then repeatedly evaluates the result numerically. Evaluated with variables
being symbolic, the function evaluation may be very slow; for example,
FourierDCT cannot be used within the objective function. For FindMinimum,
this issue may be over come by giving the Gradient option. However, I have
found no way to avoid it for NMinimize. *)

qspFindByNMinimize[{coeff_List, parity:(-1|1)}, opts:OptionsPattern[{QSPFind, NMinimize}]] := Module[
  { pst = OptionValue["PostProcessor"],
    pnt = ChebyshevPoints[{Length @ coeff, parity}],
    out, fun, var, phi, options },
  options = FilterRules[{opts}, Options @ NMinimize];
  var = Array[phi, Length @ coeff, 0]; (* minimization variables *)
  out = NMinimize[
    Mean @ qspObjective[var, {coeff, parity}, pnt, pst],
    var,
    Evaluate @ options
  ];
  { Values @ Last @ out, First @ out, 0 }
]

(**** </qspFindByNMinimize> ****)


End[]

EndPackage[]
