BeginPackage["Q3`"]

{ ChebyshevCoefficients, ChebyshevSeries };
{ ChebyshevApproximation, ChebyshevPoints };


Begin["`Private`"]

(**** <ChebyshevPoints> ****)

ChebyshevPoints::usage = "ChebyshevPoints[n] returns a list of n Chebyshev points of the first kind that is required to uniquely determine the Chebyshev expansion coefficients of degree n-1.\nChebyshevPoints[{n, parity}] returns a list of n Chebyshev points required to uniquely determine the non-zero Chebyshev coefficients of a polynomial of degree d = (2*n-1) - (1+parity)/2 and parity (\[PlusMinus]1 for even and odd parity, respectively).\nChebyschevPoints[spec, k] returns the Chebyshev points of the kth kind (1 for the first kind or 2 for the second kind).\nChebyshevPoints[n, k, {a, b}] returns the Chebyshev points over Interval[{a, b}]."

ChebyshevPoints[spec_] := ChebyshevPoints[spec, 1]

ChebyshevPoints[n_Integer?Positive, 1] :=
 Cos[(Range[n] - 1/2) * Pi/n]

ChebyshevPoints[n_Integer?Positive, 2] :=
  Cos[Range[0, n-1] * Pi/(n-1)]


ChebyshevPoints[{n_Integer?Positive, parity:(-1|1)}, 1] := With[
  { nn = 2*n - (1+parity)/2 },
  Cos[(Range[n] - 1/2) * Pi/nn]
]


ChebyshevPoints[n_Integer?Positive, kind:(1|2), Interval @ {a_, b_}] :=
  ChebyshevPoints[n, kind, {a, b}]

ChebyshevPoints[n_Integer?Positive, kind:(1|2), int:{a_, b_}] := With[
  { xx = ChebyshevPoints[n, kind] },
  a*(1 - xx)/2 + b*(1 + xx)/2
]

(**** </ChebyshevPoints> ****)


(**** <ChebyshevCoefficients> ****)

ChebyshevCoefficients::usage = "ChebyshevCoefficients[func, n] returns a list {c0, c1, c2, \[Ellipsis], c(n-1)} of n Chebyshev expansion coefficients assuming that function func is a polynomial of degree n+1 or less.\nChebyshevCoefficients[func, {n, parity}] returns the n non-zero Chebyshev expansion coefficients {c0, c2, \[Ellipsis], c2(n-1)} or {c1, c2,\[Ellipsis], c2n-1} of an even (parity = 1) or odd (parity = -1) polynomial, respectively, by evaluating func only on the positive side of the domain. It does not check the actual parity of func, but simply assumes the given parity."

ChebyshevCoefficients[fun_, n_Integer?Positive] := Module[
  { xx = ChebyshevPoints[n] },
  theChebyshevFourier @ Map[fun, xx]
]

ChebyshevCoefficients[fun_, {n_Integer?Positive, parity:(-1|1)}] := Module[
  { xx = ChebyshevPoints[{n, parity}] },
  theChebyshevFourier @ {Map[fun, xx], parity}
]


theChebyshevFourier::usage = "theChebyshevFourier[{y0, y1, ..., yn}] returns the Chebyshev expansion coefficients of the polynomial, which gives {y0, y1, ..., yn} at the Chebyshev points {x0, x1, ..., xn} of the first kind. Note that yk itself could be a vector as the polynomial may be a vector-valued function."

theChebyshevFourier[yy_/;MatrixQ[yy, NumericQ]] :=
  Transpose @ Map[theChebyshevFourier, Transpose @ yy]
(* NOTE: the Fourier transform for each COLUMN. *)
(* NOTE: FourierDCT[mat] performs a multi-dimensional Fourier transform, and cannot be directly used here. *)

theChebyshevFourier[yy_/;VectorQ[yy, NumericQ]] := Module[
  { cc = FourierDCT[yy, 2] * 2/Sqrt[Length @ yy] },
  cc[[1]] /= 2;
  Return[cc]
]

theChebyshevFourier[{yy:(_?VectorQ|_?MatrixQ), parity:(-1|1)}] := Module[
  { cc = If[parity == 1, Most @ yy, yy] },
  cc = Join[yy, parity*Reverse[cc]];
  cc = theChebyshevFourier[cc];
  cc[[1+(1-parity)/2;; ;;2]]
]


(* For non-numeric input *)
theChebyshevFourier[yy:(_?VectorQ|_?MatrixQ)] := Module[
  { n = Length[yy],
    cc },
  cc = Dot[Cos[Dyad[Range[n]-1, Range[n]-1/2] * Pi/n], yy] * 2/n;
  (* NOTE: the Fourier transform for each COLUMN. *)
  cc[[1]] /= 2;
  Return[cc]
]

(**** </ChebyshevCoefficients> ****)


(**** <ChebyshevSeries> ****)

ChebyshevSeries::usage = "ChebyshevSeries[{c0, c2, c4, \[Ellipsis]}, 1] represents the series in Chebysehv polynomlials of even parity with coefficients {c0, c2, c4, \[Ellipsis]}.\nChebyshevSeries[{c1, c3, c5, \[Ellipsis]}, -1] represents the series in Chebysehv polynomlials of odd parity with coefficients {c1, c3, c5, \[Ellipsis]}.\nCChebyshevSeries[{c0, c1, c2, \[Ellipsis]}, 0] represents the series in Chebysehv polynomlials with coefficients {c0, c1, c2, \[Ellipsis]}.\nChebyshevSeries[{c0, c1, c2, \[Ellipsis]}] is automatically converted to ChebyshevSeries[coeff, parity] according to the parity indicated in {c0, c1, c2, \[Ellipsis]}."

ChebyshevSeries /:
MakeBoxes[func:ChebyshevSeries[cc_?VectorQ, parity:(-1|0|1)], fmt_] :=
  BoxForm`ArrangeSummaryBox[
    ChebyshevSeries, func, None,
    { BoxForm`SummaryItem @ { "Degree: ", func["Degree"] },
      BoxForm`SummaryItem @ { "Parity: ", Switch[parity, 1, "Even", -1, "Odd", _, "Indefinite"] }
    },
    { BoxForm`SummaryItem @ { "Coefficients: ", cc[[;;UpTo[20]]] }
    },
    fmt,
    "Interpretable" -> Automatic
  ]

ChebyshevSeries[cc_?VectorQ /;Length[cc] == 0, _]["Degree"] = 0

ChebyshevSeries[cc_?VectorQ, parity:(-1|1|0)]["Degree"] :=
  Switch[ parity,
    +1, 2*Length[cc] - 2,
    -1, 2*Length[cc] - 1,
    -0, Length[cc] - 1
  ]


ChebyshevSeries[spec__][xx_?ArrayQ] :=
  Map[ChebyshevSeries[spec], xx]


ChebyshevSeries[{cc_?VectorQ, parity:(-1|1)}] :=
  ChebyshevSeries[cc, parity]

ChebyshevSeries[cc_?VectorQ,  0][x_] :=
  Dot[cc, ChebyshevT[Range[Length @ cc] - 1, x]]

ChebyshevSeries[cc_?VectorQ,  1][x_] := 
  Dot[cc, ChebyshevT[2*Range[Length @ cc] - 2, x]]

ChebyshevSeries[cc_?VectorQ, -1][x_] := 
  Dot[cc, ChebyshevT[2*Range[Length @ cc] - 1, x]]


ChebyshevSeries[{}] := ChebyshevSeries[{}, 0]

ChebyshevSeries[{c_}] := ChebyshevSeries[{c}, 1]

ChebyshevSeries[cc_?VectorQ] := With[
  { aa = cc[[1;; ;;2]],
    bb = cc[[2;; ;;2]] },
  Which[
    ZeroQ @ Norm[N @ aa, Infinity], ChebyshevSeries[TrimRight @ bb, -1],
    ZeroQ @ Norm[N @ bb, Infinity], ChebyshevSeries[TrimRight @ aa, +1],
    True, ChebyshevSeries[cc, 0]
  ]
]

(**** </ChebyshevSeries> ****)


(**** <ChebyshevApproximation> ****)

ChebyshevApproximation::usage = "ChebyshevApproximation[func, d] returns a ChebyshevSeries of degree d or less that approximates function func.\nChebyshevApproximation[func, {n, parity}] returns a ChebyshevSeries of degree 2n+(1-parity)/2 and parity, by evaluating the function only on the positive side of the domain.\nChebyshevApproximation[func, spec, interveal] restricts the domain of func to interval \[SubsetEqual] [-1, 1].\nChebyshevApproximation finds the polynomial approximation based on the convex optimization, more specifically, using the built-in global minimizer NMinimize."

Options[ChebyshevApproximation] = {
  "Points" -> 16,
  "NormType" -> Infinity,
  "Parity" -> False
}

ChebyshevApproximation[fun_, spec_, opts:OptionsPattern[{ChebyshevApproximation, NMinimize}]] :=
 ChebyshevApproximation[fun, spec, Interval @ {-1, 1}, opts]

ChebyshevApproximation[fun_, spec_, int:{_?NumericQ, _?NumericQ},
  opts:OptionsPattern[{ChebyshevApproximation, NMinimize}]
] := ChebyshevApproximation[fun, spec, Interval @ int, opts]

ChebyshevApproximation[fun_, spec_, int:{{_?NumericQ, _?NumericQ}..},
  opts:OptionsPattern[{ChebyshevApproximation, NMinimize}]
] := ChebyshevApproximation[fun, spec, Interval @@ int, opts]


ChebyshevApproximation[ fun_, d_Integer?NonNegative, int_Interval,
  opts:OptionsPattern[{ChebyshevApproximation, NMinimize}] ] :=
Module[
  { new = IntervalIntersection[int, Interval @ {-1, 1}], (* just in case *)
    xx, yy, zz, cc, c },
  xx = ChebyshevPoints[Round[2/IntervalSize[new]] * OptionValue["Points"]];
  xx = Select[xx, Between @ new];
  yy = N[fun /@ xx];
  cc = Array[c, d+1, 0];
  zz = ChebyshevSeries[cc, 0] @ xx;
  cc = NMinimize[Norm[zz - yy, OptionValue["NormType"]], cc, FilterRules[{opts}, Options[NMinimize]]];
  ChebyshevSeries[Values[Last @ cc]]
]

ChebyshevApproximation[ fun_, {n_Integer?NonNegative, parity:(-1|1)}, int_Interval,
  opts:OptionsPattern[{ChebyshevApproximation, NMinimize}] ] :=
Module[
  { new = IntervalIntersection[int, Interval @ {0, 1}],
    xx, yy, zz, cc, c },
  xx = ChebyshevPoints[Round[2/IntervalSize[new]] * OptionValue["Points"]];
  xx = Select[xx, Between @ new];
  yy = fun /@ xx;
  cc = Array[c, n+1, (1-parity)/2];
  zz = ChebyshevSeries[cc, parity] @ xx;
  cc = NMinimize[Norm[zz - yy, OptionValue["NormType"]], cc, FilterRules[{opts}, Options[NMinimize]]];
  ChebyshevSeries[Values[Last @ cc], parity]
]

(**** </ChebyshevApproximation> ****)


End[]

EndPackage[]
