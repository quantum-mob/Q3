BeginPackage["Q3`"]

{ ChebyshevCoefficients, ChebyshevSeries };
{ ChebyshevApproximation, ChebyshevPoints };


Begin["`Private`"]

(**** <ChebyshevPoints> ****)

ChebyshevPoints::usage = "ChebyshevPoints[n] returns a list of n+1 Chebyshev points of the first kind.\nChebyschevPoints[n, k] returns the Chebyshev points of kind k (1 for the first kind or 2 for the second kind).\nChebyshevPoints[n, k, {a, b}] returns the Chebyshev points over Interval[{a, b}]."

ChebyshevPoints[n_Integer, kind : (1|2) : 1] := 
 Cos[(Range[n+1] - 1/2)*Pi/(n+1)]

ChebyshevPoints[n_Integer, 2] := Cos[Range[0, n]*Pi/n]

ChebyshevPoints[n_Integer, kind:(1|2), Interval @ {a_, b_}] :=
  ChebyshevPoints[n, kind, {a, b}]

ChebyshevPoints[n_Integer, kind : (1 | 2), int : {a_, b_}] := With[
  { xx = ChebyshevPoints[n, kind] },
  a*(1 - xx)/2 + b*(1 + xx)/2
]

(**** </ChebyshevPoints> ****)


(**** <ChebyshevCoefficients> ****)

ChebyshevCoefficients::usage = "ChebyshevCoefficients[func, d] returns the Chebyshev expansion coefficients c0, c1, c2, \[Ellipsis], cd assuming that function func is a polynomial of degree d or less.\nChebyshevCoefficients[func, {n, parity}] returns the n non-zero Chebyshev expansion coefficients {c0, c2, \[Ellipsis], c2(n-1)} or {c1, c2,\[Ellipsis], c2n-1} of an even (parity = 1) or odd (parity = -1) polynomial, respectively, by evaluating func only on the positive side of the domain. It does not check the actual parity of func, but simply assumes the given parity."

ChebyshevCoefficients[fun_, d_Integer?NonNegative] := Module[
  { cc = ChebyshevPoints[d] },
  cc = Map[fun, cc];
  cc = FourierDCT[cc, 2] * 2/Sqrt[d+1];
  cc[[1]] /= 2;
  cc
]

ChebyshevCoefficients[fun_, {n_Integer?Positive, parity:(-1|1)}] := Module[
  { cc = ChebyshevPoints[(2*n-1) - (1+parity)/2] },
  cc = Take[cc, n];
  cc = Map[fun, cc];
  cc = Join[cc, parity*Reverse[If[parity == 1, Most @ cc, cc]]];
  cc = FourierDCT[cc, 2] * 2/Sqrt[Length @ cc];
  cc[[1]] /= 2;
  cc[[1+(1-parity)/2;; ;;2]]
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

ChebyshevApproximation::usage = "ChebyshevApproximation[func, d] returns a ChebyshevSeries of degree d or less that approximates function func. It finds the polynomial approximation based on the convex optimization.\nChebyshevApproximation[func, d, interveal] restricts the domain of func to interval \[SubsetEqual] [-1, 1]."

Options[ChebyshevApproximation] = {
  "Points" -> 16,
  "NormType" -> Infinity,
  "Parity" -> False
}

ChebyshevApproximation[fun_, d_Integer, opts:OptionsPattern[{ChebyshevApproximation, NMinimize}]] :=
 ChebyshevApproximation[fun, d, Interval @ {-1, 1}, opts]

ChebyshevApproximation[fun_, d_Integer, int:{_?NumericQ, _?NumericQ},
  opts:OptionsPattern[{ChebyshevApproximation, NMinimize}]
] := ChebyshevApproximation[fun, d, Interval @ int, opts]

ChebyshevApproximation[fun_, d_Integer, int:{{_?NumericQ, _?NumericQ}..},
  opts:OptionsPattern[{ChebyshevApproximation, NMinimize}]
] := ChebyshevApproximation[fun, d, Interval @@ int, opts]

ChebyshevApproximation[fun_, d_Integer, int_Interval, opts:OptionsPattern[{ChebyshevApproximation, NMinimize}]] := 
  If[ OptionValue["Parity"],
    theChebyApprox1[fun, d, int, opts],
    theChebyApprox0[fun, d, int, opts]
  ]


theChebyApprox1[fun_, d_Integer, int_Interval, opts:OptionsPattern[{ChebyshevApproximation, NMinimize}]] := Module[
  { new = IntervalIntersection[int, Interval @ {0, 1}],
    pp, xx, yy, zz, cc, c },
  xx = ChebyshevPoints[Round[2/IntervalSize[new]] * OptionValue["Points"]];
  xx = Select[xx, Between @ new];
  yy = fun /@ xx;
  cc = Array[c, (d + Mod[d, 2, 1])/2, Mod[d, 2]];
  pp = 1 - 2*Mod[d, 2];
  zz = ChebyshevSeries[cc, pp] @ xx;
  cc = NMinimize[Norm[zz - yy, OptionValue["NormType"]], cc, FilterRules[{opts}, Options[NMinimize]]];
  ChebyshevSeries[Values[Last @ cc], pp]
]

theChebyApprox0[fun_, d_Integer, int_Interval, opts:OptionsPattern[{ChebyshevApproximation, NMinimize}]] := Module[
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

(**** </ChebyshevApproximation> ****)


End[]

EndPackage[]
