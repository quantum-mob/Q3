(* -*- mode:math -*- *)

(* Using some parts of the code from
   https://github.com/jkuczm/MathematicaTeXUtilities *)

BeginPackage["Q3`"]

`Knuth`$Version = StringJoin[
  $Input, " v",
  StringSplit["$Revision: 1.5 $"][[2]], " (",
  StringSplit["$Date: 2022-08-23 10:17:36+09 $"][[2]], ") ",
  "Mahn-Soo Choi"
 ];

{ TeXVerbatim };


Begin["`Private`"]


fTeXRelevantQ::usage ="fTeXRelevantQ[sym] returns True if given symbol sym has TeXForm format values and is not Locked; returns False otherwise."

fTeXRelevantQ = Function[ Null,
  Not @ MemberQ[Attributes @ Unevaluated @ #, Locked] &&
    MemberQ[FormatValues @ Unevaluated @ #,
      _[lhs_ /; Not @ FreeQ[lhs, HoldPattern @ Format[_, TeXForm]] , _]],
  HoldAllComplete
 ]


getTeXRelevantSymbols::usage = "getTeXRelevantSymbols[expr] returns HoldComplete[sym1, sym2, ...] where symi are non-Locked symbols with TeXForm format values."

getTeXRelevantSymbols = Function[Null,
  HoldComplete @@ Union @@ Cases[
    Unevaluated @ #,
    s:Except[HoldPattern @ Symbol[___], _Symbol]?fTeXRelevantQ :>
      HoldComplete @ s,
    {0, Infinity},
    Heads -> True
   ],
  HoldAllComplete
 ]


fTeXToTraditionalFormat::usage =
"\
fTeXToTraditionalFormat[sym] \
replaces TeXForm format values, of given symbol sym, with TraditionalForm \
format values."


fTeXToTraditionalFormat = Function[Null,
	FormatValues@Unevaluated@# = Replace[FormatValues@Unevaluated@#,
		h_[lhs_ /; Not@FreeQ[lhs, HoldPattern@Format[_, TeXForm]], rhs_] :> h[
			lhs /. HoldPattern@Format[x_, TeXForm] :>
				MakeBoxes[x, TraditionalForm],
			Format[rhs, TraditionalForm]
		],
		{1}
	],
	HoldAllComplete
]

expressionToTeX::usage =
"\
expressionToTeX[arg1, arg2, ...] \
returns same result as Convert`TeX`ExpressionToTeX[arg1, arg2, ...] with down \
values not modified by this package."


Attributes[expressionToTeX] = HoldAllComplete

$expressionToTeXDV::usage = "$expressionToTeXDV \
is a down value for Convert`TeX`ExpressionToTeX, calling original \
Convert`TeX`ExpressionToTeX down value, except this one, in environment with \
TeXForm format values, of symbols from first argument, locally replaced with \
TraditionalForm format values."


$expressionToTeXDV = HoldPattern@Convert`TeX`ExpressionToTeX[expr_, rest___] :>
	Replace[getTeXRelevantSymbols@expr, HoldComplete@syms___ :>
		Internal`InheritedBlock[{expressionToTeX, syms},
			Unprotect@{syms};
			Scan[fTeXToTraditionalFormat, Unevaluated@{syms}];
			expressionToTeX // DownValues = DeleteCases[
				DownValues@Convert`TeX`ExpressionToTeX,
				Verbatim@$expressionToTeXDV
			] /. Convert`TeX`ExpressionToTeX -> expressionToTeX;
			expressionToTeX[expr, rest]
		]
	]

(* Evaluate symbol to load necessary contexts. *)
Convert`TeX`ExpressionToTeX


With[
  { protected = Unprotect[Convert`TeX`ExpressionToTeX],
    dv = DownValues[Convert`TeX`ExpressionToTeX] },
  If[ dv === {} || First[dv] =!= $expressionToTeXDV,
    DownValues[Convert`TeX`ExpressionToTeX] = Prepend[
      DeleteCases[dv, Verbatim@$expressionToTeXDV],
      $expressionToTeXDV
     ]
   ];
  Protect[protected]
 ]


TeXVerbatim::usage = "TeXVerbatim[\"str\"] gives verbatim \"str\" when converted to TeX (e.g., using TeXForm)."

SyntaxInformation[TeXVerbatim] = {
  "ArgumentsPattern" -> {_}
 }

TeXVerbatim[arg:Except[_String]] := (
  Message[TeXVerbatim::string, 1, HoldForm @ TeXVerbatim @ arg];
  $Failed
 )

System`Convert`TeXFormDump`maketex @ RowBox @ {
  "TeXVerbatim",
  "(" | "[",
  arg_String?(StringMatchQ[#, "\"" ~~ ___ ~~ "\""]&),
  ")" | "]"
 } := ToExpression@arg


(***** <TeXVerbatim> ****)


(***** <formatting Ket[...] and Bra[...]> ****)

Format[Ket[args:Except[_Association]..], TeXForm] :=
  TeXVerbatim @ StringJoin[
    "\\ket{",
    Riffle[ToString[#, TeXForm]& /@ {args}, ","],
    "}"
   ]

Format[Bra[args:Except[_Association]..], TeXForm] :=
  TeXVerbatim @ StringJoin[
    "\\bra{",
    Riffle[ToString[#, TeXForm]& /@ {args}, ","],
    "}"
   ]

(***** </formatting Ket[...] and Bra[...]> ****)

End[]

EndPackage[]
