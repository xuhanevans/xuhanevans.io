(* ::Package:: *)

BeginPackage["Process`"];
Needs["HypothesisTesting`"];
Needs["PlotLegends`"];

(* Utilitiy functions for using lists of rules as record structures. *)
RGet[s_, n_] := n /. s;
RSet[s_, n_, v_] := s /. (n -> _) -> (n -> v);
RAddField[s_, n_, v_] := Append[s, n -> v];
RAddFields[s_, nvpairs_] := Join[s, Map[(#[[1]] -> #[[2]])&, nvpairs]];
RMapField[slist_, n_] := Map[RGet[#, n]&, slist];
(* Given a list of records and a list of fields, create a list of tuples.
   For example, given {{a -> 1, b -> 2, c -> 3}, {a -> 4, b-> 5, c -> 6}} and
   {a, b}, returns {{1, 2}, {4, 5}}. *)
RMapFields[slist_, nlist_] := Map[Function[fields, Map[Function[name, RGet[fields, name]], nlist]], slist];

(* Indexes for columns in the CSV file. *)
RowToRecord[row_] :=
	{ date         -> row[[1]],
	  sentence     -> row[[2]],
	  word         -> row[[3]],
	  type         -> row[[4]],
	  time         -> row[[5]],
	  newline      -> row[[6]],
	  answer       -> row[[7]],
	  length       -> row[[8]],
	  iphash       -> row[[9]],
	  sentencehash -> row[[10]]
	};
RecordToRow[rec_] :=
	{ RGet[rec, date],
	  RGet[rec, sentence],
	  RGet[rec, word],
	  RGet[rec, type],
	  RGet[rec, time],
	  RGet[rec, newline],
	  RGet[rec, answer],
	  RGet[rec, length],
	  RGet[rec, iphash],
	  RGet[rec, sentencehash]
	};

ImportResults[filename_] := Map[RowToRecord, Import[filename, "CSV"]]
ExportResults[filename_, results_] := Export[filename, Map[RecordToRow, results]];

(* This function is used to rejig results to compensate for a bug in
   an earlier version of the server. *)
CorrectShift[csv_] :=
	Module[{s = Split[csv, (RGet[#1, sentencehash] == RGet[#2, sentencehash])&]},
	Flatten1[Map[
		Function[srows,
			MapIndexed[
				Function[{v, i},
					RSet[srows[[First[i]]], length, v]
				],
				Module[{lengths = RMapField[srows, length]},
					Join[{Round[Mean[lengths]]}, Drop[lengths, -1]]
				]
			]
		],
		s
	]]];

(* For each subject, find the percentage of comprehension questions
   that they got right. Returns a list of dates paired with percentages. *)
ComprehensionPercentages[csv_, typef_ : None] :=
	Module[
        {currentSubject = -1,
         right = 0,
         wrong = 0,
         percentages = { },
		 filteredcsv = If[SameQ[typef, None], csv, Select[csv, (typef[RGet[#, type]])&]]
        },
		Scan[Function[row,
			If[RGet[row, date] != currentSubject,
				If[currentSubject != -1,
				    percentages = Append[percentages, {currentSubject, right / (right + wrong)}];
                ];
				currentSubject = RGet[row, date];
	            right = 0;
	            wrong = 0;
			];

	        If[RGet[row, answer] == 1, right += 1];
	        If[RGet[row, answer] == 0, wrong += 1];
	    ], filteredcsv];
		percentages = Append[percentages, {currentSubject, right / (right + wrong)}];

		percentages
	];
MeanComprehensionPercentages[csv_, typef_ : None] :=
	Mean[Map[#[[2]]&, ComprehensionPercentages[csv, typef]]];
SdComprehensionPercentages[csv_, typef_ : None] :=
	StandardDeviation[Map[#[[2]]&, ComprehensionPercentages[csv, typef]]];

(* Change the type of a row with a given MD5 sentence hash. *)
ChangeTypeByHash[csv_, hash_, t_] :=
	Map[Function[row, If[RGet[row, sentencehash] == hash, RSet[row, type, t], row]], csv];

(* Predicates for filtering out individual rows. *)
rowFilterPredicates = {
	(RGet[#, answer] != 0)&, (* Incorrect comprehension question answer. *)
	(RGet[#, newline] != 1)&,
	(RGet[#, time] <= 1500)&,
	(* ((sentencehash /. #) == "0610f6f9f56b707518a530ad3761adb3")& *)
};
ListOr[l_] := Fold[Or, False, l];
MApply[fs_, x_] := Map[Function[f, f[x]], fs];
RemoveBadRows[csv_] := Select[csv, Function[row, ListOr[MApply[rowFilterPredicates, row]]]];

(* Add normalized reading times with matching confidence intervals
   to each row. *)
AddNormalizedReadingTimes[rcsv_] :=
	Module[{overallmeantime = Mean[RMapField[rcsv, time]],
	        bysubject = Split[rcsv, (RGet[#1, date] == RGet[#2, date])&]},
	Module[
		{bysubjectwithnorms =
			Map[
				Function[subjrows,
					Module[{mean = Mean[RMapField[subjrows, time]]},
						Map[RAddField[#, normtime, RGet[#, time] - (mean - overallmeantime)]&, subjrows]
					]
				],
				bysubject
			]
		},
		Flatten[bysubjectwithnorms, 1]
	]];

(* Fit a linear model relating word length (independent) to
   normalized reading time (dependent) and raw reading time (dependent). *)
AddResidualReadingTimes[rcsvnorm_] :=
	Module[{npairs = RMapFields[rcsvnorm, {length, normtime}],
	        bpairs = RMapFields[rcsvnorm, {length, time}]},
	Module[{nequation = Fit[npairs, {1, var}, var],
	        bequation = Fit[bpairs, {1, var}, var]}, 
		(* Add a "nresidual" and "bresidual" fields to each row by subtracting the reading time
           predicted from the linear model from the normalized/bare reading time respectively. *)
		Map[
			RAddFields[
				#,
				{{nresidual, RGet[#, normtime] - (nequation /. (var -> RGet[#, length]))},
				 {bresidual, RGet[#, time] - (bequation /. (var -> RGet[#, length]))}
			    }
			]&,
			rcsvnorm
		]
	]];

Cap3SD[rcsv_, field_] :=
	Module[{xs = RMapField[rcsv, field]},
	Module[{lim = Mean[xs] + (StandardDeviation[xs] * 3)},
		Map[If[RGet[#, field] > lim, RSet[#, field, lim], #]&,
			rcsv]
	]];

(* Processing for experiment 1. *)
Exp1[rcsv_] :=
	(* Change the type of the sentence mistakenly taken from the wrong dataset
	   to that of a filler. *)
	Module[{rcsv2 = ChangeTypeByHash[rcsv, "0610f6f9f56b707518a530ad3761adb3", -1]},
	(* Remove rows that are invalid for various reasons (e.g. incorrect comprehension
	   question answer. *)
    rcsv2 = RemoveBadRows[rcsv2];
	(*rcsv2 = Map[If[RGet[#, time] > 1000, RSet[#, time, 1000], #]&, rcsv2];*)
	rcsv2 = AddNormalizedReadingTimes[rcsv2];
	rcsv2 = AddResidualReadingTimes[rcsv2];
	rcsv2 = Cap3SD[rcsv2, time];
	rcsv2 = Cap3SD[rcsv2, normtime];
	rcsv2 = Cap3SD[rcsv2, bresidual];
	rcsv2 = Cap3SD[rcsv2, nresidual];
	rcsv2
	];

NumSubjects[rcsv_] := Length[Union[Map[RGet[#, date]&, rcsv]]];

SubjectFieldMeans[rcsv_, field_] :=
	Map[Mean[RMapField[#, field]]&,
	    Split[rcsv, (RGet[#1, date] == RGet[#2, date])&]];

(* Either of these can be used to determine confidence intervals by
   MeanField. *)
TTestCI[x_] := MeanCI[x, KnownVariance -> None, ConfidenceLevel -> 0.95];
SDCI[x_] := Module[{sd = StandardDeviation[x], m = Mean[x]}, {m - (sd/2), m + (sd/2)}];

MeanField[rows_, field_] :=
	Module[{nwords = Max[RMapField[rows, word]],
            cifunc = TTestCI},
		Table[
			Module[{rowsforword = Select[rows, (RGet[#, word] == n)&]},
			Module[{groupmeans = SubjectFieldMeans[rowsforword, field]},
				{ Mean[Map[RGet[#, field]&, rowsforword]],
				  cifunc[groupmeans]
				}
			]],
			{n, nwords}
		]
	];

MeanFieldNoCI[rows_, field_] :=
	Module[{nwords = Max[RMapField[rows, word]]},
		Table[
			Module[{rowsforword = Select[rows, (RGet[#, word] == n)&]},
				Mean[Map[RGet[#, field]&, rowsforword]]
			],
			{n, nwords}
		]
	];

MeanFieldForType[rows_, t_, field_] :=
	MeanField[Select[rows, (RGet[#, type] == t)&], field];

MeanFieldNoCIForType[rows_, t_, field_] :=
	MeanFieldNoCI[Select[rows, (RGet[#, type] == t)&], field];

TTestAt[rcsv_, w_, t1_, t2_, field_ : normtime] :=
	Module[{atword = Select[rcsv, (RGet[#, word] == w)&]},
		(* Uses a t test. *)
		MeanDifferenceTest[
			SubjectFieldMeans[Select[atword, (RGet[#, type] == t1)&], field],
			SubjectFieldMeans[Select[atword, (RGet[#, type] == t2)&], field],
			0, (* Difference for null hypothesis. *)
			TwoSided -> True,
			EqualVariances -> False,
			KnownVariance -> None
		]
	];

Flatten1[l_] := Flatten[l, 1];

Solid = Dashing[{}];

lineStyleSequence = { {Black, Solid}, {Black, DotDashed}, {Black, Dotted}, {Black, Dashed}};
arrowStyleSequence = { {Poly, Solid}, {Line, Solid}, {Line, Dotted}, {Line, Dashed} };

Options[DrawErrorBars] = { Height -> 3, Width -> 0.5 };
DrawErrorBars[x_, interval_, stylespec_, OptionsPattern[]] :=
	Module[{w = OptionValue[Width] / 2,
	        lineorpoly = stylespec[[1]],
			style = stylespec[[2]]},
	Module[{top = {{x - w, interval[[1]]}, {x + w, interval[[1]]}, { x, interval[[1]] + OptionValue[Height] }},
	        bot = {{x - w, interval[[2]]}, {x + w, interval[[2]]}, { x, interval[[2]] - OptionValue[Height] }}},
		If[MatchQ[lineorpoly, Line],
			{style, Line[Join[top, {top[[1]]}]], Line[Join[bot, {bot[[1]]}]]},
			{style, Polygon[top], Polygon[bot]}
		]
	]];

Disp[x_] := (Print[FullForm[x]]; x);
Options[PlotForTypes] = {
	Legend -> {"Finite", "Non-finite"},
	YField -> normtime,
	AxesLabel -> {"Word", "Mean normalized reading time / ms"},
	MaxX -> 17,
	ErrorBarHeight -> 2
};
PlotForTypes[rcsv_, tlist_, OptionsPattern[]] :=
	Module[{points = Map[Function[t, Take[MeanFieldForType[rcsv, t, OptionValue[YField]], OptionValue[MaxX]]], tlist]},
	(* Find range of confidence intervals to determine range of y axis. *)
	Module[{intervals = Flatten[Map[{#[[2,1]], #[[2,2]]}&, Flatten1[points]]]},
	Module[{maxi = Max[intervals], mini = Min[intervals]},
		ShowLegend[
		ListLinePlot[
			Map[Map[#[[1]]&, #]&, points],
			PlotMarkers -> (*{Automatic, 5}*) None,
			PlotStyle -> lineStyleSequence,
			PlotRange -> {{0, OptionValue[MaxX] + 1}, {mini, maxi + OptionValue[ErrorBarHeight]}},
			AxesOrigin -> {0, mini},
			Frame -> True,
			RotateLabel -> True,
			FrameLabel -> OptionValue[AxesLabel],
			Epilog ->
			(* Draw vertical lines. *)
			MapIndexed[
				Function[{ptpr, i},
					Module[{ys = Flatten1[Map[{#[[2,1]], #[[2,2]]}&, ptpr]]},
						{Gray, Thin,
					     Line[{{First[i], Min[ys] + OptionValue[ErrorBarHeight]},
					           {First[i], Max[ys] - OptionValue[ErrorBarHeight]}}]}
					]
				],
				MapThread[{#1, #2}&, points]
			]
			~Join~
			(* Draw confidence interval markers. *)
			Flatten1[
				MapIndexed[
					Function[{ps, i},
						MapIndexed[Function[{p, j},
						           DrawErrorBars[First[j], p[[2]],
						                         arrowStyleSequence[[First[i]]],
						                         Height -> OptionValue[ErrorBarHeight]]],
						           ps]
					],
					points
				]
			]
		],
		{
		  MapThread[
			{Graphics[{#1,
			           (*{*){(*Thick,*) Line[{{0,0}, {2, 0}}]}(*,
			            DrawErrorBars[6, {-1.25, 1.25}, #3, Width -> 2.5, Height -> 0.75]}*)}],
		     Style[#2, Larger]
			}&,
			{Take[Map[#[[2]]&, lineStyleSequence], Length[OptionValue[Legend]]],
			 OptionValue[Legend],
			 Take[arrowStyleSequence, Length[OptionValue[Legend]]]}
		  ],
		  LegendPosition -> {0.4, 0.5},
		  LegendSize -> 0.5,
		  LegendShadow -> {0, 0},
		  LegendBorder -> Gray
		}]
	]]];

Options[PlotForIndividuals] = {
	MaxX -> 17,
	YField -> normtime
};
PlotForIndividuals[rcsv_, dates_, types_, OptionsPattern[]] :=
	Module[{filteredrcsv = Select[rcsv, MemberQ[dates, RGet[#, date]]&]},
		ListLinePlot[
			Map[Function[t, Take[MeanFieldNoCIForType[filteredrcsv, t, OptionValue[YField]], OptionValue[MaxX]]], types],
			PlotStyle -> lineStyleSequence,
			PlotMarkers -> Automatic
		]
	];

LengthAgainstTimePlot[rcsv_] :=
	ListPlot[
		MapThread[{#1,#2}&, {RMapField[rcsv, length], RMapField[rcsv, time]}],
		Frame -> True,
		FrameLabel -> {"Word length", "Reading time / ms"}
	];

EndPackage[];
