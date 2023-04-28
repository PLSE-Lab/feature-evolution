Introduction
------------

This repository contains the code used for exploring feature evolution in PHP.

An Important Note
-----------------

We are currently working to make this code easily runnable. One challenge is
that the parsing process takes a significant amount of time: roughly a week
on a newer Mac laptop. The serialized parse trees are roughly 40 GB, so are not
easily posted for download.

Running The Analysis
---------------------

First, the paths in the file `src/main/rascal/lang/php/Features.rsc` need to be
changed. This includes `baseProjectDir`, which should point to the location of
this project; `baseSystemsDir`, which points to where the cloned systems are
stored; and `infoLoc` (if needed), although this is tied to the main configuration.
You should install `cloc`, then make sure `clocBinaryLoc` points to it. The location
`slocLoc` indicates where the information produced by `cloc` will be stored, but, like
`infoLoc`, it should not need to be changed.

Second, the systems need to be parsed.

Third, the summaries can be extracted using the function 
`extractAndWriteSummaries`. This will extract all the summaries, saving them into
your PHPAnalysis folder under `serialized/ooSummaries`.

Finally, if you run `makeCharts`, this will use the summaries to generate all the
charts that appear in the paper. You need to at least pass the location where
the charts will be stored, like `makeCharts(|file:///tmp|)` to put them into the `/tmp`
directory. The function takes a number of parameters, but, if the parameters are not
included, it will pull all the information it needs from the summaries created above.

