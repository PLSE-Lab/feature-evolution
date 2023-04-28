Introduction
------------

This repository contains the code used for exploring feature evolution in PHP.

An Important Note
-----------------

We are currently working to make this code easily runnable. One challenge is
that the parsing process takes a significant amount of time: roughly a week
on a newer Mac laptop. The serialized parse trees are roughly 40 GB, so are not
easily posted for download.

Step 1: Getting the Code to Analyze
------------------------------------

The projects we are analyzing are all on GitHub:

* Moodle: [https://github.com/moodle/moodle](https://github.com/moodle/moodle)
* MediaWiki: [https://github.com/wikimedia/mediawiki](https://github.com/wikimedia/mediawiki)
* phpBB: [https://github.com/phpbb/phpbb](https://github.com/phpbb/phpbb)
* WordPress: [https://github.com/WordPress/WordPress](https://github.com/WordPress/WordPress)

The first step is to clone these projects locally. All projects should be in the same directory. In our case, we put the cloned systems into PHPAnalysis/systems, where the PHPAnalysis directory is also where other extracted information (such as the serialized ASTs) will go. This can be done in two different ways. First, you can just use a standard `git clone` command in the PHPAnalysis/systems directory, e.g., `git clone https://github.com/WordPress/WordPress` to clone the WordPress project. We want to do a regular clone so we bring in all the history, since the analysis will need it.

The second option is to use the rascal-git project. You can use the `cloneRemoteRepository` function
to clone a GitHub repository to a local directory:

```
inport util::git::Git;
cloneRemoteRepository("https://github.com/phpbb/phpbb.git",|file:///PHPAnalysis/systems/phpBB|);
```

Step 2: Parsing the Code
------------------------

*Warning*: parsing the code will take a very, very long time (multiple days).

To parse all the code for a specific system, you can use the `buildTags` function
in the `RepoUtils` module. For instance, the following will build all the tagged
versions of WordPress, given the WordPress repo:

```
import lang::php::utils::RepoUtils;
buildTags("wordpress", |file:///PHPAnalysis/systems/WordPress|);
```

Note that the repository has to be opened first. If you just cloned it, it will be
already open. If not, you have to run `openLocalRepository(|file:///PHPAnalysis/systems/WordPress|)`
first to open it. To open all the repositories for all four systems in the analysis, you
can also run the `openRepositories()` function:

```
import lang::php::features::Features;
openRepositories();
```

The repository needs to be opened for any Git operations. Here, we need to get all the
tags to know which versions exist.

Step 3: Configuring the Analysis
--------------------------------

The paths in the file `src/main/rascal/lang/php/Features.rsc` need to be
changed. This includes `baseProjectDir`, which should point to the location of
this project; `baseSystemsDir`, which points to where the cloned systems are
stored; and `infoLoc` (if needed), although this is tied to the main configuration.
You should install `cloc`, then make sure `clocBinaryLoc` points to it. The location
`slocLoc` indicates where the information produced by `cloc` will be stored, but, like
`infoLoc`, it should not need to be changed.

Step 4: Extract the Summaries
-----------------------------

To save time, the analysis is performed on summaries of information about each system,
instead of directly on each system. The summaries can be extracted using the function 
`extractAndWriteSummaries`. This will extract all the summaries, saving them into
your PHPAnalysis folder under `serialized/ooSummaries`.

Step 5: Generate the Charts
---------------------------

Finally, if you run `makeCharts`, this will use the summaries to generate all the
charts that appear in the paper. You need to at least pass the location where
the charts will be stored, like `makeCharts(|file:///tmp|)` to put them into the `/tmp`
directory. The function takes a number of parameters, but, if the parameters are not
included, it will pull all the information it needs from the summaries created above.

