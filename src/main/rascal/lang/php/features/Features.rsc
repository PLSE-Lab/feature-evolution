module lang::php::features::Features

import lang::php::ast::AbstractSyntax;
import lang::php::ast::System;
import lang::php::util::Corpus;
import lang::php::util::Utils;
import lang::php::util::Config;
import lang::php::metrics::CC;
import lang::php::stats::Stats;
import lang::php::util::CLOC;

import util::git::Git;

import String;
import Set;
import List;
import ValueIO;
import IO;

// Other items to add:
// How much code is in classes?
// What is the average longevity of a class? Of a method?
// Interfaces?
// Exceptions: how many throws? how many try/catch blocks? how many catches?
// Namespaces: are they being used? is code being transitioned to this?
// Closures? (Not really OO, but may be interesting)

// NOTE: This is the location of this project. You should
// change this to match the location on your system. This
// is needed to load the files in the data directory which
// contain the tags being analyzed.
private loc baseProjectDir = |file:///Users/hillsma/Projects/php-analysis/feature-evolution|;

private map[str,loc] tagFiles =
	(
		"wordpress" : baseProjectDir + "data/wptags.txt",
		"moodle" : baseProjectDir + "data/mdltags.txt",
		"mediawiki" : baseProjectDir + "data/mwtags.txt",
		"phpBB" : baseProjectDir + "data/bbtags.txt"
	);

@doc{
	Load the products/systems and tags that are being analyzed.
}
public rel[str product, str version] loadTags() {
	rel[str product, str version] res = { };
	for (p <- tagFiles<0>) {
		ptags = readFileLines(tagFiles[p]);
		for (v <- ptags) {
			res = res + < p, v >;
		}
	}
	return res;
}

// TODO: This should be updated to point to the correct directory
// where the Git repositories for the systems under analysis have
// been placed.
private loc baseSystemsDir = |file:///Users/hillsma/PHPAnalysis/systems|;

// These are the locations of the repositories. 
private map[str,loc] repositories =
	( "wordpress" : baseSystemsDir + "WordPress",
	  "moodle" : baseSystemsDir + "Moodle",
	  "mediawiki" : baseSystemsDir + "MediaWiki",
	  "phpBB" : baseSystemsDir + "phpBB" 
	);

public map[str,loc] getRepositories() = repositories;

@doc{
	Open the Git repositories for the systems under analysisl
	This needs to be done before any operations that need access
	to repository information, such as reading the tags from the
	repository or switching to a specific tagged release.
}
public void openRepositories() {
	for (s <- repositories<0>) {
		openLocalRepository(repositories[s]);
	}
}

@doc{
	Summaries of the entire system, as well as specific aspects of the
	system. These are computed and used in the analyses below.
}
data Summary 
	= systemSummary(
		rel[loc cloc, Summary csum] classes, 
		rel[loc iloc, Summary isum] interfaces, 
		rel[loc floc, Summary fsum] functions, 
        rel[loc eloc, Summary esum] exceptions, 
		rel[loc tloc, Summary tsum] traits,
        int functionCallCount, 
		int methodCallCount, 
		int staticCallCount, 
		int stmtCount, 
        int exprCount, 
		map[str,int] topFunctions, 
		int throwCount, 
        int traitUseCount, 
		int traitUseNameCount,
        VarFeatureSummary varFeatures, 
		MagicMethodSummary magicMethods, 
		IncludeSummary includes, 
        EvalLikeSummary evalLikes, 
		InvocationSummary invocations)
	| classSummary(str className, set[Summary] methods, set[Modifier] modifiers, int expCount, 
        int stmtCount, loc at)
	| interfaceSummary(str className, set[Summary] methods, loc at)
	| methodSummary(str methodName, int expCount, int stmtCount, set[Modifier] modifiers, 
        int cc, loc at)
	| functionSummary(str functionName, int expCount, int stmtCount, int cc, loc at)
	| exceptionSummary(int expCount, int stmtCount, int catches, bool hasFinally, loc at)
    | traitSummary(str traitName, set[Summary] methods, loc at)
    // TODO: Add support for enums if we want to analyze those
	;

@doc{
	Given an input System, extract a Summary for the System.
}
public Summary extractSummaries(System sys) {
	rel[loc cloc, Summary csum] classSummaries = { };
	rel[loc iloc, Summary isum] interfaceSummaries = { };
    rel[loc tloc, Summary tsum] traitSummaries = { };
	rel[loc floc, Summary fsum] functionSummaries = { };
	rel[loc eloc, Summary esum] exceptionSummaries = { };
	map[str,int] callCounts = ( );
	int functionCallCount = 0;
	int methodCallCount = 0;
	int staticCallCount = 0;
	int throwCount = 0;
	int traitUseCount = 0;
	int traitUseNameCount = 0;

	for (l <- sys.files<0>) {
		visit(sys.files[l]) {
			case ClassDef cdef : {
				if (cdef is class) {
					Summary s = classSummary(cdef.className, {}, cdef.modifiers, size([st | /Stmt st := cdef]), size([ex | /Expr ex := cdef]), cdef.at);
					for (/ClassItem ci := cdef.members, ci is method) {
						s.methods = s.methods + methodSummary(ci.name, size([st | /Stmt st := ci.body]), size([ex | /Expr ex := ci.body]), ci.modifiers, 0 /*computeCC(ci.body)*/, ci.at);
					}
					classSummaries = classSummaries + < cdef.at, s >;
				} else {
					Summary s = classSummary("ANONYMOUS", {}, { }, size([st | /Stmt st := cdef]), size([ex | /Expr ex := cdef]), cdef.at);
					for (/ClassItem ci := cdef.members, ci is method) {
						s.methods = s.methods + methodSummary(ci.name, size([st | /Stmt st := ci.body]), size([ex | /Expr ex := ci.body]), ci.modifiers, 0 /*computeCC(ci.body)*/, ci.at);
					}
					classSummaries = classSummaries + < cdef.at, s >;
				}
			}

			case InterfaceDef idef: {
				Summary s = interfaceSummary(idef.interfaceName, {}, idef.at);
				for (/ClassItem ci := idef.members, ci is method) {
					s.methods = s.methods + methodSummary(ci.name, size([st | /Stmt st := ci.body]), size([ex | /Expr ex := ci.body]), ci.modifiers, 0 /*computeCC(ci.body)*/, ci.at);
				}
				interfaceSummaries = interfaceSummaries + < idef.at, s >;
			}

			case fdef:function(str name, _, _, list[Stmt] body, _, _): {
				// NOTE: can replace 0 with computeCC(body) to compute this, but slow and not needed right now
				Summary s = functionSummary(name, size([st | /Stmt st := body]), size([ex | /Expr ex := body]), 0, fdef.at);
				functionSummaries = functionSummaries + < fdef.at, s >;
			}

			case c:call(name(name(n)),_): {
				if (n in callCounts) {
					callCounts[n] = callCounts[n] + 1;
				} else {
					callCounts[n] = 1;
				}
				functionCallCount += 1;
			}

			case c:methodCall(_,_,_,_): {
				methodCallCount += 1;
			}

			case c:staticCall(_,_,_): {
				staticCallCount += 1;
			}

			case t:\throw(_): {
				throwCount += 1;
			}

			case tc:tryCatch(b,cl): {
				es = exceptionSummary(size([st | /Stmt st := b]), size([ex | /Expr ex := b]), size(cl), false, tc.at);
				exceptionSummaries = exceptionSummaries + < tc.at, es >;
			}

			case tcf:tryCatchFinally(b,cl,fb): {
				es = exceptionSummary(size([st | /Stmt st := b]), size([ex | /Expr ex := b]), size(cl), true, tcf.at);
				exceptionSummaries = exceptionSummaries + < tcf.at, es >;
			}

			case traitUse(traits, _): {
				traitUseCount += 1;
				traitUseNameCount += size(traits);
			}

			case TraitDef tdef: {
				Summary s = traitSummary(tdef.traitName, {}, tdef.at);
				for (/ClassItem ci := tdef.members, ci is method) {
					s.methods = s.methods + methodSummary(ci.name, size([st | /Stmt st := ci.body]), size([ex | /Expr ex := ci.body]), ci.modifiers, 0 /*computeCC(ci.body)*/, ci.at);
				}
				traitSummaries = traitSummaries + < tdef.at, s >;
			}
		}
	}	

	// These are easier to count separately, instead of adding them into the visit above
	int stmtCount = 0;
	int exprCount = 0;
	for (loc l <- sys.files<0>, /Stmt s := sys.files[l]) stmtCount += 1;
	for (loc l <- sys.files<0>, /Expr e := sys.files[l]) exprCount += 1;

	// Compute top function stats	
	ccList = reverse(sort([callCounts[cs] | cs <- callCounts]));
	top20 = (size(ccList) >= 20) ? [0..20] : [ ];
	cutoff = (size(ccList) >= 20) ? top20[-1] : 0;
	
	// Collect info for final summary of system
	return systemSummary(classSummaries, interfaceSummaries, functionSummaries, exceptionSummaries, 
		traitSummaries, functionCallCount, methodCallCount, staticCallCount, stmtCount, exprCount, 
        ( cs : callCounts[cs] | cs <- callCounts, callCounts[cs] > cutoff), 
        throwCount, traitUseCount, traitUseNameCount,
        getVarFeatureSummary(sys), getMagicMethodSummary(sys), getIncludeSummary(sys), 
		getEvalLikeSummary(sys), getInvocationSummary(sys));
}

@doc{
	Extract a summary for a specific product and version. This loads
	the serialized version of the ASTs for this System.
}
public Summary extractSummaries(str p, str v) {
	sys = loadBinary(p,v);
	return extractSummaries(sys);
}

@doc{
	Extract the summaries for all tags/versions of a specific product.
}
public map[str,Summary] extractSummaries(str p) {
	map[str,Summary] res = ( );
	for (v <- getTags(repositories[p])) {
		res[v] = extractSummaries(p, v);
	}
	return res;
}

@doc{
	Extract the summaries for all tags/versions of a specific product,
	writing them to disk for easy retrieval later.
}
public void extractAndWriteSummaries(str p) {
	for (v <- getTags(repositories[p])) {
		pt = loadBinary(p,v);
		s = extractSummaries(pt);
		writeSummary(p, v, s);
	}
}

@doc{
	Extract and write to disk summaries for all systems in the corpus.
}
public void extractAndWriteSummaries() {
	for (p <- repositories<0>) {
		extractAndWriteSummaries(p);
	}
}

@doc{
	Extract and write to disk just those summaries that are currently
	missing, i.e., that have not been extracted and serialized yet.
}
public void extractAndWriteMissingSummaries(str p) {
	for (v <- getTags(repositories[p]), !exists(infoLoc + "<p>-<v>-oo.bin")) {
		sys = loadBinary(p,v);
		s = extractSummaries(sys);
		writeSummary(p, v, s);
	}
}

@doc{The location of serialized OO Summary information}
private loc infoLoc = baseLoc + "serialized/ooSummaries";

@doc{Write a summary to disk}
public void writeSummary(str p, str v, Summary s) {
	writeBinaryValueFile(infoLoc + "<p>-<v>-oo.bin", s, compression=false);
}

@doc{Read a summary from disk for a specific product and version.}
public Summary readSummary(str p, str v) {
	logMessage("Loading summary for <p> version <v>", 1);
	return readBinaryValueFile(#Summary, infoLoc + "<p>-<v>-oo.bin");
}

@doc{
	Write all the summaries given in a map of summaries. The map is
	from versions to summaries.
}
public void writeSummaries(str p, map[str,Summary] smap) {
	for (v <- smap) writeSummary(p,v,smap[v]);
}

@doc {
	Read all summaries for a specific product into a map from versions
	to summaries.
}
public map[str,Summary] readSummaries(str p) {
	map[str,Summary] res = ( );
	for (v <- getTags(repositories[p]), exists(infoLoc + "<p>-<v>-oo.bin"))
		res[v] = readSummary(p,v);
	return res; 
}

public rel[str product, str version, int count] countClassDefs() {
	rel[str product, str version, int count] res = { };
	for (p <- repositories<0>) {
		for (v <- getTags(repositories[p])) {
			s = readSummary(p,v);
			res = res + < p, v, size(s.classes) >;
		}
	}
	return res;
}

public map[str,real] countClassDefsAsPercent(map[str,Summary] summaries) {
	return ( v : size(summaries[v].classes)*100.00/summaries[v].stmtCount | v <- summaries);
}

data VarFeatureItem
	= varVarUse(Expr e) 
	| varFunctionName(Expr e) 
	| varMethodName(Expr e) 
	| varClassNameNew(Expr e)
	| varPropertyName(Expr e)
	| varClassConst(Expr e)
	| varStaticMethodName(Expr e)
	| varStaticCallTargetName(Expr e)
	| varStaticPropertyName(Expr e)
	| varStaticPropertyTargetName(Expr e)
	;

data VarFeatureSummary = varFeatures(rel[loc vfloc, VarFeatureItem item] features);

public VarFeatureSummary getVarFeatureSummary(System sys) {
	rel[loc vfloc, VarFeatureItem item] items = { };
	for (l <- sys.files<0>) {
		visit(sys.files[l]) {
			case v:var(expr(_)) : 
				items = items + < v.at, varVarUse(v) >;
			case spf:staticPropertyFetch(expr(_),expr(_)) :
				items = items + < spf.at, varStaticPropertyName(spf) > + < spf.at, varStaticPropertyTargetName(spf) >;
			case spf:staticPropertyFetch(name(_),expr(_)) :
				items = items + < spf.at, varStaticPropertyName(spf) >;
			case spf:staticPropertyFetch(expr(_),name(_)) :
				items = items + < spf.at, varStaticPropertyTargetName(spf) >;
			case pf:propertyFetch(_,expr(_),_):
				items = items + < pf.at, varPropertyName(pf) >;
			case sc:staticCall(expr(_),expr(_),_):
				items = items + < sc.at, varStaticMethodName(sc) > + < sc.at, varStaticCallTargetName(sc) >;
			case sc:staticCall(name(_),expr(_),_):
				items = items + < sc.at, varStaticMethodName(sc) >;
			case sc:staticCall(expr(_),name(_),_):
				items = items + < sc.at, varStaticCallTargetName(sc) >;
			case c:call(expr(_),_):
				items = items + < c.at, varFunctionName(c) >;
			case mc:methodCall(_,expr(_),_,_):
				items = items + < mc.at, varMethodName(mc) >;
			case n:new(computedClassName(_),_):
				items = items + < n.at, varClassNameNew(n) >;
			case cc:fetchClassConst(expr(_),_):
				items = items + < cc.at, varClassConst(cc) >;
		}
	}
	return varFeatures(items);
}

data VarFeatureCounts = varFeatureCounts(int varVar, int varFCall, int varMCall, int varNew, int varProp, 
	int varClassConst, int varStaticCall, int varStaticTarget, int varStaticPropertyName, int varStaticPropertyTarget);

public VarFeatureCounts getVarFeatureCounts(VarFeatureSummary vfs) {
	int vvuses = size([ e | <_,e> <-  vfs.features, e is varVarUse]); 
	int vvcalls = size([ e | <_,e> <-  vfs.features, e is varFunctionName]); 
	int vvmcalls = size([ e | <_,e> <-  vfs.features, e is varMethodName]); 
	int vvnews = size([ e | <_,e> <-  vfs.features, e is varClassNameNew]); 
	int vvprops = size([ e | <_,e> <-  vfs.features, e is varPropertyName]); 
	int vvcconsts = size([ e | <_,e> <-  vfs.features, e is varClassConst]); 
	int vvscalls = size([ e | <_,e> <-  vfs.features, e is varStaticMethodName]); 
	int vvstargets = size([ e | <_,e> <-  vfs.features, e is varStaticCallTargetName]); 
	int vvsprops = size([ e | <_,e> <-  vfs.features, e is varStaticPropertyName]); 
	int vvsptargets = size([ e | <_,e> <-  vfs.features, e is varStaticPropertyTargetName]); 
	
	return varFeatureCounts(vvuses, vvcalls, vvmcalls, vvnews, vvprops, vvcconsts, vvscalls, vvstargets, vvsprops, vvsptargets); 
}

data MagicMethodItem
	= mmSetItem(ClassItem mmDef)
	| mmGetItem(ClassItem mmDef)
	| mmIssetItem(ClassItem mmDef)
	| mmUnsetItem(ClassItem mmDef)
	| mmCallItem(ClassItem mmDef)
	| mmCallStaticItem(ClassItem mmDef)
	;

data MagicMethodSummary = magicMethods(rel[loc mmloc, MagicMethodItem item] methods);

public MagicMethodSummary getMagicMethodSummary(System sys) {
	// These intercept method calls and property lookups
	overrideMethods = { "__set", "__get", "__isset", "__unset", "__call", "__callStatic" };

	// These handle more normal features, like constructors
	allMagicMethods = overrideMethods + { "__construct", "__destruct", "__sleep", "__wakeup", 
		"__serialize", "__unserialize", "__toString", "__invoke", "__set_state", "__clone", "__debugInfo" };

	// Find all override methods, this could be switched to all magic methods if need be
	defs = [ m | l <- sys.files<0>, /m:method(methodName,_,_,_,_,_,_) := sys.files[l], methodName in overrideMethods ];

	rel[loc vfloc, MagicMethodItem item] items = { };

	for (m <- defs) {
		switch(m.name) {
			case "__set":
				items = items + < m.at, mmSetItem(m) >;
			case "__get":
				items = items + < m.at, mmGetItem(m) >;
			case "__isset":
				items = items + < m.at, mmIssetItem(m) >;
			case "__unset":
				items = items + < m.at, mmUnsetItem(m) >;
			case "__call":
				items = items + < m.at, mmCallItem(m) >;
			case "__callStatic":
				items = items + < m.at, mmCallStaticItem(m) >;
		}
	}

	return magicMethods(items);
}

data MagicMethodCounts 
	= magicMethodCounts(int sets, int gets, int isSets, int unsets, int calls, int staticCalls);

public MagicMethodCounts getMagicMethodCounts(MagicMethodSummary msum) {

	sets = size([ e | <_,e> <-  msum.methods, e is mmSetItem]); 
	gets = size([ e | <_,e> <-  msum.methods, e is mmGetItem]); 
	isSets = size([ e | <_,e> <-  msum.methods, e is mmIssetItem]); 
	unsets = size([ e | <_,e> <-  msum.methods, e is mmUnsetItem]); 
	calls = size([ e | <_,e> <-  msum.methods, e is mmCallItem]); 
	staticCalls = size([ e | <_,e> <-  msum.methods, e is mmCallStaticItem]); 

	return magicMethodCounts(sets, gets, isSets, unsets, calls, staticCalls);
}

data IncludeItem
	= staticInclude(Expr e)
	| dynamicInclude(Expr e)
	;

data IncludeSummary = includeItems(rel[loc iloc, IncludeItem item] includes);

public IncludeSummary getIncludeSummary(System sys) {
	rel[loc vfloc, IncludeItem item] items = { };

	for (l <- sys.files<0>) {
		visit(sys.files[l]) {
			case i:include(Expr e,_):
				if (scalar(string(_)) !:= e) {
					items = items + <i.at, dynamicInclude(i) >;
				} else {
					items = items + <i.at, staticInclude(i) >;
				}
		}
	}

	return includeItems(items);
}

data IncludeCounts = includeCounts(int totalIncludes, int dynamicIncludes);

public IncludeCounts getIncludeCounts(IncludeSummary isum) {
	totalIncludes = size([ i | <_,i> <- isum.includes ]);
	dynamicIncludes = size([ i | <_,i> <- isum.includes, i is dynamicInclude ]);
	return includeCounts(totalIncludes, dynamicIncludes);
}

data EvalLikeItem
	= evalItem(Expr e)
	| createFunctionItem(Expr e)
	| closureItem(Expr e)
	;
	
data EvalLikeSummary = evalLikeItems(rel[loc eloc, EvalLikeItem item] evalLikes);

public EvalLikeSummary getEvalLikeSummary(System sys) {
	rel[loc vfloc, EvalLikeItem item] items = { };

	for (l <- sys.files<0>) {
		visit(sys.files[l]) {
			case e:eval(_):
				items = items + < e.at, evalItem(e) >;
			case cf:call(name(name("create_function")),_):
				items = items + < cf.at, createFunctionItem(cf) >;
			case cl:closure(_,_,_,_,_,_,_):
				items = items + < cl.at, closureItem(cl) >;
		}
	}

	return evalLikeItems(items);
}

data EvalLikeCounts = evalLikeCounts(int evalCount, int createFunctionCount, int closureCount);

public EvalLikeCounts getEvalLikeCounts(EvalLikeSummary esum) {
	createFunctionCount = size([ e | <_,e> <- esum.evalLikes, e is createFunctionItem ]);
	evalCount = size([ e | <_,e> <- esum.evalLikes, e is evalItem ]);
	closureCount = size([ e | <_,e> <- esum.evalLikes, e is closureItem ]);
	return evalLikeCounts(evalCount, createFunctionCount, closureCount);
}

data InvocationItem
	= callUserFuncItem(Expr e)
	| callUserFuncArrayItem(Expr e)
	| callUserMethodItem(Expr e)
	| callUserMethodArrayItem(Expr e)
	| forwardStaticCallItem(Expr e)
	| forwardStaticCallArrayItem(Expr e)
	;

data InvocationSummary = invocationItems(rel[loc iloc, InvocationItem item] invocations);

public InvocationSummary getInvocationSummary(System sys) {
	// Special invocation functions
	funsToFind = { "call_user_func", "call_user_func_array", "call_user_method", 
		"call_user_method_array", "forward_static_call", "forward_static_call_array" };

	// Find all calls of these functions
	defs = [ < c, fname > | l <- sys.files<0>, /c:call(name(name(fname)),_) := sys.files[l], fname in funsToFind ];

	rel[loc iloc, InvocationItem item] items = { };

	for (< c, fname > <- defs) {
		switch(fname) {
			case "call_user_func":
				items = items + < c.at, callUserFuncItem(c) >;
			case "call_user_func_array":
				items = items + < c.at, callUserFuncArrayItem(c) >;
			case "call_user_method":
				items = items + < c.at, callUserMethodItem(c) >;
			case "call_user_method_array":
				items = items + < c.at, callUserMethodArrayItem(c) >;
			case "forward_static_call":
				items = items + < c.at, forwardStaticCallItem(c) >;
			case "forward_static_call_array":
				items = items + < c.at, forwardStaticCallArrayItem(c) >;
		}
	}

	return invocationItems(items);
}

data InvocationCounts = invocationCounts(int callUserFuncCount, int callUserFuncArrayCount, int callUserMethodCount, int callUserMethodArrayCount, int forwardStaticCallCount, int forwardStaticCallArrayCount);

public InvocationCounts getInvocationCounts(InvocationSummary isum) {
	callUserFuncCount = size([ e | <_,e> <-  isum.invocations, e is callUserFuncItem]); 
	callUserFuncArrayCount = size([ e | <_,e> <-  isum.invocations, e is callUserFuncArrayItem]); 
	callUserMethodCount = size([ e | <_,e> <-  isum.invocations, e is callUserMethodItem]); 
	callUserMethodArrayCount = size([ e | <_,e> <-  isum.invocations, e is callUserMethodArrayItem]); 
	forwardStaticCallCount = size([ e | <_,e> <-  isum.invocations, e is forwardStaticCallItem]); 
	forwardStaticCallArrayCount = size([ e | <_,e> <-  isum.invocations, e is forwardStaticCallArrayItem]); 
	
	return invocationCounts(callUserFuncCount, callUserFuncArrayCount, callUserMethodCount, callUserMethodArrayCount, forwardStaticCallCount, forwardStaticCallArrayCount);
}

public list[int] getNumbersForSystem(Summary s) {
	list[int] stats = [ s.exprCount, s.stmtCount ];
	
	VarFeatureCounts vc = getVarFeatureCounts(s.varFeatures);
	varStats = [ vc.varVar, vc.varFCall, vc.varMCall, vc.varNew, vc.varProp, vc.varClassConst, vc.varStaticCall, vc.varStaticTarget, vc.varStaticPropertyName, vc.varStaticPropertyTarget, sum([vc.varVar, vc.varFCall, vc.varMCall, vc.varNew, vc.varProp, vc.varClassConst, vc.varStaticCall, vc.varStaticTarget, vc.varStaticPropertyName, vc.varStaticPropertyTarget]) ];
	
	MagicMethodCounts mc = getMagicMethodCounts(s.magicMethods);
	magicStats = [ mc.sets, mc.gets, mc.isSets, mc.unsets, mc.calls, mc.staticCalls, sum([mc.sets, mc.gets, mc.isSets, mc.unsets, mc.calls, mc.staticCalls]) ];
	
	IncludeCounts ic = getIncludeCounts(s.includes);
	includeStats = [ ic.totalIncludes, ic.dynamicIncludes ];
	
	EvalLikeCounts ec = getEvalLikeCounts(s.evalLikes);
	evalStats = [ ec.evalCount, ec.createFunctionCount, sum([ec.evalCount, ec.createFunctionCount]) ];
	
	InvocationCounts ivc = getInvocationCounts(s.invocations); 	
	invokeStats = [ ivc.callUserFunc, ivc.callUserFuncArray, ivc.callUserMethod, ivc.callUserMethodArray, sum([ivc.callUserFunc, ivc.callUserFuncArray, ivc.callUserMethod, ivc.callUserMethodArray]) ];
	
	return stats + varStats + magicStats + includeStats + evalStats + invokeStats;	
}

public list[str] getColumnHeaders() {
	list[str] res = [ "System", "Version", "SLOC", "Files", "Exprs", "Stmts", 
		"Variable Variables", "Variable Function Calls", "Variable Method Calls", "Variable News", "Variable Properties",
		"Variable Class Constants", "Variable Static Calls", "Variable Static Targets", "Variable Static Properties", "Variable Static Property Targets",
		"All Variable Features",
		"Magic Sets", "Magic Gets", "Magic isSets", "Magic Unsets", "Magic Calls", "Magic Static Calls",
		"All Magic Methods",
		"Total Includes", "Dynamic Includes",
		"Eval", "Create Function Uses", "All Eval Features",
		"CallUserFunc", "CallUserFuncArray", "CallUserMethod", "CallUserMethodArray",
		"All Dynamic Invocations"];
	return res;
}

public str generateNumbersFile(set[str] systems) {
	str res = intercalate(",",getColumnHeaders()) + "\n";
	slocInfo = sloc();
	for (s <- sort(toList(systems)), v <- getSortedVersions(s)) {
		< lineCount, fileCount > = getOneFrom(slocInfo[s,v]);
		res = res + "<s>,<v>,<lineCount>,<fileCount>,<intercalate(",",getNumbersForSystem(readSummary(s,v)))>\n";
	}
	return res;
}

public void writeNumbersFile(set[str] systems) {
	for (s <- systems) {
		fileText = generateNumbersFile({s});
		writeFile(|project://SANER%202015/src/lang/php/experiments/saner2015/dynamic-<s>.csv|, fileText);
	}
}

private lrel[num,num] computeCoords(list[num] inputs) {
	return [ < idx+1, inputs[idx] > | idx <- index(inputs) ];
}

str computeTicks(str s) {
	vlist = getSortedVersions(s);
	displayThese = [ idx+1 | idx <- index(vlist), ((idx+1)%10==1) || (idx==size(vlist)-1) ];
	return "xtick={<intercalate(",",displayThese)>}";
}

str computeTickLabels(str s) {
	vlist = getSortedVersions(s);
	displayThese = [ vlist[idx] | idx <- index(vlist), ((idx+1)%10==1) || (idx==size(vlist)-1) ];
	return "xticklabels={<intercalate(",",displayThese)>}";
}

private str makeCoords(list[num] inputs, str mark="", str markExtra="", str legend="") {
	return "\\addplot<if(size(mark)>0){>[mark=<mark><if(size(markExtra)>0){>,<markExtra><}>]<}> coordinates {
		   '<intercalate(" ",[ "(<i>,<j>)" | < i,j > <- computeCoords(inputs)])>
		   '};<if(size(legend)>0){>
		   '\\addlegendentry{<legend>}<}>";
}

public str varFeaturesChart(map[str,map[str,Summary]] smap, str s, str title="Variable Features", str label="fig:VarFeatures", str markExtra="") {
	list[str] coordinateBlocks = [ ];
	coordinateBlocks += makeCoords([ smap[s][v].varFeatures.varVar | v <- getSortedVersions(s), v in smap[s] ], mark="square", markExtra=markExtra, legend="Variables");
	coordinateBlocks += makeCoords([ smap[s][v].varFeatures.varFCall | v <- getSortedVersions(s), v in smap[s] ], mark="x", markExtra=markExtra, legend="Function Calls");
	coordinateBlocks += makeCoords([ smap[s][v].varFeatures.varMCall | v <- getSortedVersions(s), v in smap[s] ], mark="o", markExtra=markExtra, legend="Method Calls");
	coordinateBlocks += makeCoords([ smap[s][v].varFeatures.varNew | v <- getSortedVersions(s), v in smap[s] ], mark="+", markExtra=markExtra, legend="Object Creation");
	coordinateBlocks += makeCoords([ smap[s][v].varFeatures.varProp | v <- getSortedVersions(s), v in smap[s] ], mark="*", markExtra=markExtra, legend="Property Uses");

	int maxcoord(str s) {
		return max([ smap[s][v].varFeatures.varVar | v <- getSortedVersions(s), v in smap[s] ] +
				   [ smap[s][v].varFeatures.varFCall | v <- getSortedVersions(s), v in smap[s] ] +
				   [ smap[s][v].varFeatures.varMCall | v <- getSortedVersions(s), v in smap[s] ] +
				   [ smap[s][v].varFeatures.varNew | v <- getSortedVersions(s), v in smap[s] ] +
				   [ smap[s][v].varFeatures.varProp | v <- getSortedVersions(s), v in smap[s] ]) + 10;
	}
		
	str res = "\\begin{figure*}
			  '\\centering
			  '\\begin{tikzpicture}
			  '\\begin{axis}[width=\\textwidth,height=.25\\textheight,xlabel=Version,ylabel=Feature Count,xmin=1,ymin=0,xmax=<size(getSortedVersions(s))>,ymax=<maxcoord(s)>,legend style={at={(0,1)},anchor=north west},x tick label style={rotate=90,anchor=east},<computeTicks(s)>,<computeTickLabels(s)>]
			  '<for (cb <- coordinateBlocks) {> <cb> <}>
			  '\\end{axis}
			  '\\end{tikzpicture}
			  '\\caption{<title>.\\label{<label>}} 
			  '\\end{figure*}
			  ";
	return res;	
}

public str varFeaturesScaledChart(map[str,map[str,Summary]] smap, str s, str title="Variable Features Scaled", str label="fig:VarFeaturesScaled", str markExtra="") {
	list[str] coordinateBlocks = [ ];
	slocInfo = sloc();
	
	coordinateBlocks += makeCoords([ smap[s][v].varFeatures.varVar * 100.0 / lineCount | v <- getSortedVersions(s), v in smap[s], < lineCount, fileCount > := getOneFrom(slocInfo[s,v]) ], mark="square", markExtra=markExtra, legend="Variables");
	coordinateBlocks += makeCoords([ smap[s][v].varFeatures.varFCall * 100.0 / lineCount | v <- getSortedVersions(s), v in smap[s], < lineCount, fileCount > := getOneFrom(slocInfo[s,v]) ], mark="x", markExtra=markExtra, legend="Function Calls");
	coordinateBlocks += makeCoords([ smap[s][v].varFeatures.varMCall * 100.0 / lineCount | v <- getSortedVersions(s), v in smap[s], < lineCount, fileCount > := getOneFrom(slocInfo[s,v]) ], mark="o", markExtra=markExtra, legend="Method Calls");
	coordinateBlocks += makeCoords([ smap[s][v].varFeatures.varNew * 100.0 / lineCount | v <- getSortedVersions(s), v in smap[s], < lineCount, fileCount > := getOneFrom(slocInfo[s,v]) ], mark="+", markExtra=markExtra, legend="Object Creation");
	coordinateBlocks += makeCoords([ smap[s][v].varFeatures.varProp * 100.0 / lineCount | v <- getSortedVersions(s), v in smap[s], < lineCount, fileCount > := getOneFrom(slocInfo[s,v]) ], mark="*", markExtra=markExtra, legend="Property Uses");
	num maxcoord(str s) {
		return max([ smap[s][v].varFeatures.varVar * 100.0 / lineCount | v <- getSortedVersions(s), v in smap[s], < lineCount, fileCount > := getOneFrom(slocInfo[s,v]) ] +
				   [ smap[s][v].varFeatures.varFCall * 100.0 / lineCount | v <- getSortedVersions(s), v in smap[s], < lineCount, fileCount > := getOneFrom(slocInfo[s,v]) ] +
				   [ smap[s][v].varFeatures.varMCall * 100.0 / lineCount | v <- getSortedVersions(s), v in smap[s], < lineCount, fileCount > := getOneFrom(slocInfo[s,v]) ] +
				   [ smap[s][v].varFeatures.varNew * 100.0 / lineCount | v <- getSortedVersions(s), v in smap[s], < lineCount, fileCount > := getOneFrom(slocInfo[s,v]) ] +
				   [ smap[s][v].varFeatures.varProp * 100.0 / lineCount | v <- getSortedVersions(s), v in smap[s], < lineCount, fileCount > := getOneFrom(slocInfo[s,v]) ]) ;
	}
		
	str res = "\\begin{figure}
			  '\\centering
			  '\\begin{tikzpicture}
			  '\\begin{axis}[width=\\columnwidth,height=.25\\textheight,xlabel=Version,ylabel=Feature Count,xmin=1,ymin=0,xmax=<size(getSortedVersions(s))>,ymax=<maxcoord(s)>,legend style={at={(0,1)},anchor=north west},x tick label style={rotate=90,anchor=east},<computeTicks(s)>,<computeTickLabels(s)>]
			  '<for (cb <- coordinateBlocks) {> <cb> <}>
			  '\\end{axis}
			  '\\end{tikzpicture}
			  '\\caption{<title>.\\label{<label>}} 
			  '\\end{figure}
			  ";
	return res;	
}

public str magicMethodsChart(map[str,map[str,Summary]] smap, str s, str title="Magic Methods", str label="fig:MagicMethods", str markExtra="") {
	list[str] coordinateBlocks = [ ];
	coordinateBlocks += makeCoords([ smap[s][v].magicMethods.sets | v <- getSortedVersions(s), v in smap[s] ], mark="x", markExtra=markExtra, legend="Property Sets");
	coordinateBlocks += makeCoords([ smap[s][v].magicMethods.gets | v <- getSortedVersions(s), v in smap[s] ], mark="o", markExtra=markExtra, legend="Property Gets");
	coordinateBlocks += makeCoords([ smap[s][v].magicMethods.calls | v <- getSortedVersions(s), v in smap[s] ], mark="+", markExtra=markExtra, legend="Calls");

	int maxcoord(str s) {
		return max([ smap[s][v].magicMethods.sets | v <- getSortedVersions(s), v in smap[s] ] +
				   [ smap[s][v].magicMethods.gets | v <- getSortedVersions(s), v in smap[s] ] +
				   [ smap[s][v].magicMethods.calls | v <- getSortedVersions(s), v in smap[s] ]) + 10;
	}
		
	str res = "\\begin{figure}
			  '\\centering
			  '\\begin{tikzpicture}
			  '\\begin{axis}[width=\\columnwidth,height=.25\\textheight,xlabel=Version,ylabel=Feature Count,xmin=1,ymin=0,xmax=<size(getSortedVersions(s))>,ymax=<maxcoord(s)>,legend style={at={(0,1)},anchor=north west},x tick label style={rotate=90,anchor=east},<computeTicks(s)>,<computeTickLabels(s)>]
			  '<for (cb <- coordinateBlocks) {> <cb> <}>
			  '\\end{axis}
			  '\\end{tikzpicture}
			  '\\caption{<title>.\\label{<label>}} 
			  '\\end{figure}
			  ";
	return res;	
}

public str magicMethodsScaledChart(map[str,map[str,Summary]] smap, str s, str title="Magic Methods", str label="fig:MagicMethods", str markExtra="") {
	list[str] coordinateBlocks = [ ];
	slocInfo = sloc();

	coordinateBlocks += makeCoords([ smap[s][v].magicMethods.sets * 100.0 / lineCount | v <- getSortedVersions(s), v in smap[s], < lineCount, fileCount > := getOneFrom(slocInfo[s,v]) ], mark="x", markExtra=markExtra, legend="Property Sets");
	coordinateBlocks += makeCoords([ smap[s][v].magicMethods.gets * 100.0 / lineCount | v <- getSortedVersions(s), v in smap[s], < lineCount, fileCount > := getOneFrom(slocInfo[s,v]) ], mark="o", markExtra=markExtra, legend="Property Gets");
	coordinateBlocks += makeCoords([ smap[s][v].magicMethods.calls * 100.0 / lineCount | v <- getSortedVersions(s), v in smap[s], < lineCount, fileCount > := getOneFrom(slocInfo[s,v]) ], mark="+", markExtra=markExtra, legend="Calls");
	num maxcoord(str s) {
		return max([ smap[s][v].magicMethods.sets * 100.0 / lineCount | v <- getSortedVersions(s), v in smap[s], < lineCount, fileCount > := getOneFrom(slocInfo[s,v]) ] +
				   [ smap[s][v].magicMethods.gets * 100.0 / lineCount | v <- getSortedVersions(s), v in smap[s], < lineCount, fileCount > := getOneFrom(slocInfo[s,v]) ] +
				   [ smap[s][v].magicMethods.calls * 100.0 / lineCount | v <- getSortedVersions(s), v in smap[s], < lineCount, fileCount > := getOneFrom(slocInfo[s,v]) ]);
	}
		
	str res = "\\begin{figure}
			  '\\centering
			  '\\begin{tikzpicture}
			  '\\begin{axis}[width=\\columnwidth,height=.25\\textheight,xlabel=Version,ylabel=Feature Count,xmin=1,ymin=0,xmax=<size(getSortedVersions(s))>,ymax=<maxcoord(s)>,legend style={at={(0,1)},anchor=north west},x tick label style={rotate=90,anchor=east},<computeTicks(s)>,<computeTickLabels(s)>]
			  '<for (cb <- coordinateBlocks) {> <cb> <}>
			  '\\end{axis}
			  '\\end{tikzpicture}
			  '\\caption{<title>.\\label{<label>}} 
			  '\\end{figure}
			  ";
	return res;	
}

public str evalsChart(map[str,map[str,Summary]] smap, str s, str title="Magic Methods", str label="fig:MagicMethods", str markExtra="") {
	list[str] coordinateBlocks = [ ];
	coordinateBlocks += makeCoords([ smap[s][v].evalCounts.evalCount | v <- getSortedVersions(s), v in smap[s] ], mark="x", markExtra=markExtra, legend="eval Uses");
	coordinateBlocks += makeCoords([ smap[s][v].evalCounts.createFunctionCount | v <- getSortedVersions(s), v in smap[s] ], mark="o", markExtra=markExtra, legend="create\\_function Uses");

	int maxcoord(str s) {
		return max([ smap[s][v].evalCounts.evalCount | v <- getSortedVersions(s), v in smap[s] ] +
				   [ smap[s][v].evalCounts.createFunctionCount | v <- getSortedVersions(s), v in smap[s] ]) + 10;
	}
		
	str res = "\\begin{figure}
			  '\\centering
			  '\\begin{tikzpicture}
			  '\\begin{axis}[width=\\columnwidth,height=.25\\textheight,xlabel=Version,ylabel=Feature Count,xmin=1,ymin=0,xmax=<size(getSortedVersions(s))>,ymax=<maxcoord(s)>,legend style={at={(0,1)},anchor=north west},x tick label style={rotate=90,anchor=east},<computeTicks(s)>,<computeTickLabels(s)>]
			  '<for (cb <- coordinateBlocks) {> <cb> <}>
			  '\\end{axis}
			  '\\end{tikzpicture}
			  '\\caption{<title>.\\label{<label>}} 
			  '\\end{figure}
			  ";
	return res;	
}

public str evalsScaledChart(map[str,map[str,Summary]] smap, str s, str title="Magic Methods", str label="fig:MagicMethods", str markExtra="") {
	list[str] coordinateBlocks = [ ];
	slocInfo = sloc();

	coordinateBlocks += makeCoords([ smap[s][v].evalCounts.evalCount * 100.0 / lineCount | v <- getSortedVersions(s), v in smap[s], < lineCount, fileCount > := getOneFrom(slocInfo[s,v]) ], mark="x", markExtra=markExtra, legend="eval Uses");
	coordinateBlocks += makeCoords([ smap[s][v].evalCounts.createFunctionCount * 100.0 / lineCount | v <- getSortedVersions(s), v in smap[s], < lineCount, fileCount > := getOneFrom(slocInfo[s,v]) ], mark="o", markExtra=markExtra, legend="create\\_function Uses");

	num maxcoord(str s) {
		return max([ smap[s][v].evalCounts.evalCount * 100.0 / lineCount | v <- getSortedVersions(s), v in smap[s], < lineCount, fileCount > := getOneFrom(slocInfo[s,v]) ] +
				   [ smap[s][v].evalCounts.createFunctionCount * 100.0 / lineCount | v <- getSortedVersions(s), v in smap[s], < lineCount, fileCount > := getOneFrom(slocInfo[s,v]) ]);
	}
		
	str res = "\\begin{figure}
			  '\\centering
			  '\\begin{tikzpicture}
			  '\\begin{axis}[width=\\columnwidth,height=.25\\textheight,xlabel=Version,ylabel=Feature Count,xmin=1,ymin=0,xmax=<size(getSortedVersions(s))>,ymax=<maxcoord(s)>,legend style={at={(0,1)},anchor=north west},x tick label style={rotate=90,anchor=east},<computeTicks(s)>,<computeTickLabels(s)>}}]
			  '<for (cb <- coordinateBlocks) {> <cb> <}>
			  '\\end{axis}
			  '\\end{tikzpicture}
			  '\\caption{<title>.\\label{<label>}} 
			  '\\end{figure}
			  ";
	return res;	
}

public map[str,map[str,Summary]] getSummaries(set[str] systems) {
	return ( s : ( v : readSummary(s,v) | v <- getVersions(s) ) | s <- systems );
}

public void makeCharts() {
	wpMarkExtra = "mark phase=1,mark repeat=5";
	mwMarkExtra = "mark phase=1,mark repeat=10";
	maMarkExtra = "mark phase=1,mark repeat=10";
	
	smap = getSummaries({"WordPress"});
	writeFile(|file:///tmp/wpVar.tex|, varFeaturesChart(smap, "WordPress", title="Variable Features in WordPress", label="fig:VFWP", markExtra=wpMarkExtra));
	writeFile(|file:///tmp/wpVarScaled.tex|, varFeaturesScaledChart(smap, "WordPress", title="Variable Features in WordPress, Scaled by SLOC", label="fig:VFWPScaled", markExtra=wpMarkExtra));
	writeFile(|file:///tmp/wpMagic.tex|, magicMethodsChart(smap, "WordPress", title="Magic Methods in WordPress", label="fig:MMWP", markExtra=wpMarkExtra));
	writeFile(|file:///tmp/wpMagicScaled.tex|, magicMethodsScaledChart(smap, "WordPress", title="Magic Methods in WordPress, Scaled by SLOC", label="fig:MMWPScaled", markExtra=wpMarkExtra));
	writeFile(|file:///tmp/wpEval.tex|, evalsChart(smap, "WordPress", title="Eval Constructs in WordPress", label="fig:EvalWP", markExtra=wpMarkExtra));
	writeFile(|file:///tmp/wpEvalScaled.tex|, evalsScaledChart(smap, "WordPress", title="Eval Constructs in WordPress, Scaled by SLOC", label="fig:EvalWPScaled", markExtra=wpMarkExtra));

	smap = getSummaries({"MediaWiki"});
	writeFile(|file:///tmp/mwVar.tex|, varFeaturesChart(smap, "MediaWiki", title="Variable Features in MediaWiki", label="fig:VFMW", markExtra=mwMarkExtra));
	writeFile(|file:///tmp/mwVarScaled.tex|, varFeaturesScaledChart(smap, "MediaWiki", title="Variable Features in MediaWiki, Scaled by SLOC", label="fig:VFMWScaled", markExtra=mwMarkExtra));
	writeFile(|file:///tmp/mwMagic.tex|, magicMethodsChart(smap, "MediaWiki", title="Magic Methods in MediaWiki", label="fig:MMMW", markExtra=mwMarkExtra));
	writeFile(|file:///tmp/mwMagicScaled.tex|, magicMethodsScaledChart(smap, "MediaWiki", title="Magic Methods in MediaWiki, Scaled by SLOC", label="fig:MMMWScaled", markExtra=mwMarkExtra));
	writeFile(|file:///tmp/mwEval.tex|, evalsChart(smap, "MediaWiki", title="Eval Constructs in MediaWiki", label="fig:EvalMW", markExtra=mwMarkExtra));
	writeFile(|file:///tmp/mwEvalScaled.tex|, evalsScaledChart(smap, "MediaWiki", title="Eval Constructs in MediaWiki, Scaled by SLOC", label="fig:EvalMWScaled", markExtra=mwMarkExtra));

	smap = getSummaries({"phpMyAdmin"});
	writeFile(|file:///tmp/maVar.tex|, varFeaturesChart(smap, "phpMyAdmin", title="Variable Features in phpMyAdmin", label="fig:VFMA", markExtra=maMarkExtra));
	writeFile(|file:///tmp/maVarScaled.tex|, varFeaturesScaledChart(smap, "phpMyAdmin", title="Variable Features in phpMyAdmin, Scaled by SLOC", label="fig:VFMAScaled", markExtra=maMarkExtra));
	writeFile(|file:///tmp/maMagic.tex|, magicMethodsChart(smap, "phpMyAdmin", title="Magic Methods in phpMyAdmin", label="fig:MMMA", markExtra=maMarkExtra));
	writeFile(|file:///tmp/maMagicScaled.tex|, magicMethodsScaledChart(smap, "phpMyAdmin", title="Magic Methods in phpMyAdmin, Scaled by SLOC", label="fig:MMMAScaled", markExtra=maMarkExtra));
	writeFile(|file:///tmp/maEval.tex|, evalsChart(smap, "phpMyAdmin", title="Eval Constructs in phpMyAdmin", label="fig:EvalMA", markExtra=maMarkExtra));
	writeFile(|file:///tmp/maEvalScaled.tex|, evalsScaledChart(smap, "phpMyAdmin", title="Eval Constructs inphpMyAdmin, Scaled by SLOC", label="fig:EvalMAScaled", markExtra=maMarkExtra));
}

private loc clocBinaryLoc = |file:///opt/homebrew/bin/cloc|;
private loc slocLoc = baseLoc + "serialized/sloc";

public void computeCorpusCLOC() {	
	for (p <- repositories<0>, v <- getTags(repositories[p])) {
		switchToTag(repositories[p], v);
		logMessage("Computing SLOC for <p> version <v>", 1);
		clocRes = phpLinesOfCode(repositories[p], clocBinaryLoc);
		writeBinaryValueFile(slocLoc + "<p>-<v>-sloc.bin", clocRes, compression=false);
	}
}

alias ClocRel = rel[str product, str version, ClocResult clocResult];

@doc{
	Check to see if there are any cases where cloc failed to run properly.
}
public ClocRel checkForBadClocResults() {
	ClocRel result = { };

	for (p <- repositories<0>, v <- getTags(repositories[p])) {
		clocRes = readBinaryValueFile(#ClocResult, slocLoc + "<p>-<v>-sloc.bin");
		if (clocRes is noResult) {
			result = result + < p, v, clocRes >;
		}
	}

	return result;
}

@doc{
	Load saved cloc results from disk.
}
public ClocRel loadClocResults() {
	ClocRel result = { };

	for (p <- repositories<0>, v <- getTags(repositories[p])) {
		clocRes = readBinaryValueFile(#ClocResult, slocLoc + "<p>-<v>-sloc.bin");
		if (clocRes is clocResult) {
			result = result + < p, v, clocRes >;
		}
	}

	return result;
}

public ClocRel restrictClocResultsToCorpus(ClocRel clocRel, rel[str product,str version] tags) {
	return { < p, v, r > | < p, v, r > <- clocRel, <p, v > in tags };
}

public map[str,ClocResult] summarizeClocResultsByProduct(ClocRel clocRel = { }) {
	map[str,ClocResult] result = ( );

	if (size(clocRel) == 0) {
		clocRel = loadClocResults();
	}

	for (p <- clocRel<0>) {
		ClocResult pResult = clocResult(0,0,0,0);
		for (< v, pvResult > <- clocRel[p]) {
			pResult.files = pResult.files + pvResult.files;
			pResult.blankLines = pResult.blankLines + pvResult.blankLines;
			pResult.commentLines = pResult.commentLines + pvResult.commentLines;
			pResult.sourceLines = pResult.sourceLines + pvResult.sourceLines;
		}
		result[p] = pResult;
	}

	return result;
}

public ClocResult summarizeClocResults(ClocRel clocRel = { }) {
	ClocResult result = clocResult(0,0,0,0);

	if (size(clocRel) == 0) {
		clocRel = loadClocResults();
	}

	for (p <- clocRel<0>, < v, pvResult > <- clocRel[p]) {
		result.files = result.files + pvResult.files;
		result.blankLines = result.blankLines + pvResult.blankLines;
		result.commentLines = result.commentLines + pvResult.commentLines;
		result.sourceLines = result.sourceLines + pvResult.sourceLines;
	}

	return result;
}

public rel[str product, str version, datetime commitDate] getTagDates(rel[str product, str version] corpus) {
	rel[str product, str version, datetime commitDate] result = { };
	for (<p,v> <- corpus) {
		result = result + < p, v, getTagCommitInfo(repositories[p], v) >;
	}
	return result;
}
