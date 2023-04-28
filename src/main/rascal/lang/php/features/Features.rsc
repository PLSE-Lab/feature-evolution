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
import DateTime;
import Map;
import util::Math;

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

private lrel[num,num] computeCoords(lrel[num,num] inputs) {
	return [ < idx, j > | <idx, j> <- inputs ];
}

str computeXTicks(list[int] tickIndex) {
	displayThese = [ idx | idx <- tickIndex ];
	return "xtick={<intercalate(",",displayThese)>}";
}

str cleanUpLabel(str l) {
	if (startsWith(l, "release-")) {
		return substring(l, size("release-"));
	} else if (startsWith(l, "v")) {
		return substring(l, size("v"));
	}
	return l;
}

str computeTickLabels(list[str] vlist, list[int] tickIndex) {
	displayThese = [ cleanUpLabel(vlist[idx]) | idx <- tickIndex ];
	return "xticklabels={<intercalate(",",displayThese)>}";
}

private str makeCoords(lrel[num,num] inputs, str mark="", list[str] markExtra=[ ], str legend="", str label="", bool dashed=false) {
	list[str] extrasList = markExtra;
	if (size(mark) > 0) {
		extrasList = "mark=<mark>" + extrasList;
	}
	if (dashed) {
		extrasList = extrasList + "dashed";
	}
	str extras = intercalate(",",extrasList);

	return "\\addplot+<if(size(extras)>0){>[<extras>]<}> coordinates {
		   '<intercalate(" ",[ "(<i>,<j>)" | < i,j > <- computeCoords(inputs)])>
		   '};<if(size(legend)>0){>
		   '\\addlegendentry{<legend>}\n<}><if(size(label)>0){>
		   '\\label{<label>}\n<}>";
}

public map[str, VarFeatureCounts] getVarFeatureCountsMap(str s, set[str] vs) {
	map[str, VarFeatureCounts] counts = ( );
	for (v <- vs) {
		vsum = readSummary(s,v);
		counts[v] = getVarFeatureCounts(vsum.varFeatures);
	}
	return counts;
} 

public map[str, MagicMethodCounts] getMagicMethodCountsMap(str s, set[str] vs) {
	map[str, MagicMethodCounts] counts = ( );
	for (v <- vs) {
		msum = readSummary(s,v);
		counts[v] = getMagicMethodCounts(msum.magicMethods);
	}
	return counts;
} 

public map[str, EvalLikeCounts] getEvalCountsMap(str s, set[str] vs) {
	map[str, EvalLikeCounts] counts = ( );
	for (v <- vs) {
		esum = readSummary(s,v);
		counts[v] = getEvalLikeCounts(esum.evalLikes);
	}
	return counts;
}

public map[str, InvocationCounts] getInvocationCountsMap(str s, set[str] vs) {
	map[str, InvocationCounts] counts = ( );
	for (v <- vs) {
		isum = readSummary(s,v);
		counts[v] = getInvocationCounts(isum.invocations);
	}
	return counts;
} 

public list[int] computeTickIndexesByDate(list[str] sortedTags, rel[str,datetime] dates, int monthsApart=3) {
	list[int] tickIndex = [0];
	for (i <- index(sortedTags)) {
		tagDate = getOneFrom(dates[sortedTags[i]]);
		priorDate = getOneFrom(dates[sortedTags[tickIndex[-1]]]);
		if ( (tagDate.year == priorDate.year && tagDate.month >= (priorDate.month+monthsApart)) || tagDate.year > priorDate.year) {
			tickIndex = tickIndex + i;
		}
	}
	if (tickIndex[-1] != size(sortedTags)-1) {
		tickIndex = tickIndex + (size(sortedTags)-1);
	}
	return tickIndex;
}

public list[int] computeTickIndexesByRange(list[str] sortedTags, int total=40) {
	list[int] tickIndex = [0];
	int intervalSize = size(sortedTags) / total;
	for (i <- index(sortedTags), i % intervalSize == 0) {
		tickIndex = tickIndex + i;
	}
	if (tickIndex[-1] != size(sortedTags)-1) {
		tickIndex = tickIndex + (size(sortedTags)-1);
	}
	return tickIndex;
}

public list[str] getTagsByDate(rel[str product, str version] corpus, rel[str product, str version, datetime commitDate] tagDates, str s) {
	// Get all the tags/versions for this system s
	tags = corpus[s];

	// Load the dates for the tags
	dates = tagDates[s];

	bool sortTagsByDate(str t1, str t2) {
		d1 = getOneFrom(dates[t1]);
		d2 = getOneFrom(dates[t2]);
		return d1 < d2;
	}

	sortedTags = sort(toList(tags), sortTagsByDate);
	return sortedTags;
}

public void exportVarFeatureChart(str s, map[str,VarFeatureCounts] counts, loc saveTo, 
	str systemName, list[str] markExtra=["mark phase=1","mark repeat=10","mark size=1pt"],
	bool sortByDate = false) {
	// Get all the tags/versions for this system s
	corpus = loadTags();
	tags = corpus[s];

	// Load the dates for the tags
	allDates = getTagDates(corpus);
	dates = allDates[s];

	// Sort the tags either by date or by version. Sorting by date tends to
	// lead to odd graphs since there may be multiple major releases being
	// updated at the same time, but they may have very different feature
	// profiles. So, be warned...
	sortedTags = sortByDate ? getTagsByDate(corpus, allDates, s) : sortTags(tags);

	list[int] tickIndex = [ ];
	if (sortByDate) {
		// Find points at 6 month intervals
		tickIndex = computeTickIndexesByDate(sortedTags, dates, monthsApart=6);
	} else {
		// Divide the tags into an even number of spaces
		tickIndex = computeTickIndexesByRange(sortedTags, total=40);
	}

	// Get back the lists of counts, needed for coordinates
	vv = [ < i, counts[sortedTags[i]].varVar > | i <- index(sortedTags) ];
	vfc = [ < i, counts[sortedTags[i]].varFCall > | i <- index(sortedTags) ];
	vmc = [ < i, counts[sortedTags[i]].varMCall > | i <- index(sortedTags) ];
	vn = [ < i, counts[sortedTags[i]].varNew > | i <- index(sortedTags) ];
	vp = [ < i, counts[sortedTags[i]].varProp > | i <- index(sortedTags) ];
	vcc = [ < i, counts[sortedTags[i]].varClassConst > | i <- index(sortedTags) ];
	vsc = [ < i, counts[sortedTags[i]].varStaticCall > | i <- index(sortedTags) ];
	vst = [ < i, counts[sortedTags[i]].varStaticTarget > | i <- index(sortedTags) ];
	vspn = [ < i, counts[sortedTags[i]].varStaticPropertyName > | i <- index(sortedTags) ];
	vspt = [ < i, counts[sortedTags[i]].varStaticPropertyTarget > | i <- index(sortedTags) ];

	// Configure the blocks of coordinates that will be plotted
	list[str] coordinateBlocks = [ ];
	if (max(vv<1>) > 5)
		coordinateBlocks += makeCoords(vv, mark="square", markExtra=markExtra, legend="V");
	if (max(vfc<1>) > 5)
		coordinateBlocks += makeCoords(vfc, mark="x", markExtra=markExtra, legend="FC");
	if (max(vmc<1>) > 5)
		coordinateBlocks += makeCoords(vmc, mark="o", markExtra=markExtra, legend="MC");
	if (max(vn<1>) > 5)
		coordinateBlocks += makeCoords(vn, mark="+", markExtra=markExtra, legend="OC");
	if (max(vp<1>) > 5)
		coordinateBlocks += makeCoords(vp, mark="*", markExtra=markExtra, legend="P");
	if (max(vcc<1>) > 5)
		coordinateBlocks += makeCoords(vcc, mark="triangle", markExtra=markExtra, legend="CC");
	if (max(vsc<1>) > 5)
		coordinateBlocks += makeCoords(vsc, mark="pentagon", markExtra=markExtra, legend="SC");
	if (max(vst<1>) > 5)
		coordinateBlocks += makeCoords(vst, mark="diamond", markExtra=markExtra, legend="SCT");
	if (max(vspn<1>) > 5)
		coordinateBlocks += makeCoords(vspn, mark="otimes", markExtra=markExtra, legend="SP");
	if (max(vspt<1>) > 5)
		coordinateBlocks += makeCoords(vspt, mark="oplus", markExtra=markExtra, legend="SPT");

	// Compute the maximum y coordinate
	int maxY = max(vv<1>+vfc<1>+vmc<1>+vn<1>+vp<1>+vcc<1>+vsc<1>+vst<1>+vspn<1>+vspt<1>)+10;

	str res = "\\begin{tikzpicture}
			  '\\begin{axis}[width=\\textwidth,height=.25\\textheight,try min ticks={5},xlabel=<systemName> Version,ylabel=Feature Count,xmin=1,ymin=0,xmax=<tickIndex[-1]>,ymax=<maxY>,legend style={font=\\tiny,at={(0,1)},anchor=north west},xmajorgrids,x tick label style={rotate=90,anchor=east,font=\\tiny},<computeXTicks(tickIndex)>,<computeTickLabels(sortedTags,tickIndex)>]
			  '<for (cb <- coordinateBlocks) {> <cb> <}>
			  '\\end{axis}
			  '\\end{tikzpicture}
			  ";

	writeFileLines(saveTo, [res]);
}

public void exportMagicMethodsChart(str s, map[str,MagicMethodCounts] counts, loc saveTo, 
	str systemName, list[str] markExtra=["mark phase=1","mark repeat=10","mark size=1pt"],
	bool sortByDate = false) {
	// Get all the tags/versions for this system s
	corpus = loadTags();
	tags = corpus[s];

	// Load the dates for the tags
	allDates = getTagDates(corpus);
	dates = allDates[s];

	// Sort the tags either by date or by version. Sorting by date tends to
	// lead to odd graphs since there may be multiple major releases being
	// updated at the same time, but they may have very different feature
	// profiles. So, be warned...
	sortedTags = sortByDate ? getTagsByDate(corpus, allDates, s) : sortTags(tags);

	list[int] tickIndex = [ ];
	if (sortByDate) {
		// Find points at 6 month intervals
		tickIndex = computeTickIndexesByDate(sortedTags, dates, monthsApart=6);
	} else {
		// Divide the tags into an even number of spaces
		tickIndex = computeTickIndexesByRange(sortedTags, total=40);
	}

	// Get back the lists of counts, needed for coordinates
	mset = [ < i, counts[sortedTags[i]].sets > | i <- index(sortedTags) ];
	mget = [ < i, counts[sortedTags[i]].gets > | i <- index(sortedTags) ];
	mis = [ < i, counts[sortedTags[i]].isSets > | i <- index(sortedTags) ];
	mun = [ < i, counts[sortedTags[i]].unsets > | i <- index(sortedTags) ];
	mc = [ < i, counts[sortedTags[i]].calls > | i <- index(sortedTags) ];
	msc = [ < i, counts[sortedTags[i]].staticCalls > | i <- index(sortedTags) ];

	// Configure the blocks of coordinates that will be plotted
	list[str] coordinateBlocks = [ ];
	if (max(mset<1>) > 0)
		coordinateBlocks += makeCoords(mset, mark="square", markExtra=markExtra, legend="S");
	if (max(mget<1>) > 0)
		coordinateBlocks += makeCoords(mget, mark="x", markExtra=markExtra, legend="G");
	if (max(mis<1>) > 0)
		coordinateBlocks += makeCoords(mis, mark="o", markExtra=markExtra, legend="I");
	if (max(mun<1>) > 0)
		coordinateBlocks += makeCoords(mun, mark="otimes", markExtra=markExtra, legend="U");
	if (max(mc<1>) > 0)
		coordinateBlocks += makeCoords(mc, mark="*", markExtra=markExtra, legend="C");
	if (max(msc<1>) > 0)
		coordinateBlocks += makeCoords(msc, mark="triangle", markExtra=markExtra, legend="SC");

	// Compute the maximum y coordinate
	int maxY = max(mset<1> + mget<1> + mis<1> + mun<1> + mc<1> + msc<1>)+10;

	str res = "\\begin{tikzpicture}
			  '\\begin{axis}[width=\\textwidth,height=.25\\textheight,try min ticks={5},xlabel=<systemName> Version,ylabel=Feature Count,xmin=1,ymin=0,xmax=<tickIndex[-1]>,ymax=<maxY>,legend style={font=\\tiny,at={(0,1)},anchor=north west},xmajorgrids,x tick label style={rotate=90,anchor=east,font=\\tiny},<computeXTicks(tickIndex)>,<computeTickLabels(sortedTags,tickIndex)>]
			  '<for (cb <- coordinateBlocks) {> <cb> <}>
			  '\\end{axis}
			  '\\end{tikzpicture}
			  ";

	writeFileLines(saveTo, [res]);
}

public void exportEvalsInvocationsChart(str s, map[str,EvalLikeCounts] evals, 
	map[str,InvocationCounts] invocations, loc saveTo, 
	str systemName, list[str] markExtra=["mark phase=1","mark repeat=10","mark size=1pt"],
	bool sortByDate = false) {
	// Get all the tags/versions for this system s
	corpus = loadTags();
	tags = corpus[s];

	// Load the dates for the tags
	allDates = getTagDates(corpus);
	dates = allDates[s];

	// Sort the tags either by date or by version. Sorting by date tends to
	// lead to odd graphs since there may be multiple major releases being
	// updated at the same time, but they may have very different feature
	// profiles. So, be warned...
	sortedTags = sortByDate ? getTagsByDate(corpus, allDates, s) : sortTags(tags);

	list[int] tickIndex = [ ];
	if (sortByDate) {
		// Find points at 6 month intervals
		tickIndex = computeTickIndexesByDate(sortedTags, dates, monthsApart=6);
	} else {
		// Divide the tags into an even number of spaces
		tickIndex = computeTickIndexesByRange(sortedTags, total=40);
	}

	// Get back the lists of counts, needed for coordinates
	evalc = [ < i, evals[sortedTags[i]].evalCount > | i <- index(sortedTags) ];
	cfunc = [ < i, evals[sortedTags[i]].createFunctionCount > | i <- index(sortedTags) ];
	calluf = [ < i, invocations[sortedTags[i]].callUserFuncCount > | i <- index(sortedTags) ];
	callufa = [ < i, invocations[sortedTags[i]].callUserFuncArrayCount > | i <- index(sortedTags) ];
	callum = [ < i, invocations[sortedTags[i]].callUserMethodCount > | i <- index(sortedTags) ];
	calluma = [ < i, invocations[sortedTags[i]].callUserMethodArrayCount > | i <- index(sortedTags) ];
	fwdsc = [ < i, invocations[sortedTags[i]].forwardStaticCallCount > | i <- index(sortedTags) ];
	fwdsca = [ < i, invocations[sortedTags[i]].forwardStaticCallArrayCount > | i <- index(sortedTags) ];

	// Configure the blocks of coordinates that will be plotted
	list[str] coordinateBlocks = [ ];
	if (max(evalc<1>) > 0)
		coordinateBlocks += makeCoords(evalc, mark="square", markExtra=markExtra, legend="E");
	if (max(cfunc<1>) > 0)
		coordinateBlocks += makeCoords(cfunc, mark="x", markExtra=markExtra, legend="CF");
	if (max(calluf<1>) > 0)
		coordinateBlocks += makeCoords(calluf, mark="o", markExtra=markExtra, legend="UF");
	if (max(callufa<1>) > 0)
		coordinateBlocks += makeCoords(callufa, mark="otimes", markExtra=markExtra, legend="UFA");
	if (max(callum<1>) > 0)
		coordinateBlocks += makeCoords(callum, mark="*", markExtra=markExtra, legend="UM");
	if (max(calluma<1>) > 0)
		coordinateBlocks += makeCoords(calluma, mark="triangle", markExtra=markExtra, legend="UMA");
	if (max(fwdsc<1>) > 0)
		coordinateBlocks += makeCoords(fwdsc, mark="pentagon", markExtra=markExtra, legend="SC");
	if (max(fwdsca<1>) > 0)
		coordinateBlocks += makeCoords(fwdsca, mark="diamond", markExtra=markExtra, legend="SCA");

	// Compute the maximum y coordinate
	int maxY = max(evalc<1> + cfunc<1> + calluf<1> + callufa<1> + callum<1> + calluma<1> + fwdsc<1> + fwdsca<1>)+10;

	str res = "\\begin{tikzpicture}
			  '\\begin{axis}[width=\\textwidth,height=.25\\textheight,try min ticks={5},xlabel=<systemName> Version,ylabel=Feature Count,xmin=1,ymin=0,xmax=<tickIndex[-1]>,ymax=<maxY>,legend style={font=\\tiny,at={(0,1)},anchor=north west},xmajorgrids,x tick label style={rotate=90,anchor=east,font=\\tiny},<computeXTicks(tickIndex)>,<computeTickLabels(sortedTags,tickIndex)>]
			  '<for (cb <- coordinateBlocks) {> <cb> <}>
			  '\\end{axis}
			  '\\end{tikzpicture}
			  ";

	writeFileLines(saveTo, [res]);
}

public rel[str product, str version, loc path, int featureCount] fillCountsRel(rel[str product, str version] corpus) {
	rel[str product, str version, loc path, int featureCount] fileCounts = { };
	for (p <- corpus<0>, v <- corpus[p]) {
		fsum = readSummary(p,v);

		map[loc,int] countsPerFile = ( );

		// Get file paths and counts of var features
		for ( <l,i> <- fsum.varFeatures.features ) {
			if (l.top in countsPerFile) {
				countsPerFile[l.top] = countsPerFile[l.top] + 1;
			} else {
				countsPerFile[l.top] = 1;
			}
		}	

		// and magic methods...
		for ( <l,i> <- fsum.magicMethods.methods ) {
			if (l.top in countsPerFile) {
				countsPerFile[l.top] = countsPerFile[l.top] + 1;
			} else {
				countsPerFile[l.top] = 1;
			}
		}	

		// and invocations...
		for ( <l,i> <- fsum.invocations.invocations ) {
			if (l.top in countsPerFile) {
				countsPerFile[l.top] = countsPerFile[l.top] + 1;
			} else {
				countsPerFile[l.top] = 1;
			}
		}	

		// and eval-likes, but not closures... 
		for ( <l,i> <- fsum.evalLikes.evalLikes, !(i is closureItem) ) {
			if (l.top in countsPerFile) {
				countsPerFile[l.top] = countsPerFile[l.top] + 1;
			} else {
				countsPerFile[l.top] = 1;
			}
		}

		// and now add all this into the relation
		for (l <- countsPerFile) {
			fileCounts = fileCounts + < p, v, l, countsPerFile[l] >;
		}
	}

	return fileCounts;
}

public void exportFileInfoChart(rel[str product, str version] corpus, loc saveTo, 
	rel[str product, str version, loc path, int featureCount] crel = { },
	list[str] markExtra=["mark phase=1","mark repeat=10","mark size=1pt"]) {

	rel[str product, str version, loc path, int featureCount] featuresPerFileRel  = crel;
	if (size(crel) == 0) {
		featuresPerFileRel = fillCountsRel(corpus);
	}

	rel[str product, str version, int fileCount] fileCounts = { };
	for (p <- featuresPerFileRel<0>, v <- featuresPerFileRel[p]<0>) {
		int fileCount = size( (featuresPerFileRel[p,v])<0> );
		fileCounts = fileCounts + < p, v, fileCount >;
	}

	rel[str product, str version, real featureCount] featureCounts = { };
	for (p <- featuresPerFileRel<0>, v <- featuresPerFileRel[p]<0>) {
		list[int] featureCountList = sort([ n | <l,n> <- featuresPerFileRel[p,v] ]) ;
		listSize = size(featureCountList);
		real median = 0.0;
		if (listSize % 2 == 0) {
			median = (featureCountList[listSize/2] + featureCountList[listSize/2-1])/2.0;
		} else {
			median = featureCountList[listSize/2] * 1.0;
		}
		featureCounts = featureCounts + < p, v, floor(fitFloat(median) * 100) / 100.0 >;
	}

	map[str,list[str]] sortedTagMap = ( );
	for (p <- corpus<0>) {
		sortedTagMap[p] = sortTags(corpus[p]);
	}

	mostVersions = max([size(sortedTagMap[p]) | p <- sortedTagMap<0> ]);
	deltaForMD = (1.0*(mostVersions-1))/(size(sortedTagMap["moodle"])-1);
	deltaForMW = (1.0*(mostVersions-1))/(size(sortedTagMap["mediawiki"])-1);
	deltaForBB = (1.0*(mostVersions-1))/(size(sortedTagMap["phpBB"])-1);
	deltaForWP = (1.0*(mostVersions-1))/(size(sortedTagMap["wordpress"])-1);
	
	sortedTags = [ "<i>" | i <- [0..mostVersions]];
	tickIndex = computeTickIndexesByRange(sortedTags, total=40);

	featuresMD = [ < floor(fitFloat(i * deltaForMD)*100)/100.0, getOneFrom(featureCounts["moodle",v]) > | i <- index(sortedTagMap["moodle"]), v := sortedTagMap["moodle"][i] ];
	filesMD = [ < floor(fitFloat(i * deltaForMD)*100)/100.0, getOneFrom(fileCounts["moodle",v]) > | i <- index(sortedTagMap["moodle"]), v := sortedTagMap["moodle"][i] ];
	
	featuresMW = [ < floor(fitFloat(i * deltaForMW)*100)/100.0, getOneFrom(featureCounts["mediawiki",v]) > | i <- index(sortedTagMap["mediawiki"]), v := sortedTagMap["mediawiki"][i] ];
	filesMW = [ < floor(fitFloat(i * deltaForMW)*100)/100.0, getOneFrom(fileCounts["mediawiki",v]) > | i <- index(sortedTagMap["mediawiki"]), v := sortedTagMap["mediawiki"][i] ];

	featuresBB = [ < floor(fitFloat(i * deltaForBB)*100)/100.0, getOneFrom(featureCounts["phpBB",v]) > | i <- index(sortedTagMap["phpBB"]), v := sortedTagMap["phpBB"][i] ];
	filesBB = [ < floor(fitFloat(i * deltaForBB)*100)/100.0, getOneFrom(fileCounts["phpBB",v]) > | i <- index(sortedTagMap["phpBB"]), v := sortedTagMap["phpBB"][i] ];

	featuresWP = [ < floor(fitFloat(i * deltaForWP)*100)/100.0, getOneFrom(featureCounts["wordpress",v]) > | i <- index(sortedTagMap["wordpress"]), v := sortedTagMap["wordpress"][i] ];
	filesWP = [ < floor(fitFloat(i * deltaForWP)*100)/100.0, getOneFrom(fileCounts["wordpress",v]) > | i <- index(sortedTagMap["wordpress"]), v := sortedTagMap["wordpress"][i] ];

	list[str] coordinateBlocks1 = [ ];
	list[str] coordinateBlocks2 = [ ];
	coordinateBlocks1 += makeCoords(filesMD, mark="x", markExtra=markExtra, label="md_files", dashed=true);
	coordinateBlocks2 += makeCoords(featuresMD, mark="square", markExtra=markExtra, legend="MD Features");
	coordinateBlocks1 += makeCoords(filesMW, mark="otimes", markExtra=markExtra, label="mw_files", dashed=true);
	coordinateBlocks2 += makeCoords(featuresMW, mark="o", markExtra=markExtra, legend="MW Features");
	coordinateBlocks1 += makeCoords(filesBB, mark="triangle", markExtra=markExtra, label="bb_files", dashed=true);
	coordinateBlocks2 += makeCoords(featuresBB, mark="*", markExtra=markExtra, legend="BB Features");
	coordinateBlocks1 += makeCoords(filesWP, mark="diamond", markExtra=markExtra, label="wp_files", dashed=true);
	coordinateBlocks2 += makeCoords(featuresWP, mark="pentagon", markExtra=markExtra, legend="WP Features");

	// Compute the maximum y coordinate
	int maxY1 = max(filesMD<1> + filesMW<1> + filesBB<1> + filesWP<1>)+10;
	int maxY2 = round(max(featuresMD<1> + featuresMW<1> + featuresBB<1> + featuresWP<1>))+2;

	str res = "\\begin{tikzpicture}
			  '\\begin{axis}[axis y line*=right,width=\\textwidth,height=.25\\textheight,try min ticks={5},xlabel=Scaled Release History,ylabel=File Count,xmin=1,ymin=0,xmax=<tickIndex[-1]>,ymax=<maxY1>,xmajorgrids,x tick label style={font=\\tiny},<computeXTicks(tickIndex)>,<computeTickLabels(sortedTags,tickIndex)>]
			  '<for (cb <- coordinateBlocks1) {> <cb> <}>
			  '\\end{axis}
			  '\\begin{axis}[axis y line*=left,width=\\textwidth,height=.25\\textheight,try min ticks={5},ylabel=Median Features per File,xmin=1,ymin=0,xmax=<tickIndex[-1]>,ymax=<maxY2>,legend style={font=\\tiny,at={(0,1)},anchor=north west},axis x line=none,<computeXTicks(tickIndex)>,xticklabels={}]
			  '\\addlegendimage{/pgfplots/refstyle=md_files}\\addlegendentry{MD Files}
			  '\\addlegendimage{/pgfplots/refstyle=mw_files}\\addlegendentry{MW Files}
			  '\\addlegendimage{/pgfplots/refstyle=bb_files}\\addlegendentry{BB Files}
			  '\\addlegendimage{/pgfplots/refstyle=wp_files}\\addlegendentry{WP Files}
			  '<for (cb <- coordinateBlocks2) {> <cb> <}>
			  '\\end{axis}
			  '\\end{tikzpicture}
			  ";

	writeFileLines(saveTo, [res]);
}

@doc{
	Generate and save all charts showing the use of dynamic features 
	and the chart showing the median feature count/total file count.
}
public void makeCharts(loc exportLoc, 
	map[str, VarFeatureCounts] vcmapWP = ( ), 
	map[str, VarFeatureCounts] vcmapMD = ( ),
	map[str, VarFeatureCounts] vcmapMW = ( ), 
	map[str, VarFeatureCounts] vcmapBB = ( ),
	map[str, MagicMethodCounts] mmmapWP = ( ),
	map[str, MagicMethodCounts] mmmapMD = ( ),
	map[str, MagicMethodCounts] mmmapMW = ( ),
	map[str, MagicMethodCounts] mmmapBB = ( ),
	map[str, EvalLikeCounts] emapWP = ( ),
	map[str, EvalLikeCounts] emapMD = ( ),
	map[str, EvalLikeCounts] emapMW = ( ),
	map[str, EvalLikeCounts] emapBB = ( ),
	map[str, InvocationCounts] imapWP = ( ),
	map[str, InvocationCounts] imapMD = ( ),
	map[str, InvocationCounts] imapMW = ( ),
	map[str, InvocationCounts] imapBB = ( ),
	rel[str product, str version, loc path, int featureCount] crel = { }) {

	corpus = loadTags();

	if (size(vcmapWP) == 0)
		vcmapWP = getVarFeatureCountsMap("wordpress", corpus["wordpress"]);
	
	if (size(vcmapMD) == 0)
		vcmapMD = getVarFeatureCountsMap("moodle", corpus["moodle"]);
	
	if (size(vcmapMW) == 0)
		vcmapMW = getVarFeatureCountsMap("mediawiki", corpus["mediawiki"]);
	
	if (size(vcmapBB) == 0)
		vcmapBB = getVarFeatureCountsMap("phpBB", corpus["phpBB"]);

	if (size(mmmapWP) == 0)
		mmmapWP = getMagicMethodCountsMap("wordpress", corpus["wordpress"]);

	if (size(mmmapMD) == 0)
		mmmapMD = getMagicMethodCountsMap("moodle", corpus["moodle"]);

	if (size(mmmapMW) == 0)
		mmmapMW = getMagicMethodCountsMap("mediawiki", corpus["mediawiki"]);

	if (size(mmmapBB) == 0)
		mmmapBB = getMagicMethodCountsMap("phpBB", corpus["phpBB"]);

	if (size(emapWP) == 0)
		mmmapWP = getEvalCountsMap("wordpress", corpus["wordpress"]);

	if (size(emapMD) == 0)
		mmmapMD = getEvalCountsMap("moodle", corpus["moodle"]);

	if (size(emapMW) == 0)
		mmmapMW = getEvalCountsMap("mediawiki", corpus["mediawiki"]);

	if (size(emapBB) == 0)
		mmmapBB = getEvalCountsMap("phpBB", corpus["phpBB"]);

	if (size(imapWP) == 0)
		mmmapWP = getInvocationCountsMap("wordpress", corpus["wordpress"]);

	if (size(imapMD) == 0)
		mmmapMD = getInvocationCountsMap("moodle", corpus["moodle"]);

	if (size(imapMW) == 0)
		mmmapMW = getInvocationCountsMap("mediawiki", corpus["mediawiki"]);

	if (size(imapBB) == 0)
		mmmapBB = getInvocationCountsMap("phpBB", corpus["phpBB"]);

	if (size(crel) == 0)
		crel = fillCountsRel(corpus);

	exportVarFeatureChart("wordpress", vcmapWP, exportLoc + "wpVar.tex", "WordPress");
	exportVarFeatureChart("mediawiki", vcmapMW, exportLoc + "mwVar.tex", "MediaWiki");
	exportVarFeatureChart("moodle", vcmapMD, exportLoc + "mdVar.tex", "Moodle");
	exportVarFeatureChart("phpBB", vcmapBB, exportLoc + "bbVar.tex", "phpBB");

	exportMagicMethodsChart("wordpress", mmmapWP, exportLoc + "wpMagic.tex", "WordPress");
	exportMagicMethodsChart("mediawiki", mmmapMW, exportLoc + "mwMagic.tex", "MediaWiki");
	exportMagicMethodsChart("moodle", mmmapMD, exportLoc + "mdMagic.tex", "Moodle");
	exportMagicMethodsChart("phpBB", mmmapBB, exportLoc + "bbMagic.tex", "phpBB");
	
	exportEvalsInvocationsChart("wordpress", emapWP, imapWP, exportLoc + "wpEval.tex", "WordPress");
	exportEvalsInvocationsChart("mediawiki", emapMW, imapMW, exportLoc + "mwEval.tex", "MediaWiki");
	exportEvalsInvocationsChart("moodle", emapMD, imapMD, exportLoc + "mdEval.tex", "Moodle");
	exportEvalsInvocationsChart("phpBB", emapBB, imapBB, exportLoc + "bbEval.tex", "phpBB");

	exportFileInfoChart(corpus, exportLoc + "features-and-files.tex", crel=crel);
}

@doc{
	Location of the cloc binary.
	TODO: Adjust this if your cloc is in a different location.
}
private loc clocBinaryLoc = |file:///opt/homebrew/bin/cloc|;

@doc{
	Location of where to store extracted SLOC information.
}
private loc slocLoc = baseLoc + "serialized/sloc";

@doc{
	Compute SLOC for all systems in the corpus.
}
public void computeCorpusCLOC() {	
	for (p <- repositories<0>, v <- getTags(repositories[p])) {
		switchToTag(repositories[p], v);
		logMessage("Computing SLOC for <p> version <v>", 1);
		clocRes = phpLinesOfCode(repositories[p], clocBinaryLoc);
		writeBinaryValueFile(slocLoc + "<p>-<v>-sloc.bin", clocRes, compression=false);
	}
}

@doc{
	Type to represent SLOC for multiple systems and versions.
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

@doc{
	Restrict the computed results to a subset of products and versions.
}
public ClocRel restrictClocResultsToCorpus(ClocRel clocRel, rel[str product,str version] tags) {
	return { < p, v, r > | < p, v, r > <- clocRel, <p, v > in tags };
}

@doc{
	Create a ClocResult that includes the sums across all included versions of the same
	product in ClocRel. This will return one ClocResult for each product.
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

@doc{
	Create a ClocResult that includes the sums across all included versions of all
	products in ClocRel. This returns a single ClocResult that contains the sums.
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

@doc{
	Get the date of each commit for each product and release in corpus. This is
	done by checking the commit date in Git.
}
public rel[str product, str version, datetime commitDate] getTagDates(rel[str product, str version] corpus) {
	rel[str product, str version, datetime commitDate] result = { };
	for (<p,v> <- corpus) {
		result = result + < p, v, getTagCommitInfo(repositories[p], v) >;
	}
	return result;
}

public list[str] sortTags(set[str] tags) {
	return sort(toList(tags), compareVersion);
}
