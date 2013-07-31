module lang::php::experiments::cmulder::dynamic_invocation

import lang::php::util::System;
import lang::php::ast::AbstractSyntax;
import lang::php::util::Utils;
import lang::php::pp::PrettyPrinter;
import lang::php::ast::NormalizeAST;
import Node;
import lang::php::analysis::includes::ResolveIncludes;

import IO;
import ValueIO;
import lang::csv::IO;
import util::Math;
import Type;
import Set;
import String;
import List;
import Relation;

data callable =  callableOther()
	| callableStr(str id)
	| callableExprStr(str expr) 
	| callableClass(str name)
	| callableArray( callable class,	callable method);

alias possibilityList = list[tuple[Expr cond, list[Stmt] body]];
alias traceRel = rel[str function, loc location, tuple[callable argument, int arrElements] arguments];

set[str] changedFiles = {};

public callable parseCallable(str arg) {
	switch(arg){
		case /^'<id:\w+>'$/ : 
			return callableStr(id);
		case /^'<expr:.*>'$/ : 
			return callableExprStr(expr);
		case /^array \(0 =\> '<class:\w+>', 1 =\> '<method:.+>'\)$/: 
			return callableArray( callableStr(class),	callableStr(method));
		case /^array \(0 =\> class <class:\w+> \{.*\}, 1 =\> '<method:.+>'\)$/:
			return callableArray( callableClass(class),	callableStr(method));
		
	}
	println("Unparsable trace: <arg>");
	return callableOther();
}

public int countArrayElements(str string) {	
	// remove new lines
	string = replaceAll(string, "\n", "");
	
	// remove escaped '
	string = replaceAll(string, "\\\'", "");

	// remove surrounding array
	if (/^array \(<body:.*>\)$/ := string) {
		string = body;
	}
	
	// cleanup string (remove nested arrays/classes/strings)
	// to eliminate false positives of array elements
	solve(string) {
		// remove strings
		for (/<block:'[^']*\'>/ := string) {
			string = replaceAll(string, block, "");
		}

		// remove () sets with content (nested arrays)
		for (/<block:\([^\(\)]*\)>/ := string) {
			string = replaceAll(string, block, "");
		}

		// remove {} sets with content (objects)
		for (/<block:\{[^\{\}]*\}>/ := string) {
			string = replaceAll(string, block, "");
		}
	}
	
	return size(findAll(string, "=\>"));
}

public void generateTestOuput(Script scr, loc outputFile) {
	writeFile(outputFile, "\<?php\n<pp(flattenBlocks(scr))>");
}

public void generateTestOuput(System sys, loc outputFile) {
	str output = "\<?php\n";
	for(file <- sys) {
		output = output + "// <file>\n\n";
		output = output + "<pp(flattenBlocks(sys[file]))> \n// EOF <file>\n\n";
	}
	writeFile(outputFile, output);
}

public void generateOutput(System sys, loc outputPath, loc systemPath) {
	for(changedFile <- changedFiles) {
		loc inputFile = |file:///| + changedFile;
		loc outputFile = |file:///| + replaceFirst(changedFile, systemPath.path, outputPath.path);
		
		println("Changed file: <outputFile>");

		writeFile(outputFile, "\<?php\n<pp(flattenBlocks(sys[inputFile]))>");
	}	
}

public Script parsePHPString(str code) {
	loc tmpFile = |file:///tmp/phpString.php|;
	writeFile(tmpFile, "\<?php\n<code>");
	return loadPHPFile(tmpFile);
}

public traceRel importTraces(loc l) {
	return { <a, readTextValueString(#loc,b), <parseCallable(c), countArrayElements(d)> > | <a,b,c,d> <- readCSV(#rel[str function,str location,str argument, str argument2], l) };
}

public tuple[Expr objectVar, Expr methodVar, bool inlineArray] checkForInlineArray(Expr callableArgument) {
	Expr objectVar;
	Expr methodVar;
	bool inlineArray;
					
	if (array([arrayElement(_,obj,_),arrayElement(_,met,_),xs*]) := callableArgument) {
		objectVar = obj;
		methodVar = met; 
		inlineArray = true; 
	} else {
		objectVar = 
			fetchArrayDim(
				callableArgument,
				someExpr(scalar(integer(0)))
			);
			
		methodVar = 
			fetchArrayDim(
				callableArgument,
				someExpr(scalar(integer(1)))
			);
		inlineArray = false;
	}
	
	return <objectVar, methodVar, inlineArray>;
}

public Stmt createIfFromPossibilities(possibilityList possibilities, Stmt occurrence) {
 	list[ElseIf] elseStatements;

	possibilities = dup(possibilities);

 	if (size(possibilities) > 1) {
 		elseStatements =  [elseIf(possibility.cond, possibility.body) | possibility <- tail(possibilities)];
 	} else {
 		elseStatements = [];
 	}

	return 
		\if(
			top(possibilities).cond,
			top(possibilities).body,
		    elseStatements,
		  	someElse(\else([occurrence]))
		);
}

public System replaceStaticEvalUsage(System sys) {
	sys = replaceVisit:visit (sys) {
		case occurrence:exprstmt(/eval(scalar(string(code)))): {
			if (script(stmts) := parsePHPString(code)) {
				changedFiles += occurrence@at.path;
				insert block(stmts);
			}
		}
	}
	return sys;
}

public System replaceStaticCallUserFuncUsage(System sys) {
	sys = replaceVisit:visit (sys) {

		case match:exprstmt(/call(name(name("call_user_func")), [actualParameter(scalar(string(functionName)),_), xs*])): {
			println(functionName);
			replacement = visit(match) {
				case call(name(name("call_user_func")), args): { 
					insert call(name(name(functionName)), tail(args));
				}
			}
			changedFiles += match@at.path;
			insert replacement;
		}
		case match:exprstmt(/call(name(name("call_user_func")), [actualParameter(array([arrayElement(_, scalar(string(className)),_),arrayElement(_, scalar(string(methodName)),_),xs*]),_), ys*])): {
			println("<className>::<methodName>");

			if (contains(methodName, "::")) {
				fail replaceVisit;
			}

			replacement = visit(match) {
				case call(name(name("call_user_func")), args): { 
					insert staticCall(name(name(className)), name(name(methodName)), tail(args));
				}
			}
			changedFiles += match@at.path;
			insert replacement;
		}
			
	}

	return sys;
}

public System replaceEvalsByTraces(System sys, traceRel allTraces) {
	sys = replaceVisit:visit (sys) {
		case occurrence:exprstmt(/eval(callableArgument)): {
			tracesForOccurrence = allTraces["eval"][occurrence@at];
			
			if (isEmpty(tracesForOccurrence)) {
				fail replaceVisit;
			}
			
			possibilityList possibilities = [];
			for(callableExprStr(traceValue) <- tracesForOccurrence){
				Expr condition = binaryOperation(
		    		callableArgument,
			    	scalar(string(traceValue)),
			    	equal()
		    	);

		    	if (script(body) := parsePHPString(traceValue)) {
		    		//FIXME: no support for return value of eval()
		    		possibilities = possibilities + <condition, body>;
		    	}
		 	}
			
			if (isEmpty(possibilities)) {
				fail replaceVisit;
			}
			changedFiles += occurrence@at.path;
		 	insert createIfFromPossibilities(possibilities, occurrence);
		}
	}

	return sys;
}

public Expr combineBoolExprs([Expr singleExpr]) = singleExpr;
public Expr combineBoolExprs(list[Expr] exprs) =
	binaryOperation(
		top(exprs),
		combineBoolExprs(tail(exprs)),
		booleanAnd()
	);


public System replaceCallUserFunByTraces(System sys, traceRel allTraces) {
	notFoundTraceLocs = domain(allTraces["call_user_func"]);
	set[loc] locs = {};
	visit (sys) {
		case occ:call(name(name("call_user_func")), _): {
			locs += occ@at;
		}
	}
	
	notFoundLocs = locs;
	println("CUF in project: <size(locs)>");
	int cufMatched = 0;
	int cufTrace = 0;
	
	sys = replaceVisit:visit (sys) {
		case occurrence:Stmt s: {
			if ("at" notin getAnnotations(s) || s@at notin locs) {
				fail replaceVisit;
			}
			args = [];
			if (/call(name(name("call_user_func")), _args) := occurrence) {
				args = _args;
			}
			
			cufMatched = cufMatched + 1;
			
			tracesForOccurrence = allTraces["call_user_func"][occurrence@at];
			//println(occurrence@at);
			
			notFoundTraceLocs -= occurrence@at;
			// No traces for this occurrence, fail visit
			if (isEmpty(tracesForOccurrence)) {
				fail replaceVisit;
			}
			
			cufTrace = cufTrace + 1;
			notFoundLocs -= occurrence@at;
			possibilityList possibilities = [];

			for (trace <- tracesForOccurrence) {
				if (callableStr(traceValue) := trace.argument) {
					if (actualParameter(callableArgument,_) := top(args)) {
						Expr condition = binaryOperation(
				    		callableArgument,
					    	scalar(string(traceValue)),
					    	equal()
				    	);
						
						Stmt body = visit (occurrence) {
							case call(name(name("call_user_func")), args): {
								insert call(name(name(traceValue)), tail(args));
							}
						};
							
						possibilities = possibilities + <condition, [body]>;
				 	}
				} else if (callableArray(callableClass(_), callableStr(traceValue)) := trace.argument) {
				
					if (actualParameter(callableArgument,_) := top(args)) {
					
						callableArgumentProps = checkForInlineArray(callableArgument);
						list[Expr] conds = [];

				        if (!callableArgumentProps.inlineArray) {
							//  is_array($callableArgument) && sizeof($callableArgument) > 1
			         		conds = conds + [   
				          		call(
          							name(name("is_array")),
          							[actualParameter(callableArgument, false)]
      							),
								binaryOperation(
					            	call(
										name(name("sizeof")),
					            		[actualParameter(callableArgument, false)]),
					            	scalar(integer(1)),
					            	gt()
				            	)
				    		];
				        }
				        
				        // is_object(callableArgumentProps.objectVar) && callableArgumentProps.methodVar == "traceValue"
				        conds = conds + [
				        	call(
								name(name("is_object")),
      							[actualParameter(callableArgumentProps.objectVar, false)]
  							),
		        			binaryOperation(
			    				callableArgumentProps.methodVar,
				    			scalar(string(traceValue)),
				    			equal()
			    			)
		    			];
				        	
        						
						// objectVar->traceValue()
						Stmt body = visit (occurrence) {
							case call(name(name("call_user_func")), args): {
								insert methodCall(
									callableArgumentProps.objectVar,
    								name(name(traceValue)),
									tail(args)
								);
							}
						};
						
						possibilities = possibilities + <combineBoolExprs(conds), [body]>;
				 	}
				}  else if (callableArray(callableStr(traceValueClass), callableStr(traceValueMethod)) := trace.argument) {
				
					if (actualParameter(callableArgument,_) := top(args)) {
					
						callableArgumentProps = checkForInlineArray(callableArgument);

						list[Expr] conds = [];
				        
				        if (!callableArgumentProps.inlineArray){
							// is_array($callableArgument) && sizeof($callableArgument) > 2 
			         		conds = conds + [ 
			          			call(
          							name(name("is_array")),
          							[actualParameter(callableArgument, false)]
      							),
								binaryOperation(
					            	call(
										name(name("sizeof")),
					            		[actualParameter(callableArgument, false)]),
					            	scalar(integer(1)),
					            	gt()
				            	)
				    		];
				        }
				        // callableArgumentProps.objectVar == "traceValueClass" && callableArgumentProps.methodVar == "traceValueMethod"
			        	conds = conds + [ 
		        			binaryOperation(
			    				callableArgumentProps.objectVar,
				    			scalar(string(traceValueClass)),
				    			equal()
				    		), 
				    		binaryOperation(
			    				callableArgumentProps.methodVar,
				    			scalar(string(traceValueMethod)),
				    			equal()
				    		)
					    ];
			        
						// objectVar::traceValue()
						Stmt body = visit (occurrence) {
							case call(name(name("call_user_func")), args): {
								insert staticCall(
									name(name(traceValueClass)),
    								name(name(traceValueMethod)),
									tail(args)
								);
							}
						};
						
						possibilities = possibilities + <combineBoolExprs(conds), [body]>;
				 	}
			 	} else {
			 		//println("Unknown trace");
		 			iprintln(trace);
			 	}
			}
			if (possibilities == []) {
				//println("No possibilities for occurence, should not happen.");
				iprintln(occurrence);
			} else {
				changedFiles += occurrence@at.path;
				//println("Changed:");
				//println(pp(occurrence));
				result = createIfFromPossibilities(possibilities, occurrence);
				//println("Into:");
				//println(pp(result));
				insert result;
			}		
		}
	}
	println("cufMatched: <cufMatched>");
	println("cufTrace: <cufTrace>");
	//println("Not found:");
	ppLocs(notFoundLocs);
	return sys;
}

public void ppLocs(set[loc] locs) {
	for(l <- locs) {
		println("<l.path>:<l.begin.line>");
	}
}

public tuple[list[ActualParameter] params, list[Expr] conds] unrollCUFAArguments(actualParameter(arrArgument,_), int numElements) {
	list [Expr] conds = [];
	list[ActualParameter] params = [];
	
	if (array(arrElements) := arrArgument) {
		println("array(arrElements) := arrArgument");
		params = [actualParameter(n, false) | arrayElement(_,n,_) <- arrElements];
	} else {
	 	conds = conds + [
	 		call(
				name(name("is_array")),
				[actualParameter(arrArgument, false)]
			),
			binaryOperation(
            	call(
					name(name("sizeof")),
            		[actualParameter(arrArgument, false)]),
            	scalar(integer(numElements)),
            	equal()
        	)
	 	];
	 	for(int n <- [0 .. numElements]) {
	 		params = params + [
	 			actualParameter(
					fetchArrayDim(
						arrArgument,
						someExpr(scalar(integer(n)))
					),
					false
				)
			];
	 	}
 	}
 	return <params, conds>;
}

public tuple[list[ActualParameter] params, list[Expr] conds] unrollCUFAArguments(a) = <[],[]>;

public System replaceCUFAByTraces(System sys, traceRel allTraces) {


	
	notFoundTraceLocs = domain(allTraces["call_user_func_array"]);

	str output = "";
	
	set[loc] locs = {};
	visit (sys) {
		case occ:call(name(name("call_user_func_array")), _): {
			locs += occ@at;
			output =  output  + "<occ@at.path>:<occ@at.begin.line>\n"; 
		}
	}

	set[loc] notFoundLocs = locs;
	
	println("CUFA in project: <size(locs)>");
	int cufaMatched = 0;
	int cufaTrace = 0;
	
	sys = replaceVisit:visit (sys) {
		case occurrence:Stmt s: {
			if ("at" notin getAnnotations(s) || s@at notin locs) {
				fail replaceVisit;
			}
			args = [];
			if (/call(name(name("call_user_func_array")), _args) := occurrence) {
				args = _args;
			}
			tracesForOccurrence = allTraces["call_user_func_array"][occurrence@at];
			//println(occurrence@at);
			
			cufaMatched = cufaMatched + 1;
			
			
			notFoundTraceLocs -= occurrence@at;
			// No traces for this occurrence, fail visit
			if (isEmpty(tracesForOccurrence)) {
				fail replaceVisit;
			}
			
			notFoundLocs -= s@at;
			cufaTrace = cufaTrace + 1;
			
			possibilityList possibilities = [];

			for (trace <- tracesForOccurrence) {
				if (callableStr(traceValue) := trace.argument) {
					if (actualParameter(callableArgument,_) := top(args)) {
						list[Expr] conds = [
							binaryOperation(
					    		callableArgument,
						    	scalar(string(traceValue)),
						    	equal()
					    	)
						];
						
						tuple[list[ActualParameter] params, list[Expr] conds] unrollData = unrollCUFAArguments(top(tail(args)), trace.arrElements);
						conds = conds + unrollData.conds;
						
						Stmt body = visit (occurrence) {
							case call(name(name("call_user_func_array")), args): {
								insert call(name(name(traceValue)), unrollData.params);
							}
						};
							
						possibilities = possibilities + <combineBoolExprs(conds), [body]>;
				 	}
				} else if (callableArray(callableClass(_), callableStr(traceValue)) := trace.argument) {
				
					if (actualParameter(callableArgument,_) := top(args)) {
					
						callableArgumentProps = checkForInlineArray(callableArgument);
						list[Expr] conds = [];

				        if (!callableArgumentProps.inlineArray) {
							//  is_array($callableArgument) && sizeof($callableArgument) > 1
			         		conds = conds + [   
				          		call(
          							name(name("is_array")),
          							[actualParameter(callableArgument, false)]
      							),
								binaryOperation(
					            	call(
										name(name("sizeof")),
					            		[actualParameter(callableArgument, false)]),
					            	scalar(integer(1)),
					            	gt()
				            	)
				    		];
				        }
				        
				        // is_object(callableArgumentProps.objectVar) && callableArgumentProps.methodVar == "traceValue"
				        conds = conds + [
				        	call(
								name(name("is_object")),
      							[actualParameter(callableArgumentProps.objectVar, false)]
  							),
		        			binaryOperation(
			    				callableArgumentProps.methodVar,
				    			scalar(string(traceValue)),
				    			equal()
			    			)
		    			];
				        	
						tuple[list[ActualParameter] params, list[Expr] conds] unrollData = unrollCUFAArguments(top(tail(args)), trace.arrElements);
						conds = conds + unrollData.conds;
        						
						// objectVar->traceValue()
						Stmt body = visit (occurrence) {
							case call(name(name("call_user_func_array")), args): {
								insert methodCall(
									callableArgumentProps.objectVar,
    								name(name(traceValue)),
									unrollData.params
								);
							}
						};
						
						possibilities = possibilities + <combineBoolExprs(conds), [body]>;
				 	}
				}  else if (callableArray(callableStr(traceValueClass), callableStr(traceValueMethod)) := trace.argument) {
				
					if (actualParameter(callableArgument,_) := top(args)) {
					
						callableArgumentProps = checkForInlineArray(callableArgument);

						list[Expr] conds = [];
				        
				        if (!callableArgumentProps.inlineArray){
							// is_array($callableArgument) && sizeof($callableArgument) > 2 
			         		conds = conds + [ 
			          			call(
          							name(name("is_array")),
          							[actualParameter(callableArgument, false)]
      							),
								binaryOperation(
					            	call(
										name(name("sizeof")),
					            		[actualParameter(callableArgument, false)]),
					            	scalar(integer(1)),
					            	gt()
				            	)
				    		];
				        }
				        // callableArgumentProps.objectVar == "traceValueClass" && callableArgumentProps.methodVar == "traceValueMethod"
			        	conds = conds + [ 
		        			binaryOperation(
			    				callableArgumentProps.objectVar,
				    			scalar(string(traceValueClass)),
				    			equal()
				    		), 
				    		binaryOperation(
			    				callableArgumentProps.methodVar,
				    			scalar(string(traceValueMethod)),
				    			equal()
				    		)
					    ];
					    
						tuple[list[ActualParameter] params, list[Expr] conds] unrollData = unrollCUFAArguments(top(tail(args)), trace.arrElements);
						conds = conds + unrollData.conds;
			        
						// objectVar::traceValue()
						Stmt body = visit (occurrence) {
							case call(name(name("call_user_func_array")), args): {
								insert staticCall(
									name(name(traceValueClass)),
    								name(name(traceValueMethod)),
									unrollData.params
								);
							}
						};
						
						possibilities = possibilities + <combineBoolExprs(conds), [body]>;
				 	}
			 	} else {
			 		//println("Unknown trace");
		 			//iprintln(trace);
		 			1;
			 	}
			}
			if (possibilities == []) {
				//println("No possibilities for occurence, should not happen.");
				//iprintln(occurrence);
				1;
			} else {
				changedFiles += occurrence@at.path;
				//println("Changed:");
				//println(pp(occurrence));
				result = createIfFromPossibilities(possibilities, occurrence);
				//println("Into:");
				//println(pp(result));
				insert result;
			}		
		}
	}
	
	//println("Not found trace locs:");
	//iprintln(notFoundTraceLocs);
	//println("Not found CUFA");
	ppLocs(notFoundLocs);
	
	println("cufaMatched: <cufaMatched>");
	println("cufaTrace: <cufaTrace>");
	
	return sys;
}

public void main() {
	generateTable();
	return;
	
	loc systemPath = |file:///ufs/chrism/php/htdocs/wordpress_1/|;
	loc tracesCsv = |file:///ufs/chrism/php/htdocs/wordpress_1.csv|;
	
	loc build = |file:///export/scratch1/chrism/systems/wordpress_1.pt|;
	
	//sys = loadPHPFiles(systemPath, addLocationAnnotations=true, addLocationAnnotations=true);
	//writeBinaryValueFile(build, sys);
	sys = readBinaryValueFile(#System, build);

	//sys = resolveIncludesWithVars(sys, systemPath);
	//sys = replaceStaticEvalUsage(sys);
	//sys = replaceStaticCallUserFuncUsage(sys);

	traceRel allTraces = importTraces(tracesCsv);
	sys = replaceEvalsByTraces(sys, allTraces);
	sys = replaceCallUserFunByTraces(sys, allTraces);
	sys = replaceCUFAByTraces(sys, allTraces);
	
	println(numDiffParams(allTraces, "call_user_func"));
	println(numDiffParams(allTraces, "call_user_func_array"));
	//generateOutput(sys, |file:///tmp/output/|, systemPath);

	return;
}

public void generateTable() {
//alias traceRel = rel[str function, loc location, tuple[callable argument, int arrElements] arguments];

	list[traceRel] traces = [
		importTraces(|file:///ufs/chrism/php/htdocs/wordpress.csv|),
		importTraces(|file:///ufs/chrism/php/htdocs/wordpress_1.csv|),
		importTraces(|file:///ufs/chrism/php/htdocs/wordpress_2.csv|),
		importTraces(|file:///ufs/chrism/php/htdocs/wordpress_3.csv|),
		importTraces(|file:///ufs/chrism/php/htdocs/wordpress_4.csv|)
	];
	
	map[str, map[str,tuple[int,int,int,int,int]]] counts = ();
	
	
	for (func <- ["call_user_func", "call_user_func_array"]) {
		counts[func] = ();
		for(int n <- [0 .. 5]) {
			println(func);
			for(<loc l, <callable c,int i>> <- traces[n][func]) {
				path = l.path;
				path = replaceAll(path, "/ufs/chrism/php/htdocs/wordpress/", "");
				path = replaceAll(path, "/ufs/chrism/php/htdocs/wordpress_1/", "");
				path = replaceAll(path, "/ufs/chrism/php/htdocs/wordpress_2/", "");
				path = replaceAll(path, "/ufs/chrism/php/htdocs/wordpress_3/", "");
				path = replaceAll(path, "/ufs/chrism/php/htdocs/wordpress_4/", "");
				path = "<path>:<l.begin.line>";
				//println(l);
				if (path notin counts[func]) { 
					counts[func][path] = <0,0,0,0,0>;
				}
				counts[func][path][n] = size(traces[n][func][l]);
			}
		}
	}
	
	iprint(counts);
	
	
}

public str numDiffParams (traceRel allTraces, funcName) {
	str output = "\\begin{table}[!th]\n\\begin{tabular}{lr}\n\\hline\n\tLocation & \\# different arguments \\\\\n\\hline\n";

	tuple[int, loc] sizeX(tuple[loc, tuple[callable, int]] t) {
		return <size(allTraces[funcName][t[0]]), t[0]>;
	}

	results = mapper(allTraces[funcName], sizeX);

	for(n <- reverse(sort(domain(results)))) {
		for(item <- results[n]) {
			path = replaceAll(item.path, "/ufs/chrism/php/htdocs/wordpress_1/", "");
			output += "\t<path> (line: <item.begin.line>) & <n> \\\\\n";
		
			if (n == 1) {
				println(item);
				iprintln(allTraces[funcName][item]);
			}
		}
	}

	output += "\\hline\n\\end{tabular}\n\\caption{Varaity of arguments}\n\\label{stats:varaity}\n\\end{table}\n";
	return output;
	
}