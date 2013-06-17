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
alias traceRel = rel[str function,loc location,callable argument];

set[str] changedFiles = {};

private callable parseCallable(str arg) {
	switch(arg){
		case /^'<id:\w+>'$/ : 
			return callableStr(id);
		case /^'<expr:.*>'$/ : 
			return callableExprStr(expr);
		case /^array \(0 =\> '<class:\w+>', 1 =\> '<method:\w+>'\)$/: 
			return callableArray( callableStr(class),	callableStr(method));
		case /^array \(0 =\> class <class:\w+> \{\s*\}, 1 =\> '<method:\w+>'\)$/:
			return callableArray( callableClass(class),	callableStr(method));
		
	}
	return callableOther();
}


private void generateTestOuput(Script scr, loc outputFile) {
	writeFile(outputFile, "\<?php\n<pp(flattenBlocks(scr))>");
}

private void generateTestOuput(System sys, loc outputFile) {
	str output = "\<?php\n";
	for(file <- sys) {
		output = output + "// <file>\n\n";
		output = output + "<pp(flattenBlocks(sys[file]))> \n// EOF <file>\n\n";
	}
	writeFile(outputFile, output);
}

private void generateOutput(System sys, loc outputPath, loc systemPath) {
	for(changedFile <- changedFiles) {
		//
		loc inputFile = |file:///| + changedFile;
		loc outputFile = |file:///| + replaceFirst(changedFile, systemPath.path, outputPath.path);
		
		println(inputFile);
		println(outputFile);

		writeFile(outputFile, "\<?php\n<pp(flattenBlocks(sys[inputFile]))>");
	}	
}

private Script parsePHPString(str code) {
	loc tmpFile = |file:///tmp/phpString.php|;
	writeFile(tmpFile, "\<?php\n<code>");
	return loadPHPFile(tmpFile);
}

private rel[str function,loc location,callable argument] importTraces(loc l) {
	return { <a, readTextValueString(#loc,b), parseCallable(c) > | <a,b,c> <- readCSV(#rel[str function,str location,str argument], l) };
}

private tuple[Expr objectVar, Expr methodVar, bool inlineArray] checkForInlineArray(Expr callableArgument) {
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

private Stmt createIfFromPossibilities(possibilityList possibilities, Stmt occurrence) {
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

private System replaceEvalsByTraces(System sys, traceRel allTraces) {
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

public Expr combineBoolExprs([Expr singleExpr]) {
	return singleExpr;
}

public Expr combineBoolExprs(list[Expr] exprs) {
	return 
		binaryOperation(
			top(exprs),
			combineBoolExprs(tail(exprs)),
			booleanAnd()
		);
}

private System replaceCallUserFunByTraces(System sys, traceRel allTraces) {
	sys = visit (sys) {
		case occurrence:exprstmt(/call(name(name("call_user_func")), args)): {
			
			tracesForOccurrence = allTraces["call_user_func"][occurrence@at];

			// if all traces are plain strings
			if (all(callable c <- tracesForOccurrence, callableStr(_) := c)) {
			 	println("All callableStr");
			 	iprintln(tracesForOccurrence);

				if (actualParameter(callableArgument,_) := top(args)) {
					
					possibilityList possibilities = [];
					for (callableStr(traceValue) <- tracesForOccurrence) {
					
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
				 	changedFiles += occurrence@at.path;
				 	insert createIfFromPossibilities(possibilities, occurrence);
				}
			// if all traces are array(object, methodString) / $object->methodString()				
			} else if (all(callable c <- tracesForOccurrence, callableArray(callableClass(_), callableStr(_)) := c)) {
				println("All callableClass-\>callableStr");
				iprintln(tracesForOccurrence);
				
				if (actualParameter(callableArgument,_) := top(args)) {
					
					callableArgumentProps = checkForInlineArray(callableArgument);
					possibilityList possibilities = [];
					
					for (callableArray(callableClass(_), callableStr(traceValue)) <- tracesForOccurrence) {
						
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
					changedFiles += occurrence@at.path;
				 	insert createIfFromPossibilities(possibilities, occurrence);
				}
			// if all traces are array(classString, methodString) / classString::methodString()
			} else if (all(callable c <- tracesForOccurrence, callableArray(callableStr(_), callableStr(_)) := c)) {
				println("All callableStr::callableStr");
				iprintln(tracesForOccurrence);
				
				if (actualParameter(callableArgument,_) := top(args)) {
					
					callableArgumentProps = checkForInlineArray(callableArgument);
					possibilityList possibilities = [];
					
					for (callableArray(callableStr(traceValueClass), callableStr(traceValueMethod)) <- tracesForOccurrence) {
						
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
					changedFiles += occurrence@at.path;
				 	insert createIfFromPossibilities(possibilities, occurrence);	
			 	}			
			}
			
		}
	}
	return sys;
}

public void main() {
	//loc systemPath = |file:///ufs/chrism/php/thesis/examples/testSystem|;
	//loc tracesCsv = |file:///export/scratch1/chrism/testTraces.csv|;
	loc systemPath = |file:///export/scratch1/chrism/systems/wordpress-tests/|;
	loc tracesCsv = |file:///export/scratch1/chrism/systems/wordpress-tests.csv|;
	loc build = |file:///export/scratch1/chrism/systems/wordpress-tests.pt|;
	loc buildAltered = |file:///export/scratch1/chrism/systems/wordpress-tests.pt.altered|;

	//sys = loadPHPFiles(systemPath);
	//writeBinaryValueFile(build, sys);
	sys = readBinaryValueFile(#System, build);
	////
	//////sys = resolveIncludesWithVars(sys, systemPath);
	sys = replaceStaticEvalUsage(sys);
	sys = replaceStaticCallUserFuncUsage(sys);
	//
	traceRel allTraces = importTraces(tracesCsv);
	iprintln(domain(allTraces["call_user_func"]));
	sys = replaceEvalsByTraces(sys, allTraces);
	sys = replaceCallUserFunByTraces(sys, allTraces);
	
	print("changedFiles");
	iprintln(changedFiles);
	////	
	//writeBinaryValueFile(buildAltered, sys);
	//sys = readBinaryValueFile(#System, buildAltered);
	//generateTestOuput(sys, |file:///ufs/chrism/php/thesis/examples/testSystem.php|);
	generateOutput(sys, |file:///tmp/output/|, systemPath);

	return;
}
