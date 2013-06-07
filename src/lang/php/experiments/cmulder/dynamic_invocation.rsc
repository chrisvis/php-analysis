module lang::php::experiments::cmulder::dynamic_invocation

import lang::php::ast::AbstractSyntax;
import lang::php::util::Utils;
import lang::php::pp::PrettyPrinter;
import lang::php::ast::NormalizeAST;
import Node;

import IO;
import ValueIO;
import lang::csv::IO;
import util::Math;
import Type;
import Set;
import List;

data callable =  callableOther()
	| callableStr(str id) 
	| callableClass(str name)
	| callableArray( callable class,	callable method);

alias possibilityList = list[tuple[Expr cond, list[Stmt] body]];

private callable parseCallable(str arg) {
	switch(arg){
		case /^'<id:\w+>'$/ : 
			return callableStr(id);
		case /^array \(0 =\> '<class:\w+>', 1 =\> '<method:\w+>'\)$/: 
			return callableArray( callableStr(class),	callableStr(method));
		case /^array \(0 =\> class <class:\w+> \{\s*\}, 1 =\> '<method:\w+>'\)$/:
			return callableArray( callableClass(class),	callableStr(method));
	}
	return callableOther();
}


private rel[str function,loc location,callable argument] importTraces() {
	loc tracesCsv = |file:///export/scratch1/chrism/testTraces.csv|;
	return { <a, readTextValueString(#loc,b), parseCallable(c) > | <a,b,c> <- readCSV(#rel[str function,str location,str argument], tracesCsv) };
}

private tuple[Expr objectVar, Expr methodVar, bool inlineArray] checkForInlineArray(Expr callableArgument) {
	Expr objectVar;
	Expr methodVar;
	bool inlineArray;
					
	if (array([arrayElement(_,obj,_),arrayElement(_,met,_),xs*]) := callableArgument) {
		objectVar = obj;
		methodVar = met; 
		inlineArray = true; 
		
		println("inlineArray");
		iprintln(callableArgument);
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
		
		println("no inlineArray");
		iprintln(callableArgument);
	}
	
	return <objectVar, methodVar, inlineArray>;
}

private Stmt createIfFromPossibilities(possibilityList possibilities, Stmt occurrence) {
	possibilities = dup(possibilities);
				 	
 	list[ElseIf] elseStatements;

 	if (size(possibilities) > 1) {
 		elseStatements =  [elseIf(possibility.cond, possibility.body) | possibility <- tail(possibilities)];
 	} else {
 		elseStatements = [];
 	}
 	
	return \if(
				top(possibilities).cond,
				top(possibilities).body,
			    elseStatements,
			  	someElse(\else([occurrence]))
			);
}

public void main() {
	
	allTraces = importTraces();

	ast = loadPHPFile(|file:///ufs/chrism/php/thesis/examples/test.php|);

	newAst = visit (ast) {
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
					    	equal());
						
						Stmt body = visit (occurrence) {
							case call(name(name("call_user_func")), args): {
								insert call(name(name(traceValue)), tail(args));
							}
						};
						
						possibilities = possibilities + <condition, [body]>;
				 	}
				 	
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
						
						Expr cond;
				        if (callableArgumentProps.inlineArray) {
				        	// method == "traceValue"
				        	cond = 
			        			binaryOperation(
				    				callableArgumentProps.methodVar,
					    			scalar(string(traceValue)),
					    			equal()
					    		);
				        } else {
							// is_array($callableArgument) && sizeof($callableArgument) > 1 && $callableArgument[1] == "traceValue"
			         		cond =  
								binaryOperation(
							        binaryOperation(
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
						            	),
							          	booleanAnd()
						          	),
							        binaryOperation(
					    				callableArgumentProps.methodVar,
						    			scalar(string(traceValue)),
						    			equal()
						    		),
							        booleanAnd()
						        );
				        }
        						
						// objectVar->traceValue()
						Stmt body = visit (occurrence) {
							case call(name(name("call_user_func")), args): {
								insert methodCall(
  										callableArgumentProps.objectVar,
        								name(name(traceValue)),
										tail(args));
							}
						};
						
						possibilities = possibilities + <cond, [body]>;
				 	}

				 	insert createIfFromPossibilities(possibilities, occurrence);
				}
			// if all traces are array(classString, methodString) / classString::methodString()
			} else if (all(callable c <- tracesForOccurrence, callableArray(callableStr(_), callableStr(_)) := c)) {
				println("All callableStr::callableStr");
				iprintln(tracesForOccurrence);
			}
			
		}
	}

	println (newAst);
	writeFile(|file:///export/scratch1/chrism/testOutput.php|, "\<?\n" + pp(normalizeIf(newAst)));
	return;

}
