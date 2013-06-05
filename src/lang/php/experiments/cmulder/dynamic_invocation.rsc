module lang::php::experiments::cmulder::dynamic_invocation

import lang::php::ast::AbstractSyntax;
import lang::php::util::Utils;
import Node;

import IO;
import ValueIO;
import lang::csv::IO;
import util::Math;
import Type;
import Set;
import List;

//data callable = callableStr(str id) 
//	| callableArray(	callableStr(str id), 		callableStr(str id)) 
//	| callableArray(	callableClass(str name), 	callableStr(str id));
data callable =  callableOther()
	| callableStr(str id) 
	| callableClass(str name)
	| callableArray( callable class,	callable method);


public callable parseCallable(str arg) {
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


public rel[str function,loc location,callable argument] importTraces() {
	loc tracesCsv = |file:///export/scratch1/chrism/testTraces.csv|;
	return { <a, readTextValueString(#loc,b), parseCallable(c) > | <a,b,c> <- readCSV(#rel[str function,str location,str argument], tracesCsv) };
}

public void main() {
	
	allTraces = importTraces();

	println("#eval: <size(allTraces["eval"])>");
	println("#call_user_func: <size(allTraces["call_user_func"])>");
	println("#call_user_func_array: <size(allTraces["call_user_func_array"])>");
	
	ast = loadPHPFile(|file:///ufs/chrism/php/thesis/examples/test.php|);

	newAst = visit (ast) {
		case occurrence:exprstmt(/call(name(name("call_user_func")), args)): {
			
			tracesForOccurrence = allTraces["call_user_func"][occurrence@at];

			if (all(callable c <- tracesForOccurrence, callableStr(_) := c)) {
			 	println("All callableStr");

			 	iprintln(tracesForOccurrence);

				if (actualParameter(callableArgument,_) := top(args)) {
					
					list[tuple[Expr cond, list[Stmt] body]] possibilities = [];
					
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
				 	
					insert \if(
								top(possibilities).cond,
								top(possibilities).body,
							    [elseIf(possibility.cond, possibility.body) | possibility <- tail(possibilities)],
							  	someElse(\else([occurrence]))
							);
				}

				
			} else if (all(callable c <- tracesForOccurrence, callableArray(callableClass(_), callableStr(_)) := c)) {
				println("All callableClass-\>callableStr");
				iprintln(tracesForOccurrence);
				
				if (actualParameter(callableArgument,_) := top(args)) {
					
					list[tuple[Expr cond, list[Stmt] body]] possibilities = [];
					
					for (callableArray(callableClass(_), callableStr(traceValue)) <- tracesForOccurrence) {
						
						// is_array($callableArgument) && sizeof($callableArgument) > 1 && $callableArgument[1] == "traceValue"
						Expr condition =  
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
				    				fetchArrayDim(
										callableArgument,
										someExpr(scalar(integer(1)))
									),
					    			scalar(string(traceValue)),
					    			equal()
					    		),
						        booleanAnd()
					        );
        						
						// $callableArgument[0]->traceValue()
						Stmt body = visit (occurrence) {
							case call(name(name("call_user_func")), args): {
								insert methodCall(
  										fetchArrayDim(
          									callableArgument,
          									someExpr(scalar(integer(0)))
      									),
        								name(name(traceValue)),
										tail(args));
							}
						};
						
						possibilities = possibilities + <condition, [body]>;
				 	}
				 	
					insert \if(
								top(possibilities).cond,
								top(possibilities).body,
							    [elseIf(possibility.cond, possibility.body) | possibility <- tail(possibilities)],
							  	someElse(\else([occurrence]))
							);
				}
								
			} else if (all(callable c <- tracesForOccurrence, callableArray(callableStr(_), callableStr(_)) := c)) {
				println("All callableStr::callableStr");
				iprintln(tracesForOccurrence);
			}
			
			// //<- traces["call_user_func"][occurrence@at]) {
			//	iprintln(trace);
			//}
			//iprintln(args);
			
		}
	}

	iprintln (newAst);
	return;

	
	 
	calls = [c | /c:call(name(name("call_user_func")), _) := ast ];
	arguments = [argument | /c:call(name(name("call_user_func")), argument) := ast ];
	
	
	for (args <- arguments) {
		//iprintln(args[0]);
		loc position = args[0]@at;
		loc file = |file:///tmp|[uri=position.uri];
				
		switch(args[0]) {
			case actualParameter(scalar(_),_): {
				println("call_user_func with static string parameter:");
				//iprintln(args[0]);
			}
			case actualParameter(array([arrayElement(_, scalar(_),_),arrayElement(_, scalar(_),_)]),_): {
				println("call_user_func with static array parameter:");
				//iprintln(args[0]);
			}
			
			case actualParameter(fetchConst(_),_): {
				println("call_user_func with static const parameter:");
				//iprintln(args[0]);
			}
			case actualParameter(var(name(name(S))),_): {
				println("call_user_func with plain variable $<S>:");
				println(position);

				//println(readFile(position));
				//iprintln(position);
				//iprintln(file);
				//iprintln(ast[file]);
				assignments = [a | /a:assign(var(name(name(S))),_) := ast[file]];
				
				iprintln(assignments);
				//iprintln(args[0]);
			}
			default:
				
				println("dynamic usage"); 				
		}
		
		iprintln(traces[position]);
		println("=========================================");
		//iprintln(args[0]);
	}
	
	//writeFile(|file:///ufs/chrism/data/output1.txt|, arguments);
	//writeFile(|file:///ufs/chrism/data/output2.txt|, calls);
	println(size(arguments));
	println(size(calls));
	return;
	println("----------------");
	
	// call_user_func with static string parameter
	
	calls = [c | /c:call(name(name("call_user_func")), [actualParameter(scalar(_),_)]) := ast ];
	iprint(calls);
	
	println("----------------");
	
	// call_user_func with static array parameter
	calls = [c | /c:call(name(name("call_user_func")), [actualParameter(array([arrayElement(_, scalar(_),_),arrayElement(_, scalar(_),_)]),_)]) := ast ];
	iprint(calls);


}
