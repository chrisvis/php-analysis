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
	//traces = { <readTextValueString(#loc,a), b > | < a, b > <- readCSV(#rel[str,str], tracesCsv) };
	return { <a, readTextValueString(#loc,b), parseCallable(c) > | <a,b,c> <- readCSV(#rel[str function,str location,str argument], tracesCsv) };
}

public map[loc, node] findOccurences() {
	ast = loadPHPFile(|file:///ufs/chrism/php/thesis/examples/call_user_func.php|);
	
	calls = [c | /c:call(name(name(n)),_) := ast, /^call_user_func/ := n];

	map[loc, node] occurences = ();
	occurences += (c@at:c | c <- calls);
	
	return occurences;
}

//private
private Stmt transformCallUserFuncCall(Stmt input) {
	
	
}

public void main() {
	//iprint(findOccurences());
	
	traces = importTraces();
	iprintln(traces);
	iprintln(size(traces));
	iprintln("#eval: <size(traces["eval"])>");
	iprintln("#call_user_func: <size(traces["call_user_func"])>");
	iprintln("#call_user_func_array: <size(traces["call_user_func_array"])>");
	
	ast = loadPHPFile(|file:///ufs/chrism/php/thesis/examples/test.php|);
	
	//ast = loadPHPFile(|file:///ufs/chrism/php/thesis/examples/test_output.php|);
	//
	//iprintln(ast);
	//return;
	
	//iprintln(ast);
	//return;
	
	newAst = visit (ast) {
		case occurrence:exprstmt(call(name(name("call_user_func")), args)): {
			occTraces = traces["call_user_func"][occurrence@at];
			if (all(callable c <- occTraces, callableStr(_) := c)) {
			 	println("All callableStr");
			 	iprintln(occTraces);

				//Expr replacement;
				//iprintln();
				//Expr variable = top(args);
				iprintln(top(args));
				if (actualParameter(variable,_) := top(args)) {
					
					println("JWZ!!!");		
					if (callableStr(v) <- occTraces) {
		 		 		replacement = 
				 		 	\if(
							  binaryOperation(
							    variable,
							    scalar(string(v)),
							    equal()),
							
							  [
							    exprstmt(call(name(name(v)),[]))
							  ],
							  [],
							  noElse()
							);
					 	
					 	insert replacement;
				 	}
				 	iprintln(replacement);
				}
			} else if (all(callable c <- occTraces, callableArray(callableClass(_), callableStr(_)) := c)) {
				println("All callableClass-\>callableStr");
				iprintln(occTraces);
			} else if (all(callable c <- occTraces, callableArray(callableStr(_), callableStr(_)) := c)) {
				println("All callableStr::callableStr");
				iprintln(occTraces);
			}
			
			// //<- traces["call_user_func"][occurrence@at]) {
			//	iprintln(trace);
			//}
			//iprintln(args);
			
		}
	}
	
	iprintln (newAst);
	return;
	//buildBinaries("ZendFramework", "2.0", |file:///ufs/chrism/php/zf2/|);
	//ast = loadBinary("ZendFramework", "2.0");
	//iprint(pt);
	//buildBinaries("Drupal", "7.14");

	ast = loadBinary("ZendFramework", "2.0");
	//writeFile(|file:///ufs/chrism/data/output1.txt|, ast);
	//return;
	//callsAt = [c | c <- calls,  c@at == |file:///ufs/gast698/php/PHPAnalysis/corpus-icse13/CodeIgniter/codeigniter_2.1.2/system/core/CodeIgniter.php|(0,0,<359,0>,<359,0>)]; 
	//["at"] == |file:///ufs/gast698/php/PHPAnalysis/corpus-icse13/CodeIgniter/codeigniter_2.1.2/system/core/CodeIgniter.php| ) := calls];
	
	println("----------------");
	
	 
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
