module lang::php::experiments::cmulder::test_script

import lang::php::ast::AbstractSyntax;
import lang::php::util::Utils;
import Node;
import IO;
import Type;
import List;
//import lang::php::analysis::includes::PropagateStringVars;
//import lang::php::analysis::evaluators::ScalarEval;

//import lang::php::analysis::NamePaths;
//import lang::php::analysis::cfg::CFG;
//import lang::php::analysis::cfg::Label;
//import lang::php::analysis::cfg::FlowEdge;
//import lang::php::analysis::cfg::BuildCFG;

alias System = map[loc fileloc, Script scr];
 
//map[node,node] cfgmap;

public bool isScalarArray(arr) {
	for (/param:"arrayElement"(_,valArrEl,_) := arr) {
		if (scalar(_) !:= valArrEl) {
			return false;
		}
	}
	return true;		
}

public void main() {
	//loc file = |file:///ufs/chrism/php/thesis/examples/call_user_func.php|;
	//loc file = |file:///ufs/chrism/php/thesis/examples/simple.php|;
	loc file = |file:///ufs/chrism/php/thesis/examples/test_output.php|;
	Script scr = loadPHPFile(file);
	scr = delAnnotationsRec(scr);
		
	iprintln(scr);
	return;
	
	//cfgmap = buildCFGs(scr);
	//
	//iprintln(typeOf(cfgmap));
	//iprintln(cfgmap);
	
	//iprintln(scr);
//
	//sys = loadBinary("CodeIgniter", "2.1.2");
	//sys = loadBinary("PEAR", "1.9.4");
	//iprintln(sys);
	
	// find call_user_func in foreach loop
	
	for (n:"foreach"(arr,_,_,val,[M*,/c:"call"("name"("name"("call_user_func")),[/args:val,N*]),O*]):= scr) {
		println("foreach statement");
	
		iprintln(n);
		println("=============");
		iprintln(val);
		println("scalar array? <isScalarArray(arr)>");
		iprintln(c);

	}
	
	
	return;
	
	
	visit (scr) {
		case n:call(name(name("func")),_) : {
			iprintln(n);
			
			firstArgument = [ arg | /actualParameter(node arg, _) := n ][0];
			iprintln(firstArgument);
			if (var(name(name(str varName))) := firstArgument) {
				println("yep: <varName>"); 
				
				visit (scr) {
					case m:assign(var(name(name(varName))), assValue) : {
						println("Assigned: <assValue>");	
					}
					case m:assignWOp(var(name(name(varName))), assValue, operator) : {
						println("<operator> with: <assValue>");	
					}
				}
				
			} else {
				println("nope.");
			}
		}
	}

	/*

	map[loc,node] scripts = (|file:///ufs/chrism/php/thesis/examples/call_user_func.php|:ast);
	solve (scripts) {
		scripts = evalAllScalarsAndInlineUniques(scripts,|file:///ufs/chrism/php/thesis/examples/|);
		scripts = evalStringVars(scripts);
	}

	//iprint(evalStringVars(ast));

	assignments = [a | /a:assign(var(name(name(_))),_) := ast];
*/
}

