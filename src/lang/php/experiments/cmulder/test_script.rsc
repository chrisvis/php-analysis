module lang::php::experiments::cmulder::test_script

import lang::php::ast::AbstractSyntax;
import lang::php::util::Utils;
import Node;
import IO;
import Type;

//import lang::php::analysis::includes::PropagateStringVars;
//import lang::php::analysis::evaluators::ScalarEval;

//import lang::php::analysis::NamePaths;
//import lang::php::analysis::cfg::CFG;
//import lang::php::analysis::cfg::Label;
//import lang::php::analysis::cfg::FlowEdge;
//import lang::php::analysis::cfg::BuildCFG;

alias System = map[loc fileloc, Script scr];
 
//map[node,node] cfgmap;

public void main() {
	//loc file = |file:///ufs/chrism/php/thesis/examples/call_user_func.php|;
	loc file = |file:///ufs/chrism/php/thesis/examples/simple_assign.php|;
	Script scr = loadPHPFile(file);
	
	//cfgmap = buildCFGs(scr);
	//
	//iprintln(typeOf(cfgmap));
	//iprintln(cfgmap);
	scr = delAnnotationsRec(scr);
	iprintln(scr);

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
	//iprintln(ast);
	//iprint(ast);
	map[loc,node] scripts = (|file:///ufs/chrism/php/thesis/examples/call_user_func.php|:ast);
	solve (scripts) {
		scripts = evalAllScalarsAndInlineUniques(scripts,|file:///ufs/chrism/php/thesis/examples/|);
		scripts = evalStringVars(scripts);
	}
	iprint(scripts);
	//iprint(evalStringVars(ast));

	assignments = [a | /a:assign(var(name(name(_))),_) := ast];
	iprintln(assignments);

	println(1);
	println(readFile(|file:///ufs/chrism/php/thesis/examples/call_user_func.php|(0,0,<2,0>,<2,0>)));
	println(2);
	println(readFile(|file:///ufs/chrism/php/thesis/examples/call_user_func.php|(7,63,<2,0>,<2,0>)));
*/
}

