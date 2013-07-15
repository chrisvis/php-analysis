module lang::php::experiments::cmulder::test_script

import lang::php::ast::AbstractSyntax;
import lang::php::util::Utils;
import lang::php::pp::PrettyPrinter;
import Node;
import IO;
import Type;
import List;
import String;
import ValueIO;
//import lang::php::analysis::includes::PropagateStringVars;
//import lang::php::analysis::evaluators::ScalarEval;

//import lang::php::analysis::NamePaths;
//import lang::php::analysis::cfg::CFG;
//import lang::php::analysis::cfg::Label;
//import lang::php::analysis::cfg::FlowEdge;
//import lang::php::analysis::cfg::BuildCFG;

layout MyLayout = [\t\n\ \r\f]*;
//lexical Identifier = [a-z] !<< [a-z]+ !>> [a-z] \ MyKeywords;
keyword MyKeywords = "array" | "class";
//syntax Expression
//	=	

anno node node @ parentNode;

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
	scriptje = parsePHPStatement("for ($a = 2;($a \<= func_num_args());$a++) {
        $args[] = func_get_arg($a);
    }");
	
	/*new(
                    expr(var(name(name("widget_class")))),
                    []);*/
      /*
  	scriptje =  binaryOperation(
                  binaryOperation(
                    binaryOperation(
                      var(name(name("max_depth"))),
                      scalar(integer(0)),
                      equal()),
                    binaryOperation(
                      var(name(name("max_depth"))),
                      binaryOperation(
                        var(name(name("depth"))),
                        scalar(integer(1)),
                        plus()),
                      gt()),
                    booleanOr()),
                  isSet([fetchArrayDim(
                        var(name(name("children_elements"))),
                        someExpr(var(name(name("id")))))]),
                  booleanAnd());
               */   
  	iprintln(scriptje);
  	println(pp(scriptje));
	scr = loadPHPFile(|file:///ufs/chrism/php/htdocs/wordpress/wp-includes/capabilities.php|);
	
	set[loc] cufaLocs = {};
	visit (scr) {
		case occ:call(name(name("call_user_func_array")), args): {
			cufaLocs += occ@at;
			//iprintln(occ);
		}
	}
	
	visit (scr) {
		case Stmt s: {
			if (s@at in cufaLocs) {
				iprintln(s);
			}
		}
	}
	
	iprintln(cufaLocs);
	return;

	loc build = |file:///export/scratch1/chrism/systems/wordpress-tests.pt|;
	
	//sys = loadPHPFiles(systemPath);
	//writeBinaryValueFile(build, sys);
	sys = readBinaryValueFile(#System, build);
	
	//iprintln(scr);
	
	
	node prevNode = "unknown"();
	set[loc] cuf_locs  = {};
	for(file <- sys) {
		sys[file] = top-down visit (sys[file]) {
			case occurrence:call(name(name("call_user_func")), args): {
				println(occurrence@at);
				cuf_locs += occurrence@at;
			}
			//case node n: {
			//	n @ parentNode = prevNode;
			//	prevNode = n;
			//	insert n;
			//	//println(":)");
			//}
		}

	}


	for(file <- sys) {
		sys[file] = top-down visit (sys[file]) {
			case node n: {
				if (n@at in cuf_locs) {
					
					iprintln(n);				
				}
			}
		}

	}
return;
	set[str] parents = {};
	visit (sys) {
		case occurrence:call(name(name("call_user_func")), args): {
			if ("parentNode" in getAnnotations(occurrence)) {
				parents += getName(occurrence @ parentNode);
				iprintln(occurrence @ parentNode);
			} else {
				println(":(");
			}	
		}
	}	
	return;
		
	str arg = "array (0 =\> class Tests_XMLRPC_wp_getTerm { public $term = NULL; protected $myxmlrpcserver = NULL; protected $factory = class WP_UnitTest_Factory { ... }; protected $backupGlobals = FALSE; protected $backupGlobalsBlacklist = array (...); protected $backupStaticAttributes = NULL; protected $backupStaticAttributesBlacklist = array (...); protected $runTestInSeparateProcess = FALSE; protected $preserveGlobalState = TRUE; private ${PHPUnit_Framework_TestCase}:inIsolation = FALSE; private ${PHPUnit_Framework_TestCase}:data = array (...); private ${PHPUnit_Framework_TestCase}:dataName = \'\'; private ${PHPUnit_Framework_TestCase}:useErrorHandler = NULL; private ${PHPUnit_Framework_TestCase}:useOutputBuffering = NULL; private ${PHPUnit_Framework_TestCase}:expectedException = NULL; private ${PHPUnit_Framework_TestCase}:expectedExceptionMessage = \'\'; private ${PHPUnit_Framework_TestCase}:expectedExceptionCode = NULL; private ${PHPUnit_Framework_TestCase}:required = array (...); private ${PHPUnit_Framework_TestCase}:name = \'test_empty_term\'; private ${PHPUnit_Framework_TestCase}:dependencies = array (...); private ${PHPUnit_Framework_TestCase}:dependencyInput = array (...); private ${PHPUnit_Framework_TestCase}:iniSettings = array (...); private ${PHPUnit_Framework_TestCase}:locale = array (...); private ${PHPUnit_Framework_TestCase}:mockObjects = array (...); private ${PHPUnit_Framework_TestCase}:status = NULL; private ${PHPUnit_Framework_TestCase}:statusMessage = \'\'; private ${PHPUnit_Framework_TestCase}:numAssertions = 0; private ${PHPUnit_Framework_TestCase}:result = class PHPUnit_Framework_TestResult { ... }; private ${PHPUnit_Framework_TestCase}:testResult = NULL; private ${PHPUnit_Framework_TestCase}:output = \'\'; private ${PHPUnit_Framework_TestCase}:outputExpectedRegex = NULL; private ${PHPUnit_Framework_TestCase}:outputExpectedString = NULL; private ${PHPUnit_Framework_TestCase}:hasPerformedExpectationsOnOutput = FALSE; private ${PHPUnit_Framework_TestCase}:outputCallback = FALSE; private ${PHPUnit_Framework_TestCase}:outputBufferingActive = TRUE }, 1 =\> \'_drop_temporary_tables\')";
	if (/^array \(0 =\> class <class:\w+> \{.*\}, 1 =\> '<method:.+>'\)$/ := arg) {
		iprintln(class);
		println("-------------------");
		iprintln(method);
	}
	
	
	loc systemPath = |file:///export/scratch1/chrism/systems/wordpress-tests/|;
	loc changedFile = |file:///export/scratch1/chrism/systems/wordpress-tests/data/wpcom-themes/tarski/header.php|;
	loc outputDir = |file:///tmp/|;
	
	loc outputFile = |file:///| + replaceFirst(changedFile.path, systemPath.path, outputDir.path);
	println(outputFile);
	return;
	
	//loc buildAltered = |file:///export/scratch1/chrism/systems/wordpress-tests.pt.altered|;
	
	
	
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

