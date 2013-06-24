module lang::php::experiments::cmulder::test_script

import lang::php::ast::AbstractSyntax;
import lang::php::util::Utils;
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
	str testStr1 = "array (0 =\> array (0 =\> class stdClass { ... }))";
	str testStr2 = "array (0 =\> array (0 =\> class stdClass { ... }), 1 =\> array (0 =\> class stdClass { ... }, 1 =\> class stdClass { ... }, 2 =\> class stdClass { ... }))";
	str testStr3 = "array (0 =\> \'\', 1 =\> class WP_Post { public $ID = 2; public $post_author = \'1\'; public $post_date = \'2013-06-19 11:25:15\'; public $post_date_gmt = \'2013-06-19 11:25:15\'; public $post_content = \'This is an example page. It\'s different from a blog post because it will stay in one place and will show up in your site navigation (in most themes). Most people start with an About page that introduces them to potential site visitors. It might say something like this:\n\n\<blockquote\>Hi there! I\\\'m a bike messenger by day, aspiring actor by night, and this is my blog. I live in Los Angeles, have a great dog named Jack, and I like pi&#241;a coladas. (And gettin\\\' caught in the rain.)\</blockquote\>\n\n...or s...\'; public $post_title = \'Sample Page\'; public $post_excerpt = \'\'; public $post_status = \'publish\'; public $comment_status = \'open\'; public $ping_status = \'open\'; public $post_password = \'\'; public $post_name = \'sample-page\'; public $to_ping = \'\'; public $pinged = \'\'; public $post_modified = \'2013-06-19 11:25:15\'; public $post_modified_gmt = \'2013-06-19 11:25:15\'; public $post_content_filtered = \'\'; public $post_parent = 0; public $guid = \'http://127.0.0.1:9999/wordpress/?page_id=2\'; public $menu_order = 0; public $post_type = \'page\'; public $post_mime_type = \'\'; public $comment_count = \'0\'; public $filter = \'raw\' }, 2 =\> 0, 3 =\> array (\'depth\' =\> 0, \'show_date\' =\> \'\', \'date_format\' =\> \'F j, Y\', \'child_of\' =\> 0, \'exclude\' =\> \'\', \'title_li\' =\> \'\', \'echo\' =\> FALSE, \'authors\' =\> \'\', \'sort_column\' =\> \'menu_order, post_title\', \'link_before\' =\> \'\', \'link_after\' =\> \'\', \'walker\' =\> \'\', \'menu_class\' =\> \'nav-menu\', \'menu\' =\> \'\', \'container\' =\> \'div\', \'container_class\' =\> \'\', \'container_id\' =\> \'\', \'menu_id\' =\> \'\', \'fallback_cb\' =\> \'wp_page_menu\', \'before\' =\> \'\', \'after\' =\> \'\', \'items_wrap\' =\> \'\<ul id=\"%1$s\" class=\"%2$s\"\>%3$s\</ul\>\', \'theme_location\' =\> \'primary\', \'show_home\' =\> TRUE, \'hierarchical\' =\> 0, \'has_children\' =\> FALSE), 4 =\> 0)";

	int i = -1;
		
	list[int] stack = [];
	for (/<el:\d+> =\>/ := testStr2) {
		stack = stack + toInt(el);
		println("el:<el>");
	}
	
	iprintln(stack);
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

