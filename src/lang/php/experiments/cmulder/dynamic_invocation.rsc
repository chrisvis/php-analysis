module lang::php::experiments::cmulder::dynamic_invocation

import lang::php::ast::AbstractSyntax;
import lang::php::util::Utils;
import Node;

import IO;
import ValueIO;
import lang::csv::IO;
import util::Math;

import Set;

public void importTraces() {
	loc tracesCsv = |file:///ufs/chrism/data/call_user_func.csv.notestsuite|;

	traces = { <readTextValueString(#loc,a), b > | < a, b > <- readCSV(#rel[str,str], tracesCsv) };

	iprint(traces);
	iprint(size(traces));
	return traces;
}

public map[loc, node] findOccurences() {
	ast = loadPHPFile(|file:///ufs/chrism/php/thesis/examples/call_user_func.php|);
	
	calls = [c | /c:call(name(name(n)), _) := ast, /^call_user_func/ := n];

	map[loc, node] occurences = ();
	occurences += ( c@at : c | c <- calls);
	
	return occurences;
}

public void main() {
	//iprint(findOccurences());
	//importTraces();
	
	buildBinaries("ZendFramework", "2.0", |file:///ufs/chrism/php/zf2/|);
	// = loadBinary("ZendFramework", "2.0");
	//iprint(pt);

	//buildBinaries("Drupal", "7.14");
	//ast = loadBinary("ZendFramework", "2.0");
	
	
	//ast = loadPHPFile(|file:///ufs/chrism/php/thesis/examples/call_user_func.php|);


	//callsAt = [c | c <- calls,  c@at == |file:///ufs/gast698/php/PHPAnalysis/corpus-icse13/CodeIgniter/codeigniter_2.1.2/system/core/CodeIgniter.php|(0,0,<359,0>,<359,0>)]; 
	
		
	//["at"] == |file:///ufs/gast698/php/PHPAnalysis/corpus-icse13/CodeIgniter/codeigniter_2.1.2/system/core/CodeIgniter.php| ) := calls];
	
	/*
	println("----------------");
	
	// call_user_func with static string parameter 
	calls = [c | /c:call(name(name("call_user_func")), [actualParameter(scalar(_),_)]) := ast ];
	iprint(calls);
	
	println("----------------");
	
	// call_user_func with static array parameter
	calls = [c | /c:call(name(name("call_user_func")), [actualParameter(array([arrayElement(_, scalar(_),_),arrayElement(_, scalar(_),_)]),_)]) := ast ];
	iprint(calls);
	*/

}
