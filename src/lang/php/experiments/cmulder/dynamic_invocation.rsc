module lang::php::experiments::cmulder::dynamic_invocation

import lang::php::ast::AbstractSyntax;
import lang::php::util::Utils;

import IO;

public void main() {
	//buildBinaries("Test", "0.1", |file:///ufs/chrism/php/thesis/examples/|);
	//pt = loadBinary("Test", "0.1");
	//iprint(pt);
	
	ast = loadPHPFile(|file:///ufs/chrism/php/thesis/examples/call_user_func.php|);
	
	// call_user_func with static string parameter 
	calls = [c | /c:call(name(name("call_user_func")), [actualParameter(scalar(_),_)]) := ast ];
	iprint(calls);
	
	println("----------------");
	
	// call_user_func with static array parameter
	calls = [c | /c:call(name(name("call_user_func")), [actualParameter(array([arrayElement(_, scalar(_),_),arrayElement(_, scalar(_),_)]),_)]) := ast ];
	iprint(calls);
	
}
