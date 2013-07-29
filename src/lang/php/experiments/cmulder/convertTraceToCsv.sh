#!/bin/sh
if [ -z "$2" ] 
then 
	echo "Usage: convertTraceToCsv <inputFile> <outputFile>"
	exit 0
fi

awk -F '\t' '{
	if ($6 == "call_user_func" || $6 == "call_user_func_array" || $6 == "eval" ) {  
		if ($6 == "eval") {
			param1 = $8;
			param2 = "";
		} else {
			param1 = $12;
			param2 = $13;
		}
		gsub("\"","\"\"",param1);
		gsub("\"","\"\"",param2);  
		print "\"" $6 "\"," "\"|file://" $9 "|(0,0,<" $10 ",0>,<" $10 ",0>)\",\"" param1 "\",\"" param2 "\"";
	} 
}' $1 >> $2

