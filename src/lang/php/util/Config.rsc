module lang::php::util::Config

public loc phploc = |file:///usr/bin/php|;

public loc parserLoc = |file:///ufs/chrism/php/PHPAnalysis|;
public loc rgenLoc = parserLoc + "PHP-Parser/lib/Rascal/AST2Rascal.php";
public loc rgenCwd = parserLoc + "PHP-Parser/lib/Rascal";

public loc baseLoc = |file:///ufs/chrism/php/PHPAnalysis|;
public loc parsedDir = baseLoc + "parsed";
public loc statsDir = baseLoc + "stats";
public loc corpusRoot = baseLoc + "corpus-icse13";
public loc countsDir = baseLoc + "counts";

public bool useBinaries = false;

