package de.uni.trier.infsec.eVotingVerif.apps;

import java.io.File;

public class ParamsApp
{
	public static final String PATH_AMT = System.getProperty("java.io.tmpdir") + File.separator + "smtvote" + File.separator + "server.amt";
	public static final String PATH_SMT = System.getProperty("java.io.tmpdir") + File.separator + "smtvote" + File.separator + "server.smt";
	public static final String PATH_BB = System.getProperty("java.io.tmpdir") + File.separator + "smtvote" + File.separator + "bulletinBoard.amt";
	
	public static int numberOfVoters = 50;
	public static int numberOfCandidates = 5;
}
