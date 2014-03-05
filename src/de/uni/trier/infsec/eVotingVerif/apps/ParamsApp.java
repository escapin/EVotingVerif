package de.uni.trier.infsec.eVotingVerif.apps;

import java.io.File;

public class ParamsApp
{
	public static final String PATH_STORAGE = System.getProperty("java.io.tmpdir") + File.separator + "smtvote" + File.separator;
	public static final String PATH_AMT =  PATH_STORAGE + "server.amt";
	public static final String PATH_SMT = PATH_STORAGE + "server.smt";
	public static final String PATH_BB = PATH_STORAGE + "bulletinBoard.amt";
	public static final String PATH_VOTER = PATH_STORAGE + "voter%%%%.smt";
	
	public static final String PKI_DATABASE = System.getProperty("java.io.tmpdir") + File.separator + "PKI_server.db";
	// = de.uni.trier.infsec.functionalities.pki.PKIServerCore.DEFAULT_DATABASE;
	
	/*
	 * An array containing all files in memory which are not in PATH_STORAGE.
	 * It must remain up-to-date with all files saved in the file-system.
	 */
	public static final String[] PATH_LOCALFILES = { PKI_DATABASE };  
	
	public static int numberOfVoters = 3;
	public static int numberOfCandidates = 2;
}
