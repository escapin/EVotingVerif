package de.uni.trier.infsec.protocols.core;

import java.io.File;

public class Params {
	/*
	 * Agent identifiers.
	 */
	public static final int SERVER_ID = -1;
	public static final int BULLETIN_BOARD_ID = -2;
	// eligible voters get the identifiers in the range 0..Server.NumberOfVoters
	
	static final int DEFAULT_LISTEN_PORT_SERVER_AMT = 4088; // Listen port for Voter requests
	static final int DEFAULT_LISTEN_PORT_SERVER_SMT = 4089; // Listen port for Voter requests

	static final int DEFAULT_LISTEN_PORT_BBOARD_AMT = 4090; 		// Listen port for Server requests
	static final int DEFAULT_LISTEN_PORT_BBOARD_SMT = 4091; 		// Listen port for Server requests
	static final int DEFAULT_LISTEN_PORT_BBOARD_REQUEST = 4092; 	// Listen port for result requests

	static final String DEFAULT_HOST_SERVER = "localhost";
	static final String DEFAULT_HOST_BBOARD = "localhost";
	
	public static final String PATH_AMT = System.getProperty("java.io.tmpdir") + File.separator + "smtvote" + File.separator + "server.amt";
	public static final String PATH_SMT = System.getProperty("java.io.tmpdir") + File.separator + "smtvote" + File.separator + "server.smt";
}
