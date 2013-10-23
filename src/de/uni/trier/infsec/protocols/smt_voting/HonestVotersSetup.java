package de.uni.trier.infsec.protocols.smt_voting;

import de.uni.trier.infsec.environment.Environment;

/*
 * A setup for a server and (multiple) honest clients using secure authenticated channel
 * (secure, authenticated message transmission functionality) to send their choices
 * to the server.
 *
 * The adversary determines two variants of voters'choices, one of which is picked, based
 * on the value of the secret bit. During the voting process the adversary determines actions
 * to be taken.
 */
public class HonestVotersSetup {

	/*
	 * Class with static fields to store the correct result computed from the votes actually
	 * used by the voters. This class plays the role of the class M from the hybrid approach,
	 * as described in the paper.
	 */
	static class CorrectResult {
		static public int votesForA = 0;
		static public int votesForB = 0;
	}

	/**
	 * Objects representing a result of the e-voting process. For now, two candidates only.
	 */
	static class Result {
		public int votesForA = 0;
		public int votesForB = 0;
	}

	/**
	 * Compute the correct result from a vector of voters' choices
	 */
	private static Result result(byte[] choices) {
		Result result = new Result();
		for( int i=0; i<choices.length; ++i ) {
			int candidate = choices[i];
			if (candidate==0) result.votesForA++;
			if (candidate==1) result.votesForB++;
			// all the remaining values as considered as invalid
		}
		return result;
	}

	/**
	 * Check whether two results are the same.
	 */
	private static boolean sameResults(Result res1, Result res2 ) {
		return res1.votesForA==res2.votesForA  &&  res1.votesForB==res2.votesForB;
	}


	static private boolean secret;  // SECRET INPUT

	static private Voter[] voters;
	static private Server server;

	
	/**
	 * Computes the correct result, as determined by the vectors voters' choices given as parameters,
	 * checks if these two vectors yield the same result. If not, false is returned. Otherwise, voters
	 * are registered and created.
	 */
	private static boolean select_voters_choices_and_create_voters(byte[] voterChoices1, byte[] voterChoices2)  {
		// we check whether voterChoices1 and voterChoices2 yield the same results:
		boolean status = computeCorrectResult(voterChoices1, voterChoices2);
		if (!status) return false;

		// now, one of the vectors of voters' choices given by the adversary is chosen
		// to be used by the voters, depending on the value of the secret bit:
		byte[] voterChoices = chooseVoterChoices(voterChoices1, voterChoices2);

		// Register and create the voters
		registerAndCreateVoters(voterChoices);

		return true;
	}

	/**
	 * Checks whether voterChoices1 and voterChoices2 yield the same results
	 */
	private static boolean computeCorrectResult(byte[] voterChoices1, byte[] voterChoices2) {
		Result result1 = result(voterChoices1);
		Result result2 = result(voterChoices2);
		if( !sameResults(result1,result2) ) return false;
		CorrectResult.votesForA = result1.votesForA; // (hybrid approach extension)
		CorrectResult.votesForB = result1.votesForB; // (hybrid approach extension)
		return true;
	}

	/**
	 * One of the vectors of voters' choices given by the adversary is chosen
	 * to be used by the voters, depending on the value of the secret bit:
	 */
	private static byte[] chooseVoterChoices(byte[] voterChoices1, byte[] voterChoices2) {
		byte[] voterChoices = new byte[Server.NumberOfVoters];
		for (int i=0; i<Server.NumberOfVoters; ++i) {
			final byte data1 = voterChoices1[i];
			final byte data2 = voterChoices2[i];
			voterChoices[i] = (secret ? data1 : data2);
		}
		return voterChoices;
	}

	/**
	 * Register and create the voters.
	 */
	private static void registerAndCreateVoters(byte[] voterChoices)  {
		voters = new Voter[Server.NumberOfVoters];
		for( int i=0; i<Server.NumberOfVoters; ++i ) {
			voters[i] = new Voter(i, voterChoices[i]);
		}
	}

	private static void onVote()  {
		int voter_id = Environment.untrustedInput();
		if (voter_id>=0 && voter_id<Server.NumberOfVoters) {
			voters[voter_id].onSendBallot(server);
		}
	}


	/**
	 * Run the main loop of the setup.
	 */
	private static void run()  {
		// Main loop -- the adversary decides how many times it runs and what to do in each step:
		while( Environment.untrustedInput() != 0 )  {
			int decision = Environment.untrustedInput();
			switch (decision) {
			case 0:	// a voter (determined by the adversary) votes according to voterChoices
				onVote();
				break;

			case 1: // the server posts the result of the election (if ready) on the bulletin board
				server.onPostResult();
				break;
			}
		}
	}

	public static void main(String[] args)  {
		// the adversary determines two possible ways the voters vote:
		byte[] voterChoices1 = new byte[Server.NumberOfVoters];
		byte[] voterChoices2 = new byte[Server.NumberOfVoters];
		for( int i=0; i<Server.NumberOfVoters; ++i ) {
			voterChoices1[i] = (byte)Environment.untrustedInput();
			voterChoices2[i] = (byte)Environment.untrustedInput();
		}

		boolean status = select_voters_choices_and_create_voters(voterChoices1, voterChoices2);
		if (!status) return;
		server = new Server();
		run();
	}
}
