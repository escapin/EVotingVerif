package de.uni.trier.infsec.protocols.trivvoting;

import de.uni.trier.infsec.environment.network.NetworkError;
import de.uni.trier.infsec.environment.Environment;
import de.uni.trier.infsec.functionalities.samt.ideal.SAMT;


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
	 * Objects representing a result of the e-voting process. For now, two candidates only.
	 */
	static class Result {
		public int votesForA = 0;
		public int votesForB = 0;
	}

	/*
	 * Class with static fields to store the correct result computed from the votes actually
	 * used by the voters. This class plays the role of the class M from the hybrid approach,
	 * as described in the paper.
	 */
	static class CorrectResult {
                static public boolean exists = false;
		static public int votesForA = 0;
		static public int votesForB = 0;
	}

	static private boolean secret;  // SECRET INPUT
    private /*@ spec_public @*/ final static byte[] voterChoices = new byte[Server.NumberOfVoters];
        public /*@ spec_public @*/ static byte[] voterChoices1;
        public /*@ spec_public @*/ static byte[] voterChoices2;

        private static void initVoterChoices() {
            	voterChoices1 = new byte[Server.NumberOfVoters];
		voterChoices2 = new byte[Server.NumberOfVoters];
		for( int i=0; i<Server.NumberOfVoters; ++i ) {
			voterChoices1[i] = (byte)Environment.untrustedInput();
			voterChoices2[i] = (byte)Environment.untrustedInput();
		}
        }

        private static void computeCorrectResult() {
            Result result1 = result(voterChoices1);
            Result result2 = result(voterChoices2);
            CorrectResult.exists = sameResults(result1,result2); // if the result is not the same in both cases, no correct result exists
            CorrectResult.votesForA = result1.votesForA; // (hybrid approach extension)
            CorrectResult.votesForB = result1.votesForB; // (hybrid approach extension)
        }

        private static void chooseVoterChoices() {
            for (int i=0; i<Server.NumberOfVoters; ++i) {
                    final byte data1 = voterChoices1[i];
                    final byte data2 = voterChoices2[i];
                    voterChoices[i] = (secret ? data1 : data2);
            }
        }

	public static void main(String[] args) throws NetworkError {

		// DETERMINE THE VOTERS' CHOICES AND THE CORRECT RESULT

		// the adversary determines two possible ways the voters vote:
                initVoterChoices();
		// we check whether they yield the same results:
                computeCorrectResult();
                if (!CorrectResult.exists) return; // abort, if the result is not the same in both cases
                chooseVoterChoices();

		// SET UP THE SYSTEM AND RUN IT

		// Register and create the bulletin board:
		BulletinBoard BB = new BulletinBoard();

		// Register and create the server:
		Server server = new Server();

		// Register the adversary, i.e. register an SMTP agent and a channel from this agent to the server
		// that can be used by the adversary.
                Adversary adversary = new Adversary();

		// Register and create the voters
		Voter[] voters = new Voter[Server.NumberOfVoters];
		for( int i=0; i<Server.NumberOfVoters; ++i ) {
			voters[i] = new Voter();
		}

		// Main loop -- the adversary decides how many times it runs and what to do in each step:
		while( Environment.untrustedInput() != 0 )  {
			byte[] message;
			int decision = Environment.untrustedInput();
			switch (decision) {
			case 0:	// a voter (determined by the adversary) votes according to voterChoices
					int voter_id = Environment.untrustedInput();
					if (voter_id>=0 && voter_id<Server.NumberOfVoters) {
						voters[voter_id].onSendBallot();
					}
					break;

			case 1: // server reads a message (possibly a ballot) from a secure channel
					server.onCollectBallot();
					break;

			case 2: // the server sends the result of the election (if ready) over the network
					server.onSendResult();
					break;

			case 3: // the server posts the result of the election (if ready) on the bulletin board
					server.onPostResult();
					break;

			case 4: // the bulletin board reads a message:
					BB.onPost();
					break;

			case 5: // the bulletin board sends its content (over the network):
					BB.onRequestContent();
					break;

			case 6: // the adversary sends a message using its channel to the server
					message = Environment.untrustedInputMessage();
					adversary.channel_to_server.send(message);
					break;

			case 7: // the adversary sends a message using its channel to the bulletin board
					message = Environment.untrustedInputMessage();
					adversary.channel_to_BB.send(message);
					break;
			}
		}
	}

	/*
	 * Compute the correct result from a vector of voters' choices
	 */
	public static Result result(byte[] choices) {
		Result result = new Result();
		for( int i=0; i<choices.length; ++i ) {
			int candidate = choices[i];
			if (candidate==0) result.votesForA++;
			if (candidate==1) result.votesForB++;
			// all the remaining values as considered as invalid
		}
		return result;
	}

	/*
	 * Check whether two results are the same.
	 */
	public static boolean sameResults(Result res1, Result res2 ) {
		return res1.votesForA==res2.votesForA  &&  res1.votesForB==res2.votesForB;
	}
}
