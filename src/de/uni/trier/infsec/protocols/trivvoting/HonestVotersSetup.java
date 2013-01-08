package de.uni.trier.infsec.protocols.trivvoting;

import de.uni.trier.infsec.environment.network.Network;
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
		public int votesForA;
		public int votesForB;
		public Result() { votesForA=0; votesForB=0; }
	}

	static private boolean secret;  // SECRET INPUT
	static Result correctResult; 	// it will store the correct result computed from the votes actually used by the voters

	public static void main(String[] args) throws NetworkError {

		// DETERMINE THE VOTERS' CHOICES

		// the adversary determines two possible ways the voters vote:
		byte[] voterChoices1 = new byte[Server.NumberOfVoters];
		byte[] voterChoices2 = new byte[Server.NumberOfVoters];
		for( int i=0; i<Server.NumberOfVoters; ++i ) {
			voterChoices1[i] = (byte)Environment.untrustedInput();
			voterChoices2[i] = (byte)Environment.untrustedInput();
		}
		// we check whether they yield the same results:
		Result result1 = result(voterChoices1);
		Result result2 = result(voterChoices2);
		if( !sameResults(result1,result2) ) return; // abort, if the result in not the same in both cases
		correctResult = result1;

		// now, one of the vectors of voters' choices given by the adversary is chosen
		// to be used by the voters, depending on the value of the secret bit:
		byte[] voterChoices = new byte[Server.NumberOfVoters];
		for (int i=0; i<Server.NumberOfVoters; ++i) {
			final byte data1 = voterChoices1[i];
			final byte data2 = voterChoices2[i];
			voterChoices[i] = (secret ? data1 : data2);
		}

		// SET UP THE SYSTEM AND RUN IT

		// Register and create the server:
		final int SERVER_ID = -1;
		SAMT.AgentProxy server_proxy = SAMT.register(SERVER_ID);
		Server server = new Server(server_proxy);

		// Register the adversary, i.e. register an SMTP agent and a channel from this agent to the server
		// that can be used by the adversary.
		SAMT.AgentProxy adversary_proxy = SAMT.register(-2);
		SAMT.Channel channel_from_adversary_to_server = adversary_proxy.channelTo(SERVER_ID);

		// Register and create the voters
		Voter[] voters = new Voter[Server.NumberOfVoters];
		for( int i=0; i<Server.NumberOfVoters; ++i ) {
			SAMT.AgentProxy voter_proxy = SAMT.register(i);
			SAMT.Channel channel_from_client_to_server =  voter_proxy.channelTo(SERVER_ID);
			voters[i] = new Voter(channel_from_client_to_server);
		}

		// Main loop -- the adversary decides how many times it runs and what to do in each step:
		while( Environment.untrustedInput() != 0 )  {
			int decision = Environment.untrustedInput();
			switch (decision) {
			case 0:	// a voter (determined by the adversary) votes according to voterChoices
					int voter_id = Environment.untrustedInput();
					if (voter_id>=0 && voter_id<Server.NumberOfVoters) {
						voters[voter_id].onSendBallot(voterChoices[voter_id]);
					}
					break;

			case 1: // server reads a message (possibly a ballot) from a secure channel
					server.onCollectBallot();
					break;

			case 2: // send the result of the election (if ready) over the network
					Network.networkOut(server.getResult());
					break;

			case 3: // the adversary sends a message using its channel to the server
					byte[] message = Environment.untrustedInputMessage();
					channel_from_adversary_to_server.send(message);
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
