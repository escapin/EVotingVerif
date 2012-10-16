package de.uni.trier.infsec.protocols.trivvoting;

import de.uni.trier.infsec.environment.network.Network;
import de.uni.trier.infsec.environment.network.NetworkError;
import de.uni.trier.infsec.environment.Environment;
import de.uni.trier.infsec.functionalities.pkenc.ideal.Decryptor;
import de.uni.trier.infsec.functionalities.pkenc.ideal.Encryptor;

/*
 * A setup for a server and (multiple) clients with a passive adversary.
 *
 * It creates one server and some (fixed) number of voters. The adversary determines
 * two variants of voters'choices, one of which is picked, based on the value of the
 * secret bit. During the voting process the adversary is passive: it gets all the sent
 * messages, but does not interfere with the process (all the ballots are delivered).
 */
public class PassiveAdvSetup {
		
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

		// create the server's keys:
		Decryptor serverDec = new Decryptor();
		Encryptor serverEnc = serverDec.getEncryptor();
		Network.networkOut(serverEnc.getPublicKey()); // the public key of the server is published
		
		// create the server:
		Server server = new Server(serverDec);
		
		// create the voters
		Voter[] voters = new Voter[Server.NumberOfVoters];
		for( int i=0; i<Server.NumberOfVoters; ++i ) {
			voters[i] = new Voter(serverEnc);
		}

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
		byte[] voterChoices = (secret ? voterChoices1 : voterChoices2);

		// voting (the voters create ballots and cast them directly to the server):
		for( int i=0; i<Server.NumberOfVoters; ++i ) {
			byte[] ballot = voters[i].makeBallot(voterChoices[i]);  // create a ballot
			// Network.networkOut(ballot);  	// send it over the network (but not now: no encryption is used)
			server.collectBallot(i, ballot);  	// and deliver it directly to the server
		}

		// output the final result:
		byte[] result = server.getResult();
		Network.networkOut(result);
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

