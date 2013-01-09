package de.uni.trier.infsec.protocols.trivvoting;

import de.uni.trier.infsec.environment.network.Network;
import de.uni.trier.infsec.environment.network.NetworkError;
import de.uni.trier.infsec.functionalities.samt.ideal.SAMT;

/*
 * The server of TrivVoting. Collects votes send to it directly (via method call).
 * 
 * Two-candidates case only (for now).
 */
public class Server {

	public static int NumberOfVoters = 50;
	private boolean[] ballotCast = new boolean[NumberOfVoters];  // ballotCast[i]==true iff the i-th voter has already cast her ballot
	private int votesForA = 0;
	private int votesForB = 0;
	private SAMT.AgentProxy samt_proxy = null;

	public Server(SAMT.AgentProxy samt_proxy) {
		this.samt_proxy = samt_proxy;
		for( int i=0; i<NumberOfVoters; ++i)
			ballotCast[i] = false; // initially no voter has cast her ballot
	}

	/*
	 * Collect one ballot (read from a secure channel)
	 */
	public void onCollectBallot() {
		SAMT.AuthenticatedMessage am = samt_proxy.getMessage();
		if (am==null) return;
		int voterID = am.sender_id;
		byte[] ballot = am.message;

		if( voterID<0 || voterID>=NumberOfVoters ) return;  // invalid  voter ID
		if( ballotCast[voterID] ) return;  // the voter has already voted
		ballotCast[voterID] = true; 
		if( ballot==null || ballot.length!=1 ) return;  // malformed ballot
		int candidate = ballot[0];
		if (candidate==0) ++votesForA;
		if (candidate==1) ++votesForB;
		// all the remaining values are consider invalid
	}

	/*
	 * Returns true if the result is ready, that is if all the eligible voters have already voted.
	 */
	public boolean resultReady() {
		for( int i=0; i<NumberOfVoters; ++i ) {
			if( !ballotCast[i] )
				return false;
		}
		return true;
	}

	/*
	 * Compute and send the result of the election over the network.
	 */
	public void onSendResult() throws NetworkError {
		if (!resultReady()) return; // the result is only returned when all the voters have voted

		// PROVE THAT
		// 		votesForA == HonestVotersSetup.CorrectResult.votesForA
		// 		votesForB == HonestVotersSetup.CorrectResult.votesForB
		// (this shows that the extension is conservative)
		votesForA = HonestVotersSetup.CorrectResult.votesForA; // (hybrid approach extension)
		votesForB = HonestVotersSetup.CorrectResult.votesForB; // (hybrid approach extension)

		byte[] formatedResult =	formatResult(votesForA, votesForB);
		Network.networkOut(formatedResult);
	}

	/*
	 * Format the result of the election.
	 */
	static byte[] formatResult(int a, int b) {
		String s = "Result of the election:";
		s += "  Number of voters = " + NumberOfVoters + "\n";
		s += "  Number of votes for candidate 1 =" + a + "\n";
		s += "  Number of votes for candidate 2 =" + b + "\n";
		return s.getBytes();
	}
}
