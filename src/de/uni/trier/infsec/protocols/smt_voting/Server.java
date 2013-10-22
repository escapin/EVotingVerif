package de.uni.trier.infsec.protocols.smt_voting;

import de.uni.trier.infsec.environment.Environment;

/*
 * The server of TrivVoting. Collects votes send to it directly (via method call).
 * 
 * Two-candidates case only (for now).
 */
public class Server {

	public static final int NumberOfVoters = 50;
	private final boolean[] ballotCast;  // ballotCast[i]==true iff the i-th voter has already cast her ballot
	private int votesForA;
	private int votesForB;

	public Server() {
		votesForA = 0;
        votesForB = 0;
        ballotCast = new boolean[NumberOfVoters]; // initially no voter has cast her ballot
	}

	/*
	 * Collect one ballot (read from a secure channel)
	 */
	public void onCollectBallot(int voterID, byte[] ballot) {
		if( voterID<0 || voterID>=NumberOfVoters ) return;  // invalid  voter ID
		if( ballotCast[voterID] ) return;  // the voter has already voted
		ballotCast[voterID] = true; 
		if( ballot==null || ballot.length!=1 ) return;  // malformed ballot
		int candidate = ballot[0];
		if (candidate==0) ++votesForA;
		if (candidate==1) ++votesForB;
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
	 * Post the result (if ready) on the bulletin board.
	 */
	public void onPostResult()  {
		byte[] result = getResult();
		if (result != null)
			Environment.untrustedOutputMessage(result);
	}

	private byte[] getResult() {
		if (!resultReady()) return null; // the result is only returned when all the voters have voted

		// PROVE THAT
		// 		votesForA == HonestVotersSetup.CorrectResult.votesForA
		// 		votesForB == HonestVotersSetup.CorrectResult.votesForB
		// (this shows that the extension is conservative)
		votesForA = HonestVotersSetup.CorrectResult.votesForA; // (hybrid approach extension)
		votesForB = HonestVotersSetup.CorrectResult.votesForB; // (hybrid approach extension)

		return formatResult(votesForA, votesForB);
	}

	/*
	 * Format the result of the election.
	 */
	private static byte[] formatResult(int a, int b) {
		String s = "Result of the election:";
		s += "  Number of voters = " + NumberOfVoters + "\n";
		s += "  Number of votes for candidate 1 =" + a + "\n";
		s += "  Number of votes for candidate 2 =" + b + "\n";
		return s.getBytes();
	}
}
