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

	public static final int NumberOfVoters = 50;
	private final boolean[] ballotCast = new boolean[NumberOfVoters];  // ballotCast[i]==true iff the i-th voter has already cast her ballot
	private int votesForA = 0;
	private int votesForB = 0;
	private final SAMT.AgentProxy server_proxy;
	private final SAMT.Channel channel_to_BB;


        /*@ invariant
          @     votesForA =
          @         (\sum int i; 0 <= i && i < voterChoices.length;
          @             (ballotCast[i] && HonestVotersSetup.voterChoices[i] == 0) ? 1 : 0);
          @ invariant
          @     votesForB =
          @         (\sum int i; 0 <= i && i < voterChoices.length;
          @             (ballotCast[i] && HonestVotersSetup.voterChoices[i] == 1) ? 1 : 0);
          @ invariant channel_to_BB.sender.ID == Identifiers.SERVER_ID;
          @*/


        /*@ public normal_behavior
          @     requires    proxy.ID == Identifiers.SERVER_ID;
          @     ensures     true;   // and implicitly \invariant_for(this);
          @*/
        public Server(SAMT.AgentProxy proxy) {
		server_proxy = proxy;
		channel_to_BB = server_proxy.channelTo(Identifiers.BULLETIN_BOARD_ID);
		for( int i=0; i<NumberOfVoters; ++i)
			ballotCast[i] = false; // initially no voter has cast her ballot
	}

	/*
	 * Collect one ballot (read from a secure channel)
	 */
        //@ to be specified
	public void onCollectBallot() {
		SAMT.AuthenticatedMessage am = server_proxy.getMessage();
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
        //@ to be specified
	public boolean resultReady() {
		for( int i=0; i<NumberOfVoters; ++i ) {
			if( !ballotCast[i] )
				return false;
		}
		return true;
	}

	/*
	 * Send the result (if ready) of the election over the network.
	 */
        //@ to be specified
	public void onSendResult() throws NetworkError {
		byte[] result = getResult();
		if (result != null)
			Network.networkOut(result);
	}

	/*
	 * Post the result (if ready) on the bulletin board.
	 */
        /*@ public normal_behavior
          @     ensures true;
          @*/
	public void onPostResult() {
		byte[] result = getResult();
		if (result != null)
			channel_to_BB.send(result);
	}

        //@ to be specified
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
	static byte[] formatResult(int a, int b) {
		String s = "Result of the election:";
		s += "  Number of voters = " + NumberOfVoters + "\n";
		s += "  Number of votes for candidate 1 =" + a + "\n";
		s += "  Number of votes for candidate 2 =" + b + "\n";
		return s.getBytes();
	}
}
