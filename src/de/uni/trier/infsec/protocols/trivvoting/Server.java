package de.uni.trier.infsec.protocols.trivvoting;

import de.uni.trier.infsec.environment.network.Network;
import de.uni.trier.infsec.environment.network.NetworkError;
import de.uni.trier.infsec.functionalities.samt.ideal.SAMT;
import de.uni.trier.infsec.functionalities.amt.ideal.AMT;

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
	private final SAMT.AgentProxy samt_proxy;
	private final AMT.Channel channel_to_BB;
	
	/*@ model \locset footprint;
	  @ represents footprint = \set_union(this.*,\set_union(ballotCast[*],
	  @                                \set_union(HonestVotersSetup.voterChoices[*],\locset(HonestVotersSetup.voterChoices, 
	  @                                channel_to_BB.sender, channel_to_BB.sender.ID, Identifiers.SERVER_ID))));
	  @ accessible footprint : \empty;
	  @*/


        /*@ invariant
          @     votesForA ==
          @         (\sum int i; 0 <= i && i < NumberOfVoters;
          @             (ballotCast[i] && HonestVotersSetup.voterChoices[i] == 0) ? 1 : 0);
          @ invariant
          @     votesForB ==
          @         (\sum int i; 0 <= i && i < NumberOfVoters;
          @             (ballotCast[i] && HonestVotersSetup.voterChoices[i] == 1) ? 1 : 0);
          @ invariant channel_to_BB.sender.ID == Identifiers.SERVER_ID;
          @ invariant ballotCast.length == NumberOfVoters
          @           && HonestVotersSetup.voterChoices.length == NumberOfVoters;
          @ accessible \inv : footprint;
          @*/


        /*@ public normal_behavior
          @     requires    proxy.ID == Identifiers.SERVER_ID;
          @     ensures     true;   // and implicitly \invariant_for(this);
          @*/
        public Server() {
                samt_proxy = SAMT.register(Identifiers.SERVER_ID);
		AMT.AgentProxy amt_proxy = AMT.register(Identifiers.SERVER_ID);
                channel_to_BB = amt_proxy.channelTo(Identifiers.BULLETIN_BOARD_ID);
		for( int i=0; i<NumberOfVoters; ++i)
			ballotCast[i] = false; // initially no voter has cast her ballot
	}

	/*
	 * Collect one ballot (read from a secure channel)
	 */
        // to be specified
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
    //@ ensures \result == (\forall int i; 0 <= i && i < NumberOfVoters; ballotCast[i]);
	//@ strictly_pure
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
        // to be specified
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

    //@ requires resultReady();
	//@ pure // (this shows that the extension is conservative)
	private byte[] getResult() {
		if (!resultReady()) return null; // the result is only returned when all the voters have voted

		
		votesForA = HonestVotersSetup.CorrectResult.votesForA; // (hybrid approach extension)
		votesForB = HonestVotersSetup.CorrectResult.votesForB; // (hybrid approach extension)

		return formatResult(votesForA, votesForB);
	}

	/*
	 * Format the result of the election.
	 */
	//@ ensures true;
	//@ pure helper
	static byte[] formatResult(int a, int b) {
		String s = "Result of the election:";
		s += "  Number of voters = " + NumberOfVoters + "\n";
		s += "  Number of votes for candidate 1 =" + a + "\n";
		s += "  Number of votes for candidate 2 =" + b + "\n";
		return s.getBytes();
	}
}
