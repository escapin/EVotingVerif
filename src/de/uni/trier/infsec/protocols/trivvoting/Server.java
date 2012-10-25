package de.uni.trier.infsec.protocols.trivvoting;

import de.uni.trier.infsec.functionalities.pkenc.ideal.Decryptor;
import de.uni.trier.infsec.utils.MessageTools;

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
	private /*@ nullable @*/ Decryptor serverDecr = null;
	
	
	//@ invariant ballotCast.length == NumberOfVoters;

	public Server(Decryptor serverDecr ) {
		this.serverDecr = serverDecr;
		for( int i=0; i<NumberOfVoters; ++i)
			ballotCast[i] = false; // initially no voter has cast her ballot
	}

	/*
	 * Collect a ballot from the voter identified by voterID. 
	 */
	/*@ normal_behavior
	  @   requires ballot.length == NumberOfVoters;
	  @   requires 0 <= voterID && voterID < NumberOfVoters;
	  @   requires !ballotCast[voterID];
	  @   ensures ballotCast[voterID];
	  @   ensures ballot[voterID] == 0 ==> votesForA == \old(votesForA)+1;
      @   ensures ballot[voterID] == 1 ==> votesForB == \old(votesForB)+1;
      @   assignable ballotCast[voterID], votesForA, votesForB;
	  @*/
	public void collectBallot(int voterID, byte[] ballot) {
		if( voterID<0 || voterID>=NumberOfVoters ) return;  // invalid  voter ID
		if( ballotCast[voterID] ) return;  // the voter has already voted
		ballotCast[voterID] = true; 
		int candidate = ballot[voterID];
		if (candidate==0) ++votesForA;
		if (candidate==1) ++votesForB;
		// all the remaining values are consider invalid
	}

	/*
	 * Compute and return the result of the election. The result is formatted as a byte-string.
	 */
	public byte[] getResult() {
		// PROVE THAT:
		// votesForA == PassiveAdvSetup.correctResult.votesForA;
		// votesForB == PassiveAdvSetup.correctResult.votesForB;

		byte[] result =  MessageTools.concatenate(
							MessageTools.intToByteArray(votesForA),
							MessageTools.intToByteArray(votesForB));
		return result;
	}
}
