package de.uni.trier.infsec.protocols.trivvoting;

import de.uni.trier.infsec.functionalities.samt.ideal.SAMT;
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
		boolean ready = true;
		for( int i=0; i<NumberOfVoters; ++i ) {
			if( ! ballotCast[i] ) {
				ready = false;
				break;
			}
		}
		return ready;
	}

	/*
	 * Compute and return the result of the election. The result is formatted as a byte-string.
	 */
	public byte[] getResult() {
		if (!resultReady()) return null; // the result is only returned when all the voters have voted

		byte[] result =  MessageTools.concatenate(
							MessageTools.intToByteArray(votesForA),
							MessageTools.intToByteArray(votesForB));
		return result;
	}
}
