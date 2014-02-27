package de.uni.trier.infsec.protocols.smt_voting;

import de.uni.trier.infsec.functionalities.pki_nocorrupt.PKIError;
import de.uni.trier.infsec.functionalities.smt.SMT;
import de.uni.trier.infsec.functionalities.smt.SMT.SMTError;
import de.uni.trier.infsec.functionalities.amt.AMT;
import de.uni.trier.infsec.functionalities.amt.AMT.AMTError;

public class Server {
	private final int numberOfVoters;
    private final int numberOfCandidates;
	private final boolean[] ballotCast;  // ballotCast[i]==true iff the i-th voter has already cast her ballot
	private final int[] votesForCandidates;
	private final SMT.Receiver receiver;
	private final AMT.Sender sender;

	public Server(int numberOfVoters, int numberOfCandidates, 
			      SMT.Receiver receiver, AMT.Sender sender_to_BB) throws AMTError, PKIError {
		this.numberOfVoters = numberOfVoters;
		this.numberOfCandidates = numberOfCandidates;
		this.receiver = receiver;
		this.sender = sender_to_BB;
		votesForCandidates = new int[numberOfCandidates];		
		ballotCast = new boolean[numberOfVoters]; // initially no voter has cast her ballot
		receiver.listenOn(Parameters.DEFAULT_LISTEN_PORT_SERVER_SMT);
	}

	/*
	 * Collect one ballot (read from a secure channel)
	 */
	public void onCollectBallot() throws SMTError {
		SMT.AuthenticatedMessage authMsg = receiver.getMessage(Parameters.DEFAULT_LISTEN_PORT_SERVER_SMT);
		onCollectBallot(authMsg);
	}
	
	private void onCollectBallot(SMT.AuthenticatedMessage authMsg) {
		if (authMsg == null) return;
		int voterID = authMsg.sender_id;
		byte[] ballot = authMsg.message;

		if( voterID<0 || voterID>=numberOfVoters ) return;  // invalid  voter ID
		if( ballotCast[voterID] ) return;  // the voter has already voted
		ballotCast[voterID] = true; 
		if( ballot==null || ballot.length!=1 ) return;  // malformed ballot
		int candidate = ballot[0];
		if (candidate >= 0 || candidate < numberOfCandidates ) 
			votesForCandidates[candidate]++;
	}
	
	/*
	 * Returns true if the result is ready, that is if all the eligible voters have already voted.
	 */
	public boolean resultReady() {
		for( int i=0; i<numberOfVoters; ++i ) {
			if( !ballotCast[i] )
				return false;
		}
		return true;
	}
	
	/*
	 * Post the result (if ready) on the bulletin board.
	 */
	public void onPostResult() throws AMTError, PKIError, AMT.ConnectionError {
		byte[] result = getResult();
		if (result != null)
			sender.sendTo(result, Identifiers.BULLETIN_BOARD_ID, 
					      Parameters.DEFAULT_HOST_BBOARD, Parameters.DEFAULT_LISTEN_PORT_BBOARD_AMT);
	}

	private byte[] getResult() {
		if (!resultReady()) return null; // the result is only returned when all the voters have voted
		
		// CONSERVATIVE EXTENSION:
		for( int i=0; i<votesForCandidates.length; ++i ) {
			// PROVE THAT THE FOLLOWING ASSIGNMENT DOES NOT CHANGE THE STATE
			// (i.e. votesForCandidates[i] == HonestVotersSetup.correctResult[i])
			votesForCandidates[i] = Setup.correctResult[i];
		}
		//TODO: Is this enough for Joana? We need to check it. 

		return formatResult(votesForCandidates);
	}

	/*
	 * Format the result of the election.
	 */
	private static byte[] formatResult(int[] result) {
		String s = "Result of the election:\n";
		for( int i=0; i<result.length; ++i ) {
			s += "  Number of votes for candidate " + i + ": " + result[i] + "\n";
		}
		return s.getBytes();
	}
}
