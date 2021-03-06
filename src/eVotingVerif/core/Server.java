package eVotingVerif.core;

import funct.amt.AMT;
import funct.amt.AMT.AMTError;
import funct.smt.AuthenticatedMessage;
import funct.smt.Receiver;
import funct.smt.SMT;
import funct.smt.SMT.SMTError;

public class Server {
	private final int numberOfVoters;
    private final int numberOfCandidates;
	private final boolean[] ballotCast;  // ballotCast[i]==true iff the i-th voter has already cast her ballot
	private final int[] votesForCandidates;
	private final Receiver receiver;
	private final AMT.Sender sender;

	public Server(int numberOfVoters, int numberOfCandidates, 
			      Receiver receiver, AMT.Sender sender_to_BB) throws AMTError, SMT.ConnectionError {
		this.numberOfVoters = numberOfVoters;
		this.numberOfCandidates = numberOfCandidates;
		this.receiver = receiver;
		this.sender = sender_to_BB;
		votesForCandidates = new int[numberOfCandidates];		
		ballotCast = new boolean[numberOfVoters]; // initially no voter has cast her ballot
		receiver.listenOn(Params.LISTEN_PORT_SERVER_SMT);
	}

	/*
	 * Collect one ballot (read from a secure channel)
	 */
	int i=0;
	public void onCollectBallot() throws SMTError {
		AuthenticatedMessage authMsg = receiver.getMessage(Params.LISTEN_PORT_SERVER_SMT);
		//System.out.println(++i);
		onCollectBallot(authMsg);
	}
	
	private void onCollectBallot(AuthenticatedMessage authMsg) {
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
	public void onPostResult() throws AMTError, AMT.RegistrationError, AMT.ConnectionError {
		byte[] result = getResult();
		if (result != null)
			sender.sendTo(result, Params.BULLETIN_BOARD_ID, 
					      Params.DEFAULT_HOST_BBOARD, Params.LISTEN_PORT_BBOARD_AMT);		
	}

	private byte[] getResult() {
		if (!resultReady()) return null; // the result is only returned when all the voters have voted
		
//		// CONSERVATIVE EXTENSION:
//		for( int i=0; i<votesForCandidates.length; ++i ) {
//			// PROVE THAT THE FOLLOWING ASSIGNMENT DOES NOT CHANGE THE STATE
//			// (i.e. votesForCandidates[i] == HonestVotersSetup.correctResult[i])
//			votesForCandidates[i] = Setup.correctResult[i];
//		}
//		//TODO: Is this enough for Joana? We need to check it. 

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
