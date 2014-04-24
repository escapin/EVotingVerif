package de.uni.trier.infsec.eVotingVerif.core;

import de.uni.trier.infsec.environment.Environment;
import de.uni.trier.infsec.functionalities.smt.AuthenticatedMessage;
import de.uni.trier.infsec.functionalities.smt.SMT;
import de.uni.trier.infsec.functionalities.smt.Receiver;
import de.uni.trier.infsec.functionalities.smt.SMTError;
import de.uni.trier.infsec.functionalities.amt.AMTError;
import de.uni.trier.infsec.functionalities.amt.RegistrationError;
import de.uni.trier.infsec.functionalities.amt.Sender;

public final class Server {
	private /*@ spec_public @*/ final int numberOfVoters;
    private /*@ spec_public @*/ final int numberOfCandidates;
	private /*@ spec_public @*/ final boolean[] ballotCast;  // ballotCast[i]==true iff the i-th voter has already cast her ballot
	private /*@ spec_public @*/ final int[] votesForCandidates;
	private /*@ spec_public @*/ final Receiver receiver;
	private /*@ spec_public @*/ final Sender sender;

	/*@ invariant \disjoint(SMT.rep, this.*, ballotCast[*], votesForCandidates[*]);
	  @ invariant numberOfVoters == ballotCast.length;
	  @ invariant numberOfCandidates == votesForCandidates.length;
	  @ invariant 0 <= numberOfVoters;
	  @ invariant 0 <= numberOfCandidates;
	  @ invariant receiver.server == this;
	  @ invariant \invariant_for(receiver);
	  @*/

	/*@ requires 0 <= numberOfVoters;
	  @ requires 0 <= numberOfCandidates;
	  @ requires \invariant_for(receiver);
	  @ requires \disjoint(SMT.rep, \singleton(Environment.counter)); // TODO: make part of invariant
	  @ ensures numberOfVoters == this.numberOfVoters;
	  @ ensures numberOfCandidates == this.numberOfCandidates;
	  @ ensures receiver == this.receiver;
	  @ ensures sender == this.sender;
	  @ ensures \invariant_for(this);
	  @ ensures (\forall int i; 0 <= i && i < numberOfVoters; !ballotCast[i]);
	  @ ensures (\forall int i; 0 <= i && i < numberOfCandidates; votesForCandidates[i]==0);
	  @ diverges true;
	  @ signals_only Error, RuntimeException, AMTError, de.uni.trier.infsec.functionalities.smt.ConnectionError;
	  @ assignable Environment.counter, receiver.server;
	  @ helper
	  @*/
	public Server(int numberOfVoters, int numberOfCandidates, 
			      Receiver receiver, Sender sender_to_BB) throws AMTError, de.uni.trier.infsec.functionalities.smt.ConnectionError {
		this.numberOfVoters = numberOfVoters;
		this.numberOfCandidates = numberOfCandidates;
		this.receiver = receiver;
		//@ set receiver.server = this;
		this.sender = sender_to_BB;
		votesForCandidates = new int[numberOfCandidates];		
		ballotCast = new boolean[numberOfVoters]; // initially no voter has cast her ballot
		receiver.listenOn(Params.LISTEN_PORT_SERVER_SMT);
	}

	/**
	 * Collect one ballot (read from a secure channel)
	 */
	public void onCollectBallot() throws SMTError {
		AuthenticatedMessage authMsg = receiver.getMessage(Params.LISTEN_PORT_SERVER_SMT);
		if (authMsg != null)
            onCollectBallot(authMsg);
	}
	
	/*@ requires \invariant_for(this);
	  @ requires 0 <= authMsg.sender_id && authMsg.sender_id < numberOfVoters;
	  @ requires !ballotCast[authMsg.sender_id];
	  @ requires \invariant_for(authMsg);
	  @ requires authMsg.message != null;
	  @ requires authMsg.message.length == 1;
	  @ requires 0 <= authMsg.message[0] && authMsg.message[0] < numberOfCandidates;
	  @	ensures votesForCandidates[authMsg.message[0]] == \old(votesForCandidates[authMsg.message[0]])+1;
	  @ ensures (\forall int i; 0 <= i && i < numberOfCandidates; i != authMsg.message[0] ==>
	  @		   votesForCandidates[i] == \old(votesForCandidates[i]));
	  @ ensures ballotCast[authMsg.sender_id];
	  @ ensures (\forall int j; 0 <= j && j < numberOfCandidates; j != authMsg.sender_id ==>
	  @        ballotCast[j] == \old(ballotCast[j]));
	  @ ensures \invariant_for(this);
      @ diverges true;
	  @ assignable votesForCandidates[*], ballotCast[*];
      @*/
	private /*@ helper @*/ void onCollectBallot(AuthenticatedMessage authMsg) {
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
	/*@ normal_behavior
	  @ ensures \result ==
	  @	(\forall int j; 0 <= j && j < numberOfVoters; ballotCast[j]);
	  @ strictly_pure
	  @*/
	public boolean resultReady() {
	    /*@ maintaining 0 <= i && i <= numberOfVoters;
	      @ maintaining \invariant_for(this);
	      @ maintaining (\forall int j; 0 <= j && j < i; ballotCast[j]);
	      @ decreasing numberOfVoters-i;
	      @ assignable \strictly_nothing;
	      @*/
		for( int i=0; i<numberOfVoters; ++i ) {
			if( !ballotCast[i] )
				return false;
		}
		return true;
	}
	
	/**
	 * Post the result (if ready) on the bulletin board.
	 */
	/*@ requires \invariant_for(this);
	  @ requires (\forall int j; 0 <= j && j < numberOfVoters; ballotCast[j]);
      @ requires Setup.correctResult != null && Setup.correctResult.length == numberOfCandidates;
      @ requires (\forall int j; 0 <= j && j < numberOfCandidates;
      @            Setup.correctResult[j] == votesForCandidates[j]);
	  @ ensures true;
      @ diverges true;
	  @ assignable \set_union(SMT.rep, \singleton(Environment.counter));
	  @
	  @ also
	  @ requires \invariant_for(this);
	  @ requires !(\forall int j; 0 <= j && j < numberOfVoters; ballotCast[j]);
	  @ ensures true;
	  @*/
	public void /*@ helper @*/ onPostResult() throws AMTError, RegistrationError, de.uni.trier.infsec.functionalities.amt.ConnectionError {
		byte[] _result = getResult();
		if (_result != null)
			sender.sendTo(_result, Params.BULLETIN_BOARD_ID, 
					      Params.DEFAULT_HOST_BBOARD, Params.LISTEN_PORT_BBOARD_AMT);		
	}

	/*@ requires \invariant_for(this);
	  @ requires (\forall int j; 0 <= j && j < numberOfVoters; ballotCast[j]);
	  @ requires Setup.correctResult != null && Setup.correctResult.length == numberOfCandidates;
	  @ requires (\forall int j; 0 <= j && j < numberOfCandidates;
	  @            Setup.correctResult[j] == votesForCandidates[j]);
	  @ ensures \result != null;
	  @*/
	private /*@ pure helper nullable @*/ byte[] getResult() {
		if (!resultReady()) return null; // the result is only returned when all the voters have voted
		
        int[] _result = new int[numberOfCandidates];
        /*@ maintaining 0 <= i && i <= numberOfCandidates;
          @ maintaining Setup.correctResult != null;
          @ maintaining Setup.correctResult.length == numberOfCandidates;
          @ maintaining \invariant_for(this);
          @ maintaining (\forall int j; 0 <= j && j < numberOfCandidates;
          @             Setup.correctResult[j] == votesForCandidates[j]);
          @ decreasing numberOfCandidates-i;
          @ assignable _result[*];
          @*/
        for (int i=0; i<numberOfCandidates; ++i) {
            int x = votesForCandidates[i];
            // CONSERVATIVE EXTENSION:
            // PROVE THAT THE FOLLOWING ASSINGMENT IS REDUNDANT
            x = consExt(i);
            _result[i] = x;
        }
        return formatResult(_result);
	}

	/*@ normal_behavior
	  @ requires 0 <= i && i < numberOfCandidates;
	  @ requires Setup.correctResult != null;
	  @ requires Setup.correctResult.length == numberOfCandidates;
	  @ requires Setup.correctResult[i] == votesForCandidates[i];
	  @ ensures \result == votesForCandidates[i];
	  @ strictly_pure
	  @*/
    private int consExt(int i) {
        return Setup.correctResult[i];
    }

	/*
	 * Format the result of the election.
	 */
	/*@ ensures true;
	  @ pure
	  @*/
	private static byte[] formatResult(int[] _result) {
		String s = "Result of the election:\n";
		/*@ maintaining 0 <= i && i <= _result.length;
		  @ decreasing _result.length-i;
		  @ assignable \nothing;
		  @*/
		for( int i=0; i<_result.length; ++i ) {
			s += "  Number of votes for candidate " + i + ": " + _result[i] + "\n";
		}
		return s.getBytes();
	}
}
