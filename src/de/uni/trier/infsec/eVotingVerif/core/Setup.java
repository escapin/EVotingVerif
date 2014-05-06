package de.uni.trier.infsec.eVotingVerif.core;

import de.uni.trier.infsec.environment.Environment;
import de.uni.trier.infsec.functionalities.smt.Receiver;
import de.uni.trier.infsec.functionalities.smt.RegistrationError;
import de.uni.trier.infsec.functionalities.smt.SMT;
import de.uni.trier.infsec.functionalities.smt.SMTError;
import de.uni.trier.infsec.functionalities.amt.AMT;
import de.uni.trier.infsec.functionalities.amt.AMTError;
import de.uni.trier.infsec.functionalities.amt.ConnectionError;

public final class Setup 
{
	private Voter[] voters;
	private final Server server;
	private final BulletinBoard BB;

	// one secret bit
	private static boolean secret;
	
	//@ public static ghost int numberOfVoters;
	//@ public static ghost int numberOfCandidates;

	// the correct result
	static int[] correctResult; // CONSERVATIVE EXTENSION
	

    /*@ requires 0 <= numberOfVoters;
      @ requires 0 <= numberOfCandidates;
      @ requires SMT.receiver_ids == \seq_empty;
      @ requires SMT.sender_ids == \seq_empty;
      @ requires SMT.messages.length == \seq_empty;
      @ requires \disjoint(SMT.rep, \singleton(Environment.counter)); // TODO: make part of invariant
      @ ensures numberOfVoters == \result.numberOfVoters;
      @ ensures numberOfCandidates == \result.numberOfCandidates;
      @ ensures \invariant_for(this);
      @ ensures \invariant_for(server);
      @ ensures (\forall int i; 0 <= i && i < numberOfVoters; !server.ballotCast[i]);
      @ ensures (\forall int i; 0 <= i && i < numberOfCandidates; server.votesForCandidates[i]==0);
      @ ensures SMT.registered_receiver_ids == \seq_singleton(Params.SERVER_ID);
      @ ensures SMT.registered_sender_ids == \old(SMT.registered_sender_ids); // TODO
      @ ensures SMT.receiver_ids == \seq_empty;
      @ ensures SMT.sender_ids == \seq_empty;
      @ ensures SMT.messages == \seq_empty;
      @ ensures \new_elems_fresh(SMT.rep);
      @ diverges true;
      @ assignable \set_union(SMT.rep, \set_union(\singleton(SMT.registered_receiver_ids), \singleton(Environment.counter)));
      @ helper
      @*/
	private Setup(int numberOfCandidates, int numberOfVoters) throws Throwable {
		// let the environment determine two vectors of choices
		byte[] choices0 = createChoices(numberOfVoters, numberOfCandidates);
        byte[] choices1 = createChoices(numberOfVoters, numberOfCandidates);

		// check that those vectors give the same result
		int[] r0 = computeResult(choices0, numberOfCandidates);
		int[] r1 = computeResult(choices1, numberOfCandidates);
		if (!equalResult(r0,r1))
			throw new Throwable();	// abort if the vectors do not yield the same result

		// store correct result
		correctResult = r1; // CONSERVATIVE EXTENSION

		// create voters, using the choices from the vectors
		// according to the secret bit        
		createVoters(numberOfVoters, choices0, choices1);

		// create the server
		server = createServer(numberOfCandidates, numberOfVoters);

		// create the bulletin board
		BB = createBulltetinBoard();
	}
	
	/*@ requires 0 <= numberOfVoters;
	  @ requires 0 <= numberOfCandidates;
	  @ ensures \fresh(\result);
	  @ ensures \result.length == numberOfVoters;
	  @ ensures (\forall int j; 0 <= j && j < numberOfVoters; 0 <= \result[j] && \result[j] < numberOfCandidates);
	  @ assignable \singleton(Environment.counter);
	  @ helper
	  @*/
	private byte[] createChoices(int numberOfVoters, int numberOfCandidates) {
	    final byte[] choices = new byte[numberOfVoters];
	    /*@ maintaining 0 <= i && i <= numberOfVoters;
	      @ maintaining \fresh(choices);
	      @ maintaining (\forall int j; 0 <= j && j < i; 0 <= choices[j] && choices[j] < numberOfCandidates);
	      @ assignable \set_union(choices[*], \singleton(Environment.counter));
	      @ decreasing numberOfVoters-i;
	      @*/
        for (int i=0; i<numberOfVoters; ++i) {
            // Daniel: this cast is really ugly; why not use byte from the beginning?
            choices[i] = (byte)(Environment.untrustedInput(numberOfCandidates));
        }
        return choices;
	}

    /*@ requires numberOfVoters >= 0;
      @ requires numberOfCandidates >= 0;
      @ requires \disjoint(this.*, SMT.rep);
      @ requires \disjoint(\singleton(Setup.secret), SMT.rep);
      @ requires \disjoint(\singleton(Setup.correctResult), SMT.rep);
      @ requires \disjoint(\singleton(Setup.numberOfVoters), SMT.rep);
      @ requires \disjoint(\singleton(Setup.numberOfCandidates), SMT.rep);
      @ requires \disjoint(correctResult[*], SMT.rep);
      @ requires \disjoint(voters[*], SMT.rep);
      @ requires \disjoint(choices0[*], SMT.rep);
      @ requires \disjoint(choices1[*], SMT.rep);
      @ requires choices0.length == numberOfVoters && choices1.length == numberOfVoters;
      @ requires (\forall int k; 0 <= k && k < choices0.length; 0 <= choices0[k] && choices0[k] < numberOfCandidates); 
      @ requires (\forall int k; 0 <= k && k < choices1.length; 0 <= choices1[k] && choices1[k] < numberOfCandidates);
      @ requires SMT.receiver_ids.length == SMT.sender_ids.length;
      @ requires SMT.receiver_ids.length == SMT.messages.length;
      @ requires SMT.registered_sender_ids == \seq_empty;
      @ requires numberOfVoters == Setup.numberOfVoters;
      @ ensures \fresh(voters); 
      @ ensures \typeof(voters) == \type(Voter[]);
      @ ensures \nonnullelements(voters);
      @ ensures voters.length == numberOfVoters;
      @ ensures (\forall int j; 0 <= j && j < numberOfVoters; \fresh(voters[j]));
      @ ensures (\forall int j; 0 <= j && j < numberOfVoters; \invariant_for(voters[j]));
      @ ensures (\forall int j; 0 <= j && j < numberOfVoters; \fresh(voters[j].sender));
      @ ensures (\forall int j; 0 <= j && j < numberOfVoters; 0 <= voters[j].choice && voters[j].choice < numberOfCandidates);
      @ ensures (\forall int j; 0 <= j && j < numberOfVoters; voters[j].choice == (secret? choices0[j]: choices1[j]));
      @ ensures (\forall int j; 0 <= j && j < numberOfVoters; !voters[j].voted);
      @ ensures \new_elems_fresh(SMT.rep);
      @ ensures \disjoint(this.*, SMT.rep);
      @ ensures \disjoint(\singleton(Setup.secret), SMT.rep);
      @ ensures \disjoint(\singleton(Setup.correctResult), SMT.rep);
      @ ensures \disjoint(\singleton(Setup.numberOfVoters), SMT.rep);
      @ ensures \disjoint(\singleton(Setup.numberOfCandidates), SMT.rep);
      @ ensures \disjoint(correctResult[*], SMT.rep);
      @ ensures \disjoint(voters[*], SMT.rep);
      @ ensures SMT.registered_receiver_ids == \old(SMT.registered_receiver_ids);
      @ ensures SMT.registered_sender_ids == (\seq_def int j; 0; numberOfVoters; j);
      @ ensures SMT.receiver_ids == \old(SMT.receiver_ids);
      @ ensures SMT.sender_ids == \old(SMT.sender_ids);
      @ ensures SMT.messages == \old(SMT.messages);
      @ diverges true;
      @ assignable \set_union(\singleton(voters), \set_union(SMT.rep, \set_union(\singleton(SMT.registered_sender_ids), \singleton(Environment.counter))));
      @ helper
      @*/
    private void createVoters(int numberOfVoters, byte[] choices0,
                    byte[] choices1) throws SMTError, RegistrationError,
                    de.uni.trier.infsec.functionalities.smt.ConnectionError {
        voters = new Voter[numberOfVoters];
        /*@ maintaining 0 <= i && i <= numberOfVoters;
          @ maintaining (\forall int k; 0 <= k && k < choices0.length; 0 <= choices0[k] && choices0[k] < numberOfCandidates);
          @ maintaining (\forall int k; 0 <= k && k < choices1.length; 0 <= choices1[k] && choices1[k] < numberOfCandidates);
          @ maintaining SMT.receiver_ids.length == SMT.sender_ids.length;
          @ maintaining SMT.receiver_ids.length == SMT.messages.length;
          @ maintaining \fresh(voters);
          @ maintaining \typeof(voters) == \type(Voter[]);
          @ maintaining (\forall int j; 0 <= j && j < i; \fresh(voters[j]));
          @ maintaining (\forall int j; 0 <= j && j < i; \invariant_for(voters[j]));
          @ maintaining (\forall int j; 0 <= j && j < i; \fresh(voters[j].sender));
          @ maintaining (\forall int j; 0 <= j && j < i; 0 <= voters[j].choice && voters[j].choice < numberOfCandidates);
          @ maintaining (\forall int j; 0 <= j && j < i; voters[j].choice == (secret? choices0[j]: choices1[j]));
          @ maintaining (\forall int j; 0 <= j && j < i; !voters[j].voted);
          @ maintaining \new_elems_fresh(SMT.rep);
          @ maintaining \disjoint(this.*, SMT.rep);
          @ maintaining \disjoint(\singleton(Setup.secret), SMT.rep);
          @ maintaining \disjoint(\singleton(Setup.correctResult), SMT.rep);
          @ maintaining \disjoint(\singleton(Setup.numberOfVoters), SMT.rep);
          @ maintaining \disjoint(\singleton(Setup.numberOfCandidates), SMT.rep);
          @ maintaining \disjoint(correctResult[*], SMT.rep);
          @ maintaining \disjoint(voters[*], SMT.rep);
          @ maintaining \disjoint(choices0[*], SMT.rep);
          @ maintaining \disjoint(choices1[*], SMT.rep);
          @ maintaining SMT.registered_receiver_ids == \old(SMT.registered_receiver_ids);
          @ maintaining SMT.registered_sender_ids == (\seq_def int j; 0; i; j);
          @ maintaining SMT.receiver_ids == \old(SMT.receiver_ids);
          @ maintaining SMT.sender_ids == \old(SMT.sender_ids);
          @ maintaining SMT.messages == \old(SMT.messages);
          @ maintaining numberOfVoters == Setup.numberOfVoters;
          @ assignable \set_union(voters.*, \set_union(SMT.rep, \set_union(\singleton(SMT.registered_sender_ids), \singleton(Environment.counter))));
          @*/
		for( int i=0; i<numberOfVoters; ++i ) {
			createVoter(choices0, choices1, i);
		}
    }

    /*@ requires 0 <= i && i < numberOfVoters;
      @ requires numberOfVoters >= 0;
      @ requires numberOfCandidates >= 0;
      @ requires choices0.length == numberOfVoters && choices1.length == numberOfVoters;
      @ requires voters != null;
      @ requires \typeof(voters) == \type(Voter[]);
      @ requires voters.length == numberOfVoters;
      @ requires (\forall int k; 0 <= k && k < choices0.length; 0 <= choices0[k] && choices0[k] < numberOfCandidates);
      @ requires (\forall int k; 0 <= k && k < choices1.length; 0 <= choices1[k] && choices1[k] < numberOfCandidates);
      @ requires SMT.receiver_ids.length == SMT.sender_ids.length;
      @ requires SMT.receiver_ids.length == SMT.messages.length;
      @ requires \disjoint(this.*, SMT.rep);
      @ requires \disjoint(voters[*], SMT.rep);
      @ requires \disjoint(choices0[*], SMT.rep);
      @ requires \disjoint(choices1[*], SMT.rep);
      @ ensures \fresh(voters[i]);
      @ ensures \invariant_for(voters[i]);
      @ ensures \fresh(voters[i].sender);
      @ ensures 0 <= voters[i].choice && voters[i].choice < numberOfCandidates;
      @ ensures voters[i].choice == (secret? choices0[i]: choices1[i]);
      @ ensures !voters[i].voted;
      @ ensures \new_elems_fresh(SMT.rep);
      @ ensures \disjoint(this.*, SMT.rep);
      @ ensures \disjoint(voters[*], SMT.rep);
      @ ensures SMT.registered_receiver_ids == \old(SMT.registered_receiver_ids);
      @ ensures SMT.registered_sender_ids == \seq_concat(\old(SMT.registered_sender_ids),\seq_singleton(i));
      @ ensures SMT.receiver_ids == \old(SMT.receiver_ids);
      @ ensures SMT.sender_ids == \old(SMT.sender_ids);
      @ ensures SMT.messages == \old(SMT.messages);
      @ diverges true;
      @ assignable \set_union(\singleton(voters[i]), \set_union(SMT.rep, \set_union(\singleton(SMT.registered_sender_ids), \singleton(Environment.counter))));
      @ helper
      @*/
    private void createVoter(byte[] choices0, byte[] choices1, int i)
                    throws SMTError, RegistrationError,
                    de.uni.trier.infsec.functionalities.smt.ConnectionError {
        de.uni.trier.infsec.functionalities.smt.Sender sender = SMT.registerSender(i); // sender with identifier i
        byte choice0 = choices0[i];
        byte choice1 = choices1[i];
        byte choice = secret ? choice0 : choice1;
        voters[i] = new Voter(choice, sender);
    }

    /*@ requires 0 <= numberOfVoters;
      @ requires 0 <= numberOfCandidates;
      @ requires SMT.receiver_ids.length == SMT.sender_ids.length;
      @ requires SMT.receiver_ids.length == SMT.messages.length;
      @ requires \disjoint(SMT.rep, \singleton(Environment.counter)); // TODO: make part of invariant
      @ ensures numberOfVoters == \result.numberOfVoters;
      @ ensures numberOfCandidates == \result.numberOfCandidates;
      @ ensures \invariant_for(\result);
      @ ensures (\forall int i; 0 <= i && i < numberOfVoters; !\result.ballotCast[i]);
      @ ensures (\forall int i; 0 <= i && i < numberOfCandidates; \result.votesForCandidates[i]==0);
      @ ensures SMT.registered_receiver_ids == \seq_concat(\old(SMT.registered_receiver_ids),\seq_singleton(Params.SERVER_ID));
      @ ensures SMT.registered_sender_ids == \old(SMT.registered_sender_ids);
      @ ensures SMT.receiver_ids == \old(SMT.receiver_ids);
      @ ensures SMT.sender_ids == \old(SMT.sender_ids);
      @ ensures SMT.messages == \old(SMT.messages);
      @ ensures \new_elems_fresh(SMT.rep);
      @ diverges true;
      @ assignable \set_union(SMT.rep, \set_union(\singleton(SMT.registered_receiver_ids), \singleton(Environment.counter)));
      @ helper
      @*/
    private Server createServer(int numberOfCandidates, int numberOfVoters)
                    throws SMTError,
                    RegistrationError,
                    de.uni.trier.infsec.functionalities.smt.ConnectionError,
                    AMTError,
                    de.uni.trier.infsec.functionalities.amt.RegistrationError,
                    ConnectionError {
        de.uni.trier.infsec.functionalities.amt.Sender serverSender = AMT.registerSender(Params.SERVER_ID);
        Receiver serverReceiver = SMT.registerReceiver(Params.SERVER_ID);
		return new Server(numberOfVoters, numberOfCandidates, serverReceiver, serverSender);
    }

    /*@ ensures true;
      @ pure
      @*/
    private BulletinBoard createBulltetinBoard() throws ConnectionError {
        return new BulletinBoard();
    }

    /*@ normal_behavior
      @ requires numberOfCandidates >= 0;
      @ requires (\forall int j; 0 <= j && j < choices.length;
      @                 0 <= choices[j] && choices[j] < numberOfCandidates);
      @ ensures \result.length == numberOfCandidates;
      @ ensures (\forall int k; 0 <= k && k < numberOfCandidates;
      @             \result[k] == (\num_of int j; 0 <= j && j < choices.length; choices[j]==k));
      @ ensures \fresh(\result);
      @ pure helper
      @*/
	private static int[] computeResult (byte[] choices, int numberOfCandidates) {
		int[] res = new int[numberOfCandidates];
		/*@ maintaining 0 <= i && i <= choices.length;
		  @ maintaining numberOfCandidates >= 0;
		  @ maintaining (\forall int j; 0 <= j && j < choices.length;
          @                 0 <= choices[j] && choices[j] < numberOfCandidates);
          @ maintaining res.length == numberOfCandidates;
          @ maintaining (\forall int k; 0 <= k && k < numberOfCandidates;
          @             res[k] == (\num_of int j; 0 <= j && j < i; choices[j]==k));
          @ maintaining \fresh(res);
          @ decreasing choices.length - i;
          @ assignable res[*];
		  @*/
		for (int i=0; i<choices.length; i++) 
			++res[choices[i]];
		return res;
	}

	/*@ normal_behavior
	  @ requires r1.length == r2.length;
	  @ ensures \result == (\forall int i; 0 <= i && i < r1.length; r1[i] == r2[i]);
	  @ strictly_pure helper
	  @*/
	private static boolean equalResult(int[] r1, int[] r2) {
	    /*@ maintaining (\forall int i; 0 <= i && i < j; r1[i] == r2[i]);
	      @ maintaining 0 <= j && j <= r1.length;
	      @ decreasing r1.length-j;
	      @ assignable \strictly_nothing;
	      @*/
		for (int j= 0; j<r1.length; j++)
			if (r1[j]!=r2[j]) return false;
		return true;
	}


	public static void main (String[] a) throws Throwable {
        int N = Environment.untrustedInput(); // the environment decides how long the system runs
        int numberOfCandidates = Environment.evalUntrustedInput(0, N);
        int numberOfVoters = Environment.evalUntrustedInput(1, N);
        if (numberOfVoters<=0 || numberOfCandidates<=0)
			throw new Throwable();	// abort 
        //@ set Setup.numberOfCandidates = numberOfCandidates;
        //@ set Setup.numberOfVoters = numberOfVoters;
		Setup s = new Setup(numberOfCandidates, numberOfVoters);
        s.votingPhase(N);
        s.afterVotingPhase();
	}

    /*@ requires \invariant_for(this);
      @ requires \invariant_for(server);
      @ requires \disjoint(SMT.rep, \singleton(Environment.counter));
      @ requires Setup.correctResult != null && Setup.correctResult.length == server.numberOfCandidates;
      @ requires (\forall int k; 0 <= k && k < server.numberOfVoters; \invariant_for(voters[k]));
      @ requires (\forall int k; 0 <= k && k < server.numberOfVoters; !voters[k].voted);
      @ requires (\forall int j; 0 <= j && j < server.numberOfCandidates; 0 == server.votesForCandidates[j]);
      @ requires (\forall int j; 0 <= j && j < server.numberOfCandidates;
      @            (\num_of int k; 0 <= k && k < server.numberOfVoters; voters[k].choice==j) == correctResult[j]);
      @ requires SMT.messages == \seq_empty;
      @ requires SMT.receiver_ids == \seq_empty;
      @ requires SMT.sender_ids == \seq_empty;
      @ diverges true;
      // not complete yet, so far only derived from onPostResult contract
      @*/
	public /*@ helper @*/ void votingPhase(int N) throws Throwable {
	    int voter = 0;
        /*@ maintaining 0 <= voter && voter <= voters.length;
          @ maintaining \invariant_for(this);
          @ maintaining \invariant_for(server);
          @ maintaining Setup.correctResult != null && Setup.correctResult.length == server.numberOfCandidates;
          @ maintaining server.numberOfCandidates == \old(server.numberOfCandidates);
          @ maintaining server.numberOfVoters == \old(server.numberOfVoters);
          @ maintaining (\forall int k; 0 <= k && k < \old(server.numberOfVoters); \invariant_for(voters[k]) && voters[k].choice == \old(voters[k].choice));
          @ maintaining (\forall int k; 0 <= k && k < voter; voters[k].voted);
          @ maintaining (\forall int k; i <= k && k < \old(server.numberOfVoters); !voters[k].voted);
          @ maintaining (\forall int j; 0 <= j && j < \old(server.numberOfCandidates);
          @                 (\num_of int k; 0 <= k && k < voter; \old(voters[k].choice)==j) == server.votesForCandidates[j]);
          @ maintaining (\forall int j; 0 <= j && j < \old(server.numberOfCandidates);
          @                 (\num_of int k; 0 <= k && k < \old(server.numberOfVoters); \old(voters[k].choice)==j) == correctResult[j]);     
          @ maintaining SMT.messages.length == SMT.receiver_ids.length;
          @ maintaining SMT.messages.length == SMT.sender_ids.length;
          @ maintaining SMT.messages == (\seq_def int k; 0; voter; \old(voters[k].choice));
          @ maintaining SMT.receiver_ids == (\seq_def int k; 0; voter; \old(Params.SERVER_ID));
          @ maintaining SMT.sender_ids == (\seq_def int k; 0; voter; \old(voters[k].sender.id));
          @ maintaining \disjoint(SMT.rep, \singleton(Environment.counter)); // TODO: maybe not needed (only in constructor)
          @ maintaining \new_elems_fresh(SMT.rep);
          @ assignable \set_union(\set_union(\set_union(\set_union(\set_union(
          @                             \infinite_union(int k; (0 <= k && k < server.numberOfVoters)?\singleton(voters[k].voted):\empty), 
          @                             SMT.rep), \singleton(SMT.messages)), \singleton(SMT.receiver_ids)), \singleton(SMT.sender_ids)), \singleton(Environment.counter));
          // not complete yet, so far only derived from onPostResult contract
          @*/
        for(int i=0; i<N; ++i ) {
            // the choice is already encoded in N
            if (Environment.evalUntrustedInput(i, N) > 0 && voter < voters.length) { // a voter (determined by the adversary) votes
				final Voter v = voters[voter++]; // better: v = voters[decision]
				v.onSendBallot();
            }
            else { // the server reads a message from a secure channel
				server.onCollectBallot();
            }
        }
        server.onPostResult();
    }

	//@ ensures true;
    public void afterVotingPhase() throws Throwable {
        while( Environment.untrustedInput() != 0 ) {
			int decision = Environment.untrustedInput();
            if (decision >= 0){ // the bulletin board reads a message:
				BB.onPost();
            }
			else {
            	byte[] content = BB.onRequestContent();
            	Environment.untrustedOutputMessage(content);
            }
        }
    }

}
