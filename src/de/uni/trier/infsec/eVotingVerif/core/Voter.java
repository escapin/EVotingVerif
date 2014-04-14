package de.uni.trier.infsec.eVotingVerif.core;

import de.uni.trier.infsec.environment.Environment;
import de.uni.trier.infsec.functionalities.smt.*;
import de.uni.trier.infsec.functionalities.smt.SMT.*;

public final class Voter {
	private /*@ spec_public @*/ final byte choice;
	private /*@ spec_public @*/ final Sender sender;
    private /*@ spec_public @*/ boolean voted;

	//@ public invariant \invariant_for(sender);
    //@ public invariant \disjoint(SMT.rep, this.*);

	/*@ normal_behavior
	  @ requires \invariant_for(sender);
	  @ ensures this.choice == choice;
	  @ ensures this.sender == sender;
	  @ ensures !voted;
	  @ pure
	  @*/
	public Voter(byte choice, Sender sender) throws SMTError, RegistrationError, ConnectionError  {
		this.choice = choice;
		this.sender = sender; 
        this.voted = false;
	}

	/**
	 * Prepare the ballot containing the vote and send it to the server using the secure 
	 * message transfer functionality (the Sender object).
	 */
	/*@ behavior // the following must be true if no exception is thrown
	  @ requires !voted;
	  @ ensures SMT.messages == \seq_concat(\old(SMT.messages),\seq_singleton(choice));
	  @ ensures SMT.receiver_ids == \seq_concat(\old(SMT.receiver_ids),\seq_singleton(Params.SERVER_ID));
	  @ ensures SMT.sender_ids == \seq_concat(\old(SMT.sender_ids),\seq_singleton(sender.id));
	  @ ensures (\exists int i; 0 <= i && i < SMT.registered_receiver_ids.length; SMT.registered_receiver_ids[i]==Params.SERVER_ID);
	  @ ensures \new_elems_fresh(SMT.rep);
	  @ ensures voted;
      @ diverges true;
	  @ assignable \set_union(\set_union(\set_union(\set_union(\set_union(\singleton(voted), SMT.rep), \singleton(SMT.messages)), \singleton(SMT.receiver_ids)), \singleton(SMT.sender_ids)), \singleton(Environment.counter)); // what can be changed
	  @ also normal_behavior
	  @ requires voted;
      @ diverges true;
	  @ assignable \nothing;
	  @*/
	public void onSendBallot() throws RegistrationError, ConnectionError, SMTError {
        if (voted) return;
        voted = true;
		byte [] ballot = new byte[] {choice};
		sender.sendTo(ballot,  Params.SERVER_ID, Params.DEFAULT_HOST_SERVER, Params.LISTEN_PORT_SERVER_SMT);
	}
}
