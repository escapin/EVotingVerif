package de.uni.trier.infsec.functionalities.smt;

import de.uni.trier.infsec.eVotingVerif.core.Server;
import de.uni.trier.infsec.environment.*;
import de.uni.trier.infsec.utils.MessageTools;

final public class Receiver {
	public final int id;
	//@ public ghost nullable Server server;
	
	/*@ invariant 
	  @ (\exists int i; 0 <= i && i < SMT.registered_receiver_ids.length; (int)SMT.registered_receiver_ids[i]==id);
	  @ invariant 
	  @ (\forall Receiver r; r.id == id; r == this);
	  @ invariant \disjoint(SMT.rep, this.*);
	  @ accessible \inv: \set_union(SMT.rep, this.*);
	  @*/

	/*@ ensures true;
      @ diverges true;
	  @ assignable Environment.counter;
	  @*/
	public void listenOn(int port) throws ConnectionError {
		boolean ok = SMTEnv.listenOn(port);
		if (!ok) throw new ConnectionError();
	}

	/*@ 
      @ requires SMT.messages.length == SMT.receiver_ids.length;
      @ requires SMT.messages.length == SMT.sender_ids.length;
      @ ensures (\exists int i; 0 <= i && i < SMT.messages.length;
	  @	       \result.message[0] == (byte)SMT.messages[i]
	  @	       && (int)SMT.receiver_ids[i] == id && (int)SMT.sender_ids[i] == \result.sender_id);
	  @ ensures \fresh(\result) && \invariant_for(\result);
	  @ ensures \disjoint(SMT.rep, \result.*);
  	  @ ensures \new_elems_fresh(SMT.rep);
      @ ensures 0 <= \result.sender_id && \result.sender_id < server.numberOfVoters;
      @ ensures \result.message != null;
      @ ensures \result.message.length == 1;
      @ ensures 0 <= \result.message[0] && \result.message[0] < server.numberOfCandidates;
      @ diverges true;
	  @ assignable \set_union(SMT.rep, \singleton(Environment.counter));
	  @*/
	public AuthenticatedMessage getMessage(int port) throws SMTError {
		if (SMT.registrationInProgress) throw new SMTError();			

		// the simulator/environment determines the index of the message to be returned
		int index = SMTEnv.getMessage(this.id, port);
		if (index < 0) return null;
		LogEntry smtmsg = SMT.log.get(index);
		if (smtmsg == null) return null;
		// check whether the message was sent to *this* receiver
		if (smtmsg.receiver_id != id) return null;
		// return new authenticated message
		return new AuthenticatedMessage(MessageTools.copyOf(smtmsg.message), smtmsg.sender_id);
	}

	Receiver(int id)  {
		this.id = id;
	}
}