package de.uni.trier.infsec.functionalities.smt;

import de.uni.trier.infsec.environment.*;
import de.uni.trier.infsec.functionalities.smt.SMT.ConnectionError;
import de.uni.trier.infsec.functionalities.smt.SMT.SMTError;
import de.uni.trier.infsec.utils.MessageTools;

final public class Receiver {
	public final int id;
	/*@ invariant 
	  @ (\exists int i; 0 <= i && i < SMT.registered_receiver_ids.length; (int)SMT.registered_receiver_ids[i]==id);
	  @ invariant 
	  @ (\forall Receiver r; r.id == id; r == this);
	  @ invariant \disjoint(SMT.rep, \singleton(this.id));
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
      @ ensures \result==null || (\exists int i; 0 <= i && i < SMT.messages.length;
	  @	       \result.message[0] == (byte)SMT.messages[i]
	  @	       && (int)SMT.receiver_ids[i] == id && (int)SMT.sender_ids[i] == \result.sender_id);
	  @ ensures \result==null || (\fresh(\result) && \invariant_for(\result));
	  @ ensures \result==null || \disjoint(SMT.rep, \result.*);
  	  @ ensures \new_elems_fresh(SMT.rep);
      @ diverges true;
	  @ assignable SMT.rep, Environment.counter;
	  @*/
	public /*@ nullable @*/ AuthenticatedMessage getMessage(int port) throws SMTError {
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