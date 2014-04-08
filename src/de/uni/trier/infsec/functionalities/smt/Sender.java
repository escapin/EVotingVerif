package de.uni.trier.infsec.functionalities.smt;

import de.uni.trier.infsec.environment.SMTEnv;
import de.uni.trier.infsec.functionalities.smt.SMT.ConnectionError;
import de.uni.trier.infsec.functionalities.smt.SMT.RegistrationError;
import de.uni.trier.infsec.functionalities.smt.SMT.SMTError;
import de.uni.trier.infsec.lib.network.NetworkClient;
import de.uni.trier.infsec.lib.network.NetworkError;
import de.uni.trier.infsec.utils.MessageTools;

final public class Sender 
{
	/*@ invariant 
	  @ (\exists int i; 0 <= i && i < registered_sender_ids.length; (int)registered_sender_ids[i]==id);
	  @ invariant 
	  @ (\forall Sender s; s.id == id; s == this);
	  @ invariant \disjoint(SMT.rep, \singleton(this.id));
	  @*/
	public final int id;

	/*@ behavior // the following must be true if no exception is thrown
	  @ requires message.length > 0;
	  @ ensures messages == \seq_concat(\old(messages),\seq_singleton(message[0]));
	  @ ensures receiver_ids == \seq_concat(\old(receiver_ids),\seq_singleton(receiver_id));
	  @ ensures sender_ids == \seq_concat(\old(sender_ids),\seq_singleton(id));
	  @ ensures (\exists int i; 0 <= i && i < registered_receiver_ids.length; registered_receiver_ids[i]==receiver_id);
  	  @ ensures \new_elems_fresh(SMT.rep);
	  @ assignable SMT.rep, messages, receiver_ids, sender_ids, Environment.counter; // what can be changed
	  @*/
	public void sendTo(/*@nullable@*/ byte[] message, int receiver_id, /*@ nullable @*/ String server, int port) throws SMTError, RegistrationError, ConnectionError {
		if (SMT.registrationInProgress) throw new SMTError();

		// get from the simulator a message to be later sent out
		byte[] output_message = SMTEnv.sendTo(message.length, id, receiver_id, server, port);
		if (output_message == null) throw new ConnectionError();
		// get the answer from PKI
		if (!SMT.registeredReceivers.exists(receiver_id))
			throw new RegistrationError();
		// log the sent message along with the sender and receiver identifiers			
		SMT.log.add(new LogEntry(MessageTools.copyOf(message), id, receiver_id));
	  	//@ set messages = \seq_concat(messages,\seq_singleton(message[0]));
		//@ set receiver_ids = \seq_concat(receiver_ids,\seq_singleton(receiver_id));
		//@ set sender_ids = \seq_concat(sender_ids,\seq_singleton(id));

		// sent out the message from the simulator
		try {
			NetworkClient.send(output_message, server, port);
		}
		catch( NetworkError e ) {
			throw new ConnectionError();
		}
	}

	Sender(int id) {
		this.id = id;
	}
}