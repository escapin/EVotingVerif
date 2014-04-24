package de.uni.trier.infsec.functionalities.smt;

import de.uni.trier.infsec.environment.Environment;
import de.uni.trier.infsec.environment.SMTEnv;

/**
 * Ideal functionality for SMT (Secure Authenticated Message Transmission).
 */
public final class SMT {

	//// The public interface ////

	

	// what locations belong to the SMT component, what may be changed upon sending
	//@ public static ghost \locset rep;

	// the abstract state (message queue)
	//@ public static ghost \seq receiver_ids;
	//@ public static ghost \seq messages;
	//@ public static ghost \seq sender_ids;

	//@ public static ghost \seq registered_sender_ids;
	//@ public static ghost \seq registered_receiver_ids;

	/*@ requires receiver_ids.length == sender_ids.length;
	  @ requires receiver_ids.length == messages.length;
	  @ ensures \invariant_for(\result) && \fresh(\result);
	  @ ensures \new_elems_fresh(SMT.rep);
	  @ ensures SMT.registered_sender_ids == \seq_concat(\old(SMT.registered_sender_ids),\seq_singleton(id));
      @ diverges true;
	  @ assignable \set_union(SMT.rep, \set_union(\singleton(SMT.registered_sender_ids), \singleton(Environment.counter)));
	  @*/
	public static Sender registerSender(int id) throws SMTError, RegistrationError, ConnectionError {
		if (registrationInProgress) throw new SMTError();
		registrationInProgress = true;
		// call the simulator, throw a network error if the simulator says so
		boolean network_ok = SMTEnv.registerSender(id);
		if (!network_ok) throw new ConnectionError();
		// check whether the id has not been claimed
		if( registeredSenders.exists(id) ) {
			registrationInProgress = false;
			throw new RegistrationError();
		}
		// create a new agent, add it to the list of registered agents, and return it
		registeredSenders.add(id);
		Sender sender = new Sender(id);
		registrationInProgress = false;
		return sender;
	}

    /*@ requires receiver_ids.length == sender_ids.length;
      @ requires receiver_ids.length == messages.length;
	  @ ensures \invariant_for(\result) && \fresh(\result);
	  @ ensures \new_elems_fresh(SMT.rep);
	  @ ensures SMT.registered_receiver_ids == \seq_concat(\old(SMT.registered_receiver_ids),\seq_singleton(id));
      @ diverges true;
	  @ assignable \set_union(SMT.rep, \set_union(\singleton(registered_receiver_ids), \singleton(Environment.counter)));
	  @*/
	public static Receiver registerReceiver(int id) throws SMTError, RegistrationError, ConnectionError {
		if (registrationInProgress) throw new SMTError();
		registrationInProgress = true;
		// call the simulator, throw a network error if the simulator says so
		boolean network_ok =  SMTEnv.registerReceiver(id);
		if (!network_ok) throw new ConnectionError();
		// check whether the id has not been claimed
		if( registeredReceivers.exists(id) ) {
			registrationInProgress = false;
			throw new RegistrationError();
		}
		// create a new agent, add it to the list of registered agents, and return it
		registeredReceivers.add(id);
		Receiver receiver = new Receiver(id);
		registrationInProgress = false;
		return receiver;
	}


	//// Implementation ////

	static boolean registrationInProgress = false;

	static Log log = new Log();

	// static lists of registered agents:
	private static IdQueue registeredSenders = new IdQueue();
	static IdQueue registeredReceivers = new IdQueue();
}
