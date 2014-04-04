package de.uni.trier.infsec.functionalities.smt;

import de.uni.trier.infsec.utils.MessageTools;
import de.uni.trier.infsec.lib.network.NetworkClient;
import de.uni.trier.infsec.lib.network.NetworkError;
import de.uni.trier.infsec.environment.SMTEnv;

/**
 * Ideal functionality for SMT (Secure Authenticated Message Transmission).
 */
public final class SMT {

	//// The public interface ////

	static public class SMTError extends Exception {}

	static public class ConnectionError extends Exception {}

	static public class RegistrationError extends Exception {}

	// what locations belong to the network/SMT, what may be changed upon sending
	//@ public static ghost \locset rep;

	// the abstract state (message queue)
	//@ public static ghost \seq receiver_ids;
	//@ public static ghost \seq messages;
	//@ public static ghost \seq sender_ids;

	//@ public static invariant receiver_ids.length == sender_ids.length;
	//@ public static invariant receiver_ids.length == messages.length;

	//@ public static ghost \seq registered_sender_ids;
	//@ public static ghost \seq registered_receiver_ids;

	/** 
	 * Pair (message, sender_id).
	 * 
	 * Objects of this class are returned when a receiver gets a message.
	 */
	static final public class AuthenticatedMessage {
		public final byte[] message;
		public final int sender_id;
		//@ public invariant message.length > 0;

		public AuthenticatedMessage(byte[] message, int sender) {
			this.sender_id = sender;  this.message = message;
		}
	}

	static final public class Sender 
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
			if (registrationInProgress) throw new SMTError();

			// get from the simulator a message to be later sent out
			byte[] output_message = SMTEnv.sendTo(message.length, id, receiver_id, server, port);
			if (output_message == null) throw new ConnectionError();
			// get the answer from PKI
			if (!registeredReceivers.exists(receiver_id))
				throw new RegistrationError();
			// log the sent message along with the sender and receiver identifiers			
			log.add(new LogEntry(MessageTools.copyOf(message), id, receiver_id));
		  	//@ set messages = \seq_concat(\old(messages),\seq_singleton(message[0]));
			//@ set receiver_ids = \seq_concat(\old(receiver_ids),\seq_singleton(receiver_id));
			//@ set sender_ids = \seq_concat(\old(sender_ids),\seq_singleton(id));

			// sent out the message from the simulator
			try {
				NetworkClient.send(output_message, server, port);
			}
			catch( NetworkError e ) {
				throw new ConnectionError();
			}
		}

		private Sender(int id) {
			this.id = id;
		}
	}

	static final public class Receiver {
		public final int id;
		/*@ invariant 
		  @ (\exists int i; 0 <= i && i < registered_receiver_ids.length; (int)registered_receiver_ids[i]==id);
		  @ invariant 
		  @ (\forall Receiver s; r.id == id; r == this);
		  @ invariant \disjoint(SMT.rep, \singleton(this.id));
		  @*/

		//@ ensures true;
		//@ pure
		public void listenOn(int port) throws ConnectionError {
			boolean ok = SMTEnv.listenOn(port);
			if (!ok) throw new ConnectionError();
		}

		/*@ ensures \result==null || (\exists int i; 0 <= i && i < messages.length;
		  @	\result.message[0] == (byte)messages[i]);
		  @	&& (int)receiver_ids[i] == id && (int)sender_ids[i] == \result.sender_id;
		  @ ensures \result==null || (\fresh(\result) && \invariant_for(\result));
		  @ ensures \disjoint(SMT.rep, \result.*);
	  	  @ ensures \new_elems_fresh(SMT.rep);
		  @ assignable SMT.rep, Environment.counter;
		  @*/
		public /*@ nullable @*/ AuthenticatedMessage getMessage(int port) throws SMTError {
			if (registrationInProgress) throw new SMTError();			

			// the simulator/environment determines the index of the message to be returned
			int index = SMTEnv.getMessage(this.id, port);
			if (index < 0) return null;
			LogEntry smtmsg = log.get(index);
			if (smtmsg == null) return null;
			// check whether the message was sent to *this* receiver
			if (smtmsg.receiver_id != id) return null;
			// return new authenticated message
			return new AuthenticatedMessage(MessageTools.copyOf(smtmsg.message), smtmsg.sender_id);
		}

		private Receiver(int id)  {
			this.id = id;
		}
	}

	/*@ ensures \invariant_for(\result) && \fresh(\result);
	  @ ensures \new_elems_fresh(SMT.rep);
	  @ ensures SMT.registered_sender_ids == \seq_concat(\old(SMT.registered_sender_ids),\seq_singleton(id));
	  @ assignable SMT.rep, SMT.registered_sender_ids;
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

	/*@ ensures \invariant_for(\result) && \fresh(\result);
	  @ ensures \new_elems_fresh(SMT.rep);
	  @ ensures SMT.registered_receiver_ids == \seq_concat(\old(SMT.registered_receiver_ids),\seq_singleton(id));
	  @ assignable SMT.rep;
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

	private static boolean registrationInProgress = false;

	private static class LogEntry {
		final byte[] message;
		final int sender_id;
		final int receiver_id;

		LogEntry(byte[] message, int sender_id, int receiver_id) {
			this.message = message;
			this.sender_id = sender_id;
			this.receiver_id = receiver_id;
		}
	}

	// A queue of messages along with the identifier of senders and receivers.
	private static class Log 
	{
		private static class Node {
			final LogEntry msg;
			final Node next;

			Node(LogEntry msg, Node next) {
				this.msg = msg;
				this.next = next;
			}
		}		
		private Node first = null;

		void add(LogEntry msg) {
			first = new Node(msg, first);
		}

		LogEntry get(int index) {
			int i = 0;
			for( Node node = first;  node != null;  node = node.next ) {
				if(i == index) return node.msg;
				++i;
			}
			return null;
		}
	}

	static Log log = new Log();

	// Collection of (registered) identifiers.
	private static class IdQueue
	{	
		private static class Node {
			final int id;
			final Node next;

			Node(int id, Node next) {
				this.id = id;
				this.next = next;
			}
		}			
		private Node first = null;

		public void add(int id) {
			first = new Node(id, first);
		}

		boolean exists(int id) {
			for( Node node = first;  node != null;  node = node.next )
				if( id == node.id )
					return true;
			return false;
		}
	}

	// static lists of registered agents:
	private static IdQueue registeredSenders = new IdQueue();
	private static IdQueue registeredReceivers = new IdQueue();
}
