package de.uni.trier.infsec.functionalities.amt;

import de.uni.trier.infsec.utils.MessageTools;
import de.uni.trier.infsec.environment.Environment;
import de.uni.trier.infsec.environment.AMTEnv;
import de.uni.trier.infsec.functionalities.smt.SMT;

/**
 * Ideal functionality for AMT (Authenticated Message Transmission).
 */
public class AMT {

	//// The public interface ////

	/** 
	 * Pair (message, sender_id).
	 * 
	 * Objects of this class are returned when a receiver gets a message.
	 */
	static public class AuthenticatedMessage {
		public final byte[] message;
		public final int sender_id;

		public AuthenticatedMessage(byte[] message, int sender) {
			this.sender_id = sender;  this.message = message;
		}
	}

	/*@ ensures \new_elems_fresh(SMT.rep);
	  @ ensures SMT.receiver_ids == \old(SMT.receiver_ids);
      @ ensures SMT.sender_ids == \old(SMT.sender_ids);
      @ ensures SMT.messages == \old(SMT.messages);
      @ ensures SMT.registered_receiver_ids == \old(SMT.registered_receiver_ids);
      @ ensures SMT.registered_sender_ids == \old(SMT.registered_sender_ids);
	  @ diverges true;
	  @ assignable \set_union(SMT.rep, \singleton(Environment.counter));
	  @ helper
	  @*/
	public static Sender registerSender(int id) throws AMTError, RegistrationError, ConnectionError {
		if (registrationInProgress) throw new AMTError();
		registrationInProgress = true;
		// call the simulator, throw a network error if the simulator says so
		boolean network_ok = AMTEnv.registerSender(id);
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
	
	public static void listenOn(int port) throws ConnectionError {
		boolean ok = AMTEnv.listenOn(port);
		if (!ok) throw new ConnectionError();
	}

	public static AuthenticatedMessage getMessage(int id, int port) throws AMTError {
		if (registrationInProgress) throw new AMTError();			

		// the simulator/environment determines the index of the message to be returned
		int index = AMTEnv.getMessage(id, port);
		if (index < 0) return null;
		LogEntry smtmsg = log.get(index);
		if (smtmsg == null) return null;
		// check whether the message was sent to *this* receiver
		if (smtmsg.receiver_id != id) return null;
		// return new authenticated message
		return new AuthenticatedMessage(MessageTools.copyOf(smtmsg.message), smtmsg.sender_id);
	}


	//// Implementation ////

	static boolean registrationInProgress = false;

	static class LogEntry {
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
	static class Log 
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
}
