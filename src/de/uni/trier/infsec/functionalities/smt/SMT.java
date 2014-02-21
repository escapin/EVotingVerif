package de.uni.trier.infsec.functionalities.smt;

import de.uni.trier.infsec.utils.MessageTools;
import de.uni.trier.infsec.functionalities.pki_nocorrupt.PKIError;
import de.uni.trier.infsec.lib.network.NetworkClient;
import de.uni.trier.infsec.lib.network.NetworkError;
import de.uni.trier.infsec.environment.SMTEnv;

/**
 * Ideal functionality for SMT (Secure Authenticated Message Transmission).
 */
public class SMT {

	//// The public interface ////

	@SuppressWarnings("serial")
	static public class SMTError extends Exception {}

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

	static public class Sender 
	{
		public final int id;

		public void sendTo(byte[] message, int receiver_id, String server, int port) throws SMTError, PKIError, NetworkError {
			if (registrationInProgress) throw new SMTError();

			// get from the simulator a message to be later sent out
			byte[] output_message = SMTEnv.sendTo(message.length, id, receiver_id, server, port);
			if (output_message == null) throw new NetworkError();
			// get the answer from PKI
			if (!registeredReceivers.exists(receiver_id))
				throw new PKIError();
			// log the sent message along with the sender and receiver identifiers			
			log.add(new LogEntry(MessageTools.copyOf(message), id, receiver_id));
			// sent out the message from the simulator
			NetworkClient.send(output_message, server, port);
		}

		private Sender(int id) {
			this.id = id;
		}
	}

	static public class Receiver {
		public final int id;

		public AuthenticatedMessage getMessage(int port) throws SMTError {
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

	public static Sender registerSender(int id) throws SMTError, PKIError, NetworkError {
		if (registrationInProgress) throw new SMTError();
		registrationInProgress = true;
		// call the simulator, throw a network error if the simulator says so
		boolean network_ok = SMTEnv.registerSender(id);
		if (!network_ok) throw new NetworkError();
		// check whether the id has not been claimed
		if( registeredSenders.exists(id) ) {
			registrationInProgress = false;
			throw new PKIError();
		}
		// create a new agent, add it to the list of registered agents, and return it
		registeredSenders.add(id);
		Sender sender = new Sender(id);
		registrationInProgress = false;
		return sender;
	}

	public static Receiver registerReceiver(int id) throws SMTError, PKIError, NetworkError {
		if (registrationInProgress) throw new SMTError();
		registrationInProgress = true;
		// call the simulator, throw a network error if the simulator says so
		boolean network_ok =  SMTEnv.registerReceiver(id);
		if (!network_ok) throw new NetworkError();
		// check whether the id has not been claimed
		if( registeredReceivers.exists(id) ) {
			registrationInProgress = false;
			throw new PKIError();
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
