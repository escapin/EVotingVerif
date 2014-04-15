package de.uni.trier.infsec.functionalities.smt;

/** 
 * Pair message, sender_id. 
 *
 * Objects of this class are returned when an agent try to read a message from its queue. 
 */
public class AuthenticatedMessage {
	public byte[] message;
	public int sender_id;

	protected AuthenticatedMessage(byte[] message, int sender) {
		this.sender_id = sender;  this.message = message;
	}
}