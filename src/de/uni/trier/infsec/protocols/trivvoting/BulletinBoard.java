package de.uni.trier.infsec.protocols.trivvoting;

import de.uni.trier.infsec.environment.network.Network;
import de.uni.trier.infsec.environment.network.NetworkError;
import de.uni.trier.infsec.functionalities.samt.ideal.SAMT;
import de.uni.trier.infsec.utils.MessageTools;

/*
 * Bulletin board on which the server can post messages (the result) and
 * everybody can retrieve the posted messages.
 */
public class BulletinBoard {

	public BulletinBoard(SAMT.AgentProxy proxy) {
		content = new MessageList();
		samt_proxy = proxy;
	}

	/*
	 * Reads a message, checks if it comes from the server, and, if this is the
	 * case, adds it to the maintained list of messages.
	 */
	public void onPost() {
		SAMT.AuthenticatedMessage am = samt_proxy.getMessage();
		if (am == null) return;
		if (am.sender_id != Identifiers.SERVER_ID) return;

		byte[] message = am.message;
		content.add(message);
	}

	/*
	 * Sends its content (that is the concatenation of all the message in the maintained
	 * list of messages) over the network.
	 */
	public void onRequestContent() throws NetworkError {
		byte[] contentMessage = {};
		for( MessageList.Node node = content.first;  node!=null;  node = node.next ) {
			contentMessage = MessageTools.concatenate(contentMessage, node.message);
		}
		Network.networkOut(contentMessage);
	}

	/// implementation ///

	class MessageList {
		class Node {
			byte[] message;
			Node next;
			Node(byte[] message, Node next) { this.message = message; this.next = next; }
		}

		Node first = null;

		void add(byte[] message) {
			first = new Node(message, first);
		}
	}

	private MessageList content;
	private SAMT.AgentProxy samt_proxy;
}
