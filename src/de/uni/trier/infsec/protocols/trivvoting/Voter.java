package de.uni.trier.infsec.protocols.trivvoting;

import de.uni.trier.infsec.functionalities.samt.ideal.SAMT;

/*
 * Voter client for TrivVoting.
 */
public class Voter {
	private SAMT.Channel channel_to_server;

	public Voter(SAMT.AgentProxy voter_proxy) {
		// create secure channel to the server
		this.channel_to_server = voter_proxy.channelTo(Identifiers.SERVER_ID);
	}

	/*
	 * Prepare the ballot containing the vote given as the argument and send it
	 * through the secure channel to the server.
	 */
	public void onSendBallot(byte vote) {
		byte [] ballot = new byte[] {vote};  // for now, the ballot is not even encrypted!
		channel_to_server.send(ballot);
	}

}
