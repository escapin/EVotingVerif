package de.uni.trier.infsec.protocols.trivvoting;

import de.uni.trier.infsec.functionalities.samt.ideal.SAMT;

/*
 * Voter client for TrivVoting.
 */
public class Voter {
	private final byte vote;
	private final SAMT.Channel channel_to_server;

	public Voter(byte vote, SAMT.AgentProxy voter_proxy) throws SAMT.Error {
		this.vote = vote;
		// create secure channel to the server
		this.channel_to_server = voter_proxy.channelTo(Identifiers.SERVER_ID);
	}

	/*
	 * Prepare the ballot containing the vote and send it using the secure channel to the server.
	 */
	public void onSendBallot() throws SAMT.Error {
		byte [] ballot = new byte[] {vote};
		channel_to_server.send(ballot);
	}
}
