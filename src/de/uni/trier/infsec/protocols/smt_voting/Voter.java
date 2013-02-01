package de.uni.trier.infsec.protocols.smt_voting;

import de.uni.trier.infsec.environment.network.NetworkError;
import de.uni.trier.infsec.functionalities.pki.ideal.PKIError;
import de.uni.trier.infsec.functionalities.smt.ideal.SMT;
import de.uni.trier.infsec.functionalities.smt.ideal.SMT.SMTError;

/*
 * Voter client for TrivVoting.
 */
public class Voter {
	private final byte vote;
	private final SMT.Channel channel_to_server;

	public Voter(byte vote, SMT.AgentProxy voter_proxy) throws SMTError, PKIError, NetworkError  {
		this.vote = vote;
		// create secure channel to the server
		this.channel_to_server = voter_proxy.channelTo(Identifiers.SERVER_ID, "www.server.com", 89);
	}

	/*
	 * Prepare the ballot containing the vote and send it using the secure channel to the server.
	 */
	public void onSendBallot() throws SMTError {
		byte [] ballot = new byte[] {vote};
		channel_to_server.send(ballot);
	}
}
