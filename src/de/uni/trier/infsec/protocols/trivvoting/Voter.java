package de.uni.trier.infsec.protocols.trivvoting;

import de.uni.trier.infsec.functionalities.samt.ideal.SAMT;

/*
 * Voter client for TrivVoting.
 */
public class Voter {
        private static int idCounter = 0;

        private final byte vote = HonestVotersSetup.setup.getVoteForVoter(this);

        public final int ID;
	private final SAMT.Channel channel_to_server;

	public Voter() {
                this.ID = idCounter;
                idCounter++;
                SAMT.AgentProxy voter_proxy = SAMT.register(ID);
		// create secure channel to the server
		this.channel_to_server = voter_proxy.channelTo(Identifiers.SERVER_ID);
	}

	/*
	 * Prepare the ballot containing the vote given as the argument and send it
	 * through the secure channel to the server.
	 */
	public void onSendBallot() {
		byte [] ballot = new byte[] {vote};  // for now, the ballot is not even encrypted!
		channel_to_server.send(ballot);
	}

}
