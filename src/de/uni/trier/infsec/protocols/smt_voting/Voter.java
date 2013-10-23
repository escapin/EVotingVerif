package de.uni.trier.infsec.protocols.smt_voting;

/*
 * Voter client for TrivVoting.
 */
public class Voter {
	private final int id;
	private final byte vote;

	public Voter(int id, byte vote) {
		this.id = id;
		this.vote = vote;
	}

	/*
	 * Prepare the ballot containing the vote and send it to the server.
	 */
	public void onSendBallot(Server server)  {
		byte [] ballot = new byte[] {vote};
		// send the vote directly to the server	(by a method call)	
		server.onCollectBallot(id, ballot);
	}
}
