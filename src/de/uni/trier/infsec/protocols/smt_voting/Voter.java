package de.uni.trier.infsec.protocols.smt_voting;

import de.uni.trier.infsec.lib.network.NetworkError;
import de.uni.trier.infsec.functionalities.pki_nocorrupt.PKIError;
import de.uni.trier.infsec.functionalities.smt.SMT;
import de.uni.trier.infsec.functionalities.smt.SMT.SMTError;

public class Voter {
	private final byte vote;
	private final SMT.Sender sender;

	public Voter(byte vote, SMT.Sender sender) throws SMTError, PKIError, NetworkError  {
		this.vote = vote;
		this.sender = sender; 
	}

	/*
	 * Prepare the ballot containing the vote and send it to the server using the secure 
	 * message transfer functionality.
	 */
	public void onSendBallot() throws PKIError, NetworkError, SMTError {
		byte [] ballot = new byte[] {vote};
		sender.sendTo(ballot,  Identifiers.SERVER_ID, Parameters.DEFAULT_HOST_SERVER, Parameters.DEFAULT_LISTEN_PORT_SERVER_SMT);
	}
}
