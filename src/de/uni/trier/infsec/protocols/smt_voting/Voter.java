package de.uni.trier.infsec.protocols.smt_voting;

import de.uni.trier.infsec.functionalities.pki_nocorrupt.PKIError;
import de.uni.trier.infsec.functionalities.smt.SMT;
import de.uni.trier.infsec.functionalities.smt.SMT.SMTError;
import de.uni.trier.infsec.functionalities.smt.SMT.ConnectionError;

public class Voter {
	private final byte choice;
	private final SMT.Sender sender;

	public Voter(byte choice, SMT.Sender sender) throws SMTError, PKIError, ConnectionError  {
		this.choice = choice;
		this.sender = sender; 
	}

	/*
	 * Prepare the ballot containing the vote and send it to the server using the secure 
	 * message transfer functionality (the Sender object).
	 */
	public void onSendBallot() throws PKIError, ConnectionError, SMTError {
		byte [] ballot = new byte[] {choice};
		sender.sendTo(ballot,  Identifiers.SERVER_ID, Parameters.DEFAULT_HOST_SERVER, Parameters.DEFAULT_LISTEN_PORT_SERVER_SMT);
	}
}
