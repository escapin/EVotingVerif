package de.uni.trier.infsec.eVotingVerif.core;

import de.uni.trier.infsec.functionalities.smt.SMT.SMTError;
import de.uni.trier.infsec.functionalities.smt.SMT.ConnectionError;
import de.uni.trier.infsec.functionalities.smt.SMT.RegistrationError;
import de.uni.trier.infsec.functionalities.smt.Sender;

public class Voter {
	private final byte choice;
	private final Sender sender;

	public Voter(byte choice, Sender sender) throws SMTError, RegistrationError, ConnectionError  {
		this.choice = choice;
		this.sender = sender; 
	}

	/*
	 * Prepare the ballot containing the vote and send it to the server using the secure 
	 * message transfer functionality (the Sender object).
	 */
	public void onSendBallot() throws RegistrationError, ConnectionError, SMTError {
		byte [] ballot = new byte[] {choice};
		sender.sendTo(ballot,  Params.SERVER_ID, Params.DEFAULT_HOST_SERVER, 
				Params.LISTEN_PORT_SERVER_SMT);
	}
}
