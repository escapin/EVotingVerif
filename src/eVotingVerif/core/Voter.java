package eVotingVerif.core;

import funct.smt.Sender;
import funct.smt.SMT.ConnectionError;
import funct.smt.SMT.RegistrationError;
import funct.smt.SMT.SMTError;

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
