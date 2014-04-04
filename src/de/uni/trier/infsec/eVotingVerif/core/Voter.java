package de.uni.trier.infsec.eVotingVerif.core;

import de.uni.trier.infsec.functionalities.smt.SMT;
import de.uni.trier.infsec.functionalities.smt.SMT.SMTError;
import de.uni.trier.infsec.functionalities.smt.SMT.ConnectionError;
import de.uni.trier.infsec.functionalities.smt.SMT.RegistrationError;

public final class Voter {
	private final byte choice;
	private final SMT.Sender sender;
    private boolean voted;

	public Voter(byte choice, SMT.Sender sender) throws SMTError, RegistrationError, ConnectionError  {
		this.choice = choice;
		this.sender = sender; 
        this.voted = false;
	}

	/*
	 * Prepare the ballot containing the vote and send it to the server using the secure 
	 * message transfer functionality (the Sender object).
	 */
	public void onSendBallot() throws RegistrationError, ConnectionError, SMTError {
        if (voted) return;
        voted = true;
		byte [] ballot = new byte[] {choice};
		sender.sendTo(ballot,  Params.SERVER_ID, Params.DEFAULT_HOST_SERVER, Params.LISTEN_PORT_SERVER_SMT);
	}
}
