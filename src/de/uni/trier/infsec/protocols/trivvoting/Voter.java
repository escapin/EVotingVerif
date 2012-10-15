package de.uni.trier.infsec.protocols.trivvoting;

import de.uni.trier.infsec.functionalities.pkenc.ideal.Encryptor;

/*
 * Voter client for TivVoting.
 */
public class Voter {
	private Encryptor serverEnc = null;

	public Voter(Encryptor serverEnc) {
		this.serverEnc = serverEnc;
	}

	/*
	 * Prepare and return (a bit-string representing) the ballot containing the
	 * vote given as the argument.
	 */
	public byte[] makeBallot(byte vote) {
		byte [] ballot = new byte[] {vote};  // for now, the ballot is not even encrypted!
		return ballot;
	}
}
