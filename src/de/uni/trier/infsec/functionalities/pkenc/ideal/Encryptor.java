package de.uni.trier.infsec.functionalities.pkenc.ideal;

import de.uni.trier.infsec.environment.crypto.CryptoLib;
import de.uni.trier.infsec.utils.MessageTools;

/**
 * Ideal functionality for public-key encryption: Encryptor
 */
public final class Encryptor {

	private MessagePairList log;
	private byte[] publKey;
	
	Encryptor(MessagePairList mpl, byte[] publicKey) { 
		log = mpl;		
		publKey = publicKey;
	}
		
	public byte[] getPublicKey() {
		return MessageTools.copyOf(publKey);
	}
	
	public byte[] encrypt(byte[] message) {
		byte[] messageCopy = MessageTools.copyOf(message);
		byte[] randomCipher = null;
		// keep asking the environment for the ciphertext, until a fresh one is given:
		while( randomCipher==null || log.contains(randomCipher) ) {
			randomCipher = MessageTools.copyOf(
					CryptoLib.pke_encrypt(MessageTools.getZeroMessage(message.length), MessageTools.copyOf(publKey)));
		}
		log.add(messageCopy, randomCipher);
		return MessageTools.copyOf(randomCipher);
	}
}
