package de.uni.trier.infsec.functionalities.smt;

import static de.uni.trier.infsec.utils.MessageTools.concatenate;
import static de.uni.trier.infsec.utils.MessageTools.first;
import static de.uni.trier.infsec.utils.MessageTools.second;
import de.uni.trier.infsec.functionalities.pkienc.Decryptor;
import de.uni.trier.infsec.functionalities.pkienc.RegisterEnc;
import de.uni.trier.infsec.functionalities.pkisig.Signer;
import de.uni.trier.infsec.functionalities.pkisig.RegisterSig;
import de.uni.trier.infsec.lib.network.NetworkError;
import de.uni.trier.infsec.utils.MessageTools;

/**
 * Real functionality for SMT (Secure Authenticated Message Transmission).
 * See smt.ideal.SMT for typical usage pattern.
 */
public class SMT {

	//// The public interface ////

	@SuppressWarnings("serial")
	static public class SMTError extends Exception {}

	@SuppressWarnings("serial")
	static public class RegistrationError extends Exception {}

	@SuppressWarnings("serial")
	static public class ConnectionError extends Exception {}

	public static Sender registerSender(int id) throws SMTError, RegistrationError, ConnectionError {
		if (registrationInProgress) throw new SMTError();
		registrationInProgress = true;	
		try {
			// create and register a new signer 
			Signer signer = new Signer();
			RegisterSig.registerVerifier(signer.getVerifier(), id, DOMAIN_SMT_VERIFICATION);
			// registration successful; return a new Sender object
			registrationInProgress = false;
			return new Sender(id, signer);
		}
		catch (RegisterSig.PKIError err) {
			registrationInProgress = false;
			throw new RegistrationError();
		}
		catch (NetworkError err) {
			registrationInProgress = false;
			throw new ConnectionError();
		}
	}

	public static Receiver registerReceiver(int id) throws SMTError, RegistrationError, ConnectionError {
		if (registrationInProgress) throw new SMTError();
		registrationInProgress = true;	
		try {
			// create a new decryptor 
			Decryptor decryptor = new Decryptor();
			RegisterEnc.registerEncryptor(decryptor.getEncryptor(), id, DOMAIN_SMT_ENCRYPTION);
			// registration successful; return a new Receiver object
			registrationInProgress = false;
			return new Receiver(id, decryptor);
		}
		catch (RegisterEnc.PKIError err) {
			registrationInProgress = false;
			throw new RegistrationError();
		}
		catch (NetworkError err) {
			registrationInProgress = false;
			throw new ConnectionError();
		}
	}


	////////////////////////////////////////////////////////////////////////////

	static boolean registrationInProgress = false;
	public static final byte[] DOMAIN_SMT_VERIFICATION  = new byte[] {0x02, 0x01};
	public static final byte[] DOMAIN_SMT_ENCRYPTION  = new byte[] {0x02, 0x02};

	/**
	 * Serialization Sender -> Bytes
	 */
	public static byte[] senderToBytes(Sender sender) {
		byte[] id = MessageTools.intToByteArray(sender.id);
		byte[] signer = sender.signer.toBytes();
		byte[] out = concatenate(id, signer);
		return out;
	}

	/**
	 * Serialization Receiver -> Bytes
	 */
	public static byte[] receiverToBytes(Receiver receiver) {
		byte[] id = MessageTools.intToByteArray(receiver.id);
		byte[] signer = receiver.decryptor.toBytes();
		byte[] out = concatenate(id, signer);
		return out;
	}


	/**
	 * Deserialization Sender <- Bytes
	 */
	public static Sender senderFromBytes(byte[] bytes) {
		byte[] bId = first(bytes);
		int id = MessageTools.byteArrayToInt(bId);
		byte[] bSigner = second(bytes);
		Signer signer = Signer.fromBytes(bSigner);
		return new Sender(id, signer);
	}

	/**
	 * Deserialization Receiver <- Bytes
	 */
	public static Receiver receiverFromBytes(byte[] bytes) {
		byte[] bId = first(bytes);
		int id = MessageTools.byteArrayToInt(bId);
		byte[] bDecryptor = second(bytes);
		Decryptor decryptor = Decryptor.fromBytes(bDecryptor);
		return new Receiver(id, decryptor);
	}
}
