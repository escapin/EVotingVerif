package de.uni.trier.infsec.functionalities.smt;

import static de.uni.trier.infsec.utils.MessageTools.concatenate;
import de.uni.trier.infsec.functionalities.pkienc.Encryptor;
import de.uni.trier.infsec.functionalities.pkienc.RegisterEnc;
import de.uni.trier.infsec.functionalities.pkisig.Signer;
import de.uni.trier.infsec.functionalities.smt.SMT.ConnectionError;
import de.uni.trier.infsec.functionalities.smt.SMT.RegistrationError;
import de.uni.trier.infsec.functionalities.smt.SMT.SMTError;
import de.uni.trier.infsec.lib.network.NetworkClient;
import de.uni.trier.infsec.lib.network.NetworkError;
import de.uni.trier.infsec.utils.MessageTools;

public class Sender 
{
	public final int id;
	final Signer signer;

	Sender(int id, Signer signer) {
		this.id = id;
		this.signer = signer;
	}
	
	public void sendTo(byte[] message, int receiver_id, String server, int port) throws SMTError, RegistrationError, ConnectionError {
		if (SMT.registrationInProgress) throw new SMTError();

		// get the encryptor for the receiver
		Encryptor recipient_encryptor;
		try {
			recipient_encryptor = RegisterEnc.getEncryptor(receiver_id, SMT.DOMAIN_SMT_ENCRYPTION);
		}
		catch (RegisterEnc.PKIError e) {
			throw new RegistrationError();
		} 
		catch (NetworkError e) {
			throw new ConnectionError();
		}
		

		// format the message (sign and encrypt)
		byte[] recipient_id_as_bytes = MessageTools.intToByteArray(receiver_id);
		byte[] message_with_recipient_id = concatenate(recipient_id_as_bytes, message);
		byte[] signature = signer.sign(message_with_recipient_id);
		byte[] signed = MessageTools.concatenate(signature, message_with_recipient_id);
		byte[] signedAndEncrypted = recipient_encryptor.encrypt(signed);
		byte[] sender_id_as_bytes = MessageTools.intToByteArray(id);
		byte[] outputMessage = MessageTools.concatenate(sender_id_as_bytes, signedAndEncrypted);

		// send it out			
		try {
			NetworkClient.send(outputMessage, server, port);
		} 
		catch (NetworkError e) {
			throw new ConnectionError();
		}
	}
}