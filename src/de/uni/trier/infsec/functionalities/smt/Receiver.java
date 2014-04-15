package de.uni.trier.infsec.functionalities.smt;

import de.uni.trier.infsec.functionalities.pkienc.Decryptor;
import de.uni.trier.infsec.functionalities.pkisig.RegisterSig;
import de.uni.trier.infsec.functionalities.pkisig.Verifier;
import de.uni.trier.infsec.functionalities.smt.SMT.ConnectionError;
import de.uni.trier.infsec.functionalities.smt.SMT.SMTError;
import de.uni.trier.infsec.lib.network.NetworkError;
import de.uni.trier.infsec.lib.network.NetworkServer;
import de.uni.trier.infsec.utils.MessageTools;

public class Receiver {
	public final int id;
	final Decryptor decryptor;
	
	public void listenOn(int port) throws ConnectionError {
		try {
			NetworkServer.listenForRequests(port);
		}
		catch (NetworkError e) {
			throw new ConnectionError();
		}
	}

	public AuthenticatedMessage getMessage(int port) throws SMTError {
		if (SMT.registrationInProgress) throw new SMTError();

		try {
			// read a message from the network
			// (it may end up with a network error)
			byte[] inputMessage = NetworkServer.read(port);
			if (inputMessage == null) return null;

			// get the sender id and her verifier
			byte[] sender_id_as_bytes = MessageTools.first(inputMessage);
			int sender_id = MessageTools.byteArrayToInt(sender_id_as_bytes);
			Verifier sender_verifier = RegisterSig.getVerifier(sender_id, SMT.DOMAIN_SMT_VERIFICATION);

			// retrieve the recipient id and the signature
			byte[] signedAndEncrypted = MessageTools.second(inputMessage);
			byte[] signed = decryptor.decrypt(signedAndEncrypted);
			byte[] signature = MessageTools.first(signed);
			byte[] message_with_recipient_id = MessageTools.second(signed);

			// verify the signature
			if(!sender_verifier.verify(signature, message_with_recipient_id))
				return null; // invalid signature

			// make sure that the message is intended for this receiver
			byte[] recipient_id_as_bytes = MessageTools.first(message_with_recipient_id);
			int recipient_id = MessageTools.byteArrayToInt(recipient_id_as_bytes);
			if( recipient_id != id )
				return null; // message not intended for this receiver
			byte[] message = MessageTools.second(message_with_recipient_id);
			return new AuthenticatedMessage(message, sender_id);
		}
		catch (NetworkError | RegisterSig.PKIError e) {
			return null;
		}
	}

	Receiver(int id, Decryptor decryptor)  {
		this.id = id;
		this.decryptor = decryptor;
	}
}