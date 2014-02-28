package de.uni.trier.infsec.apps;

import de.uni.trier.infsec.functionalities.amt.AMT;
import de.uni.trier.infsec.functionalities.amt.AMT.AMTError;
import de.uni.trier.infsec.functionalities.smt.SMT;
import de.uni.trier.infsec.functionalities.smt.SMT.SMTError;
import de.uni.trier.infsec.protocols.core.Params;

public class RegisterServer {

	public static void main(String[] args) {		
		System.setProperty("remotemode", Boolean.toString(true));
		registerAndSave();
	}

	private static void registerAndSave() {
		SMT.Receiver serverReceiver;
		AMT.Sender serverSender;
		try {
			serverReceiver = SMT.registerReceiver(Params.SERVER_ID);
			byte[] serialized = SMT.receiverToBytes(serverReceiver);
			UtilsApp.storeAsFile(serialized, Params.PATH_SMT);
			
			serverSender  = AMT.registerSender(Params.SERVER_ID);
			serialized = AMT.senderToBytes(serverSender);
			UtilsApp.storeAsFile(serialized, Params.PATH_AMT);
		} catch (SMTError e) {
			e.printStackTrace();
		} catch (AMTError e) {
			e.printStackTrace();
		} catch (Exception e) {
			e.printStackTrace();
		}
	}
	
}
