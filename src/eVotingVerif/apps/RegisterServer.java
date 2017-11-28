package eVotingVerif.apps;

import eVotingVerif.core.Params;
import funct.amt.AMT;
import funct.amt.AMT.AMTError;
import funct.pki.PKI;
import funct.smt.Receiver;
import funct.smt.SMT;
import funct.smt.SMT.SMTError;

public class RegisterServer {

	public static void main(String[] args) {		
		// System.setProperty("remotemode", Boolean.toString(true));
		PKI.useRemoteMode();
		registerAndSave();
	}

	private static void registerAndSave() {
		Receiver serverReceiver;
		AMT.Sender serverSender;
		try {
			serverReceiver = SMT.registerReceiver(Params.SERVER_ID);
			byte[] serialized = SMT.receiverToBytes(serverReceiver);
			UtilsApp.storeAsFile(serialized, ParamsApp.PATH_SMT);
			
			serverSender  = AMT.registerSender(Params.SERVER_ID);
			serialized = AMT.senderToBytes(serverSender);
			UtilsApp.storeAsFile(serialized, ParamsApp.PATH_AMT);
		} catch (SMTError e) {
			e.printStackTrace();
		} catch (AMTError e) {
			e.printStackTrace();
		} catch (Exception e) {
			e.printStackTrace();
		}
	}
	
}
