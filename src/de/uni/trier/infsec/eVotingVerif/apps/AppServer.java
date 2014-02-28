package de.uni.trier.infsec.eVotingVerif.apps;

import de.uni.trier.infsec.eVotingVerif.core.Server;
import de.uni.trier.infsec.functionalities.amt.AMT;
import de.uni.trier.infsec.functionalities.amt.AMT.AMTError;
import de.uni.trier.infsec.functionalities.pki.PKI;
import de.uni.trier.infsec.functionalities.smt.SMT;
import de.uni.trier.infsec.functionalities.smt.SMT.SMTError;

public class AppServer {

	
	public static void main(String[] args) {		
		// System.setProperty("remotemode", Boolean.toString(true));
		PKI.useRemoteMode();
		run();
	}

	private static void run() {
		SMT.Receiver serverReceiver;
		AMT.Sender serverSender;
		try {
			
			byte[] serialized = UtilsApp.readFromFile(ParamsApp.PATH_SMT);
			serverReceiver = SMT.receiverFromBytes(serialized);

			serialized = UtilsApp.readFromFile(ParamsApp.PATH_AMT);
			serverSender = AMT.senderFromBytes(serialized);
			
			Server s = new Server(ParamsApp.numberOfVoters, ParamsApp.numberOfCandidates, 
						serverReceiver, serverSender);
			System.out.println("Server: ready to collect votes...");
			while (!s.resultReady()) {
				s.onCollectBallot();
				Thread.sleep(250);
			}
			s.onPostResult();
			System.out.println("Server successfully collected all votes. Terminating.");
		} catch (SMTError e) {
			e.printStackTrace();
		} catch (AMTError e) {
			e.printStackTrace();
		} catch (Exception e) {
			e.printStackTrace();
		}
	}
	
	
}
