package eVotingVerif.apps;

import eVotingVerif.core.Server;
import funct.amt.AMT;
import funct.amt.AMT.AMTError;
import funct.pki.PKI;
import funct.smt.Receiver;
import funct.smt.SMT;
import funct.smt.SMT.SMTError;

public class AppServer {

	
	public static void main(String[] args) {		
		// System.setProperty("remotemode", Boolean.toString(true));
		PKI.useRemoteMode();
		run();
	}

	private static void run() {
		Receiver serverReceiver;
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
