package eVotingVerif.apps;

import eVotingVerif.core.Voter;
import funct.pki.PKI;
import funct.smt.SMT;
import funct.smt.Sender;
import funct.smt.SMT.ConnectionError;
import funct.smt.SMT.RegistrationError;
import funct.smt.SMT.SMTError;
import utils.Utilities;

public class AppVoter {

	public static void main(String[] args) {
		//System.setProperty("remotemode", Boolean.toString(true));
		PKI.useRemoteMode();
		if (args.length < 2) {
			System.out.println("Wrong number of Arguments!\n" +
					"Expected: AppVoter <vote [1 byte hex]> <voter_id [int]>\n" +
					"Example: AppVoter F5 42");
		} else {
			try {				
				byte vote = Utilities.hexStringToByteArray(args[0])[0]; 
				// Take first byte in case there are is more than one byte
				int id    = Integer.parseInt(args[1]);		
				byte[] serialized = UtilsApp.readFromFile(ParamsApp.PATH_VOTER.replaceAll("%%%%", "" + id)); 
				Sender agent = SMT.senderFromBytes(serialized);
				submitVote(vote, id, agent);
			} catch (Exception e) {				
				System.out.println("Something is wrong with arguments!\n" +
						"Expected: AppVoter <vote [1 byte hex]> <voter_id [int]>\n" +
						"Example: AppVoter F5 42");
				e.printStackTrace();
			}
		}
	}


	private static void submitVote(byte vote, int id, Sender sender) {
		try {
			Voter v = new Voter(vote, sender);
			v.onSendBallot();
			System.out.println("Voter " + id  + " successfully voted. Terminating.");
		} catch (SMTError e) {
			e.printStackTrace();
		} catch (RegistrationError e) {
			e.printStackTrace();
		} catch (ConnectionError e) {
			e.printStackTrace();
		}
	}
}
