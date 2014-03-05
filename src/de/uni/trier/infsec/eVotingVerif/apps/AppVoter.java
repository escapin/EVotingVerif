package de.uni.trier.infsec.eVotingVerif.apps;

import de.uni.trier.infsec.eVotingVerif.core.Voter;
import de.uni.trier.infsec.functionalities.pki.PKI;
import de.uni.trier.infsec.functionalities.smt.SMT;
import de.uni.trier.infsec.functionalities.smt.SMT.ConnectionError;
import de.uni.trier.infsec.functionalities.smt.SMT.RegistrationError;
import de.uni.trier.infsec.functionalities.smt.SMT.SMTError;
import de.uni.trier.infsec.utils.Utilities;

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
				SMT.Sender agent = SMT.senderFromBytes(serialized);
				submitVote(vote, id, agent);
			} catch (Exception e) {				
				System.out.println("Something is wrong with arguments!\n" +
						"Expected: AppVoter <vote [1 byte hex]> <voter_id [int]>\n" +
						"Example: AppVoter F5 42");
				e.printStackTrace();
			}
		}
	}


	private static void submitVote(byte vote, int id, SMT.Sender sender) {
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
