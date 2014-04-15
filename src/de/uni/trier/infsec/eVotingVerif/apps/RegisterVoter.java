package de.uni.trier.infsec.eVotingVerif.apps;

import java.io.IOException;

import de.uni.trier.infsec.functionalities.pki.PKI;
import de.uni.trier.infsec.functionalities.smt.SMT;
import de.uni.trier.infsec.functionalities.smt.Sender;

public class RegisterVoter {

	public static void main(String[] args) throws IOException {
		//System.setProperty("remotemode", Boolean.toString(true));
		PKI.useRemoteMode();
		if (args.length < 1) {
			System.out.println("Wrong number of Arguments!\n" +
					"Expected: RegisterVoter <voter_id [int]>\n" +
					"Example: RegisterVoter 42");
		} else {
			try {				
				int id  = Integer.parseInt(args[0]);
				Sender sender = SMT.registerSender(id);
				byte[] serialized = SMT.senderToBytes(sender);
				UtilsApp.storeAsFile(serialized, ParamsApp.PATH_VOTER.replaceAll("%%%%", "" + id));
			} catch (Exception e) {
				System.out.println("Something is wrong with arguments!\n" +
						"Expected: RegisterVoter <voter_id [int]>\n" +
						"Example: RegisterVoter 42");
				e.printStackTrace();
			}
		}
	}

}
