package de.uni.trier.infsec.protocols.core;

import de.uni.trier.infsec.environment.Environment;
import de.uni.trier.infsec.functionalities.smt.SMT;
import de.uni.trier.infsec.functionalities.amt.AMT;

public final class Setup 
{
	private static int numberOfVoters = 50;
	private static int numberOfCandidates = 5;

	private final Voter[] voters;
	private final Server server;
	private final BulletinBoard BB;
	private final SMT.Sender adversarySMTSender;
	private final AMT.Sender adversaryAMTSender;

	// one secret bit
	private static boolean secret;

	// the correct result
	static int[] correctResult; // CONSERVATIVE EXTENSION

	private Setup() throws Throwable {
		// let the environment determine two vectors of choices
		byte[] choices0 = new byte[numberOfVoters];
		byte[] choices1 = new byte[numberOfVoters];
		for (int i=0; i<numberOfVoters; ++i) {
			choices0[i] = (byte)Environment.untrustedInput();
			choices1[i] = (byte)Environment.untrustedInput();
		}

		// check that those vectors give the same result
		int[] r0 = computeResult(choices0);
		int[] r1 = computeResult(choices1);
		if (!equalResult(r0,r1))
			throw new Throwable();	// abort if the vectors do not yield the same result

		// store correct result
		correctResult = r1; // CONSERVATIVE EXTENSION

		// create voters, using the choices from on of the vectors
		// according to the secret bit        
		voters = new Voter[numberOfVoters];
		for( int i=0; i<numberOfVoters; ++i ) {
			SMT.Sender sender = SMT.registerSender(i); // sender with identifier i
			byte choice = secret ? choices0[i] : choices1[i];
			voters[i] = new Voter(choice, sender);
		}

		// create the server
		SMT.Receiver serverReceiver = SMT.registerReceiver(Params.SERVER_ID);
		AMT.Sender serverSender = AMT.registerSender(Params.SERVER_ID);
		server = new Server(numberOfVoters, numberOfCandidates, serverReceiver, serverSender);

		// create the bulletin board
		BB = new BulletinBoard();
		
		// create SMT and AMD functionalities for the adversary
		int adv_smt_id = Environment.untrustedInput();
		adversarySMTSender = SMT.registerSender(adv_smt_id);
		int adv_amt_id = Environment.untrustedInput();
		adversaryAMTSender = AMT.registerSender(adv_amt_id);
	}

	private static int[] computeResult (byte[] choices) {
		int[] res = new int[numberOfCandidates];
		for (int i=0; i<choices.length; i++) 
			++res[choices[i]];
		return res;
	}

	private static boolean equalResult(int[] r1, int[] r2) {
		for (int j= 0; j<r1.length; j++)
			if (r1[j]!=r2[j]) return false;
		return true;
	}


	public static void main (String[] a) throws Throwable {
		Setup s = new Setup();
		s.main();
	}

	// end hybrid approach extensions
	////////////////////////////////////////////////////////////////////

	public void main () throws Throwable {
		byte[] message;
		int rec_id;
		int port;
		String host;
		
		// let adversary decide how long the election runs
		while( Environment.untrustedInput() != 0 )  {
			int decision = Environment.untrustedInput();
			switch (decision) {
			case 0:	// a voter (determined by the adversary) votes
				final int k = Environment.untrustedInput();
				final Voter v = voters[k];
				v.onSendBallot();
				break;

			case 1: // the server reads a message from a secure channel
				server.onCollectBallot();
				break;

			case 2: // the server posts the result of the election (if ready) on the bulletin board
				server.onPostResult();
				break;

			case 3: // the bulletin board reads a message:
				BB.onPost();
				break;

			case 4: // the bulletin board sends its content (over the network):
				byte[] content = BB.onRequestContent();
				Environment.untrustedOutputMessage(content);
				break;
				
			case 5: // the adversary sends a message of his choice using SMT:
				message = Environment.untrustedInputMessage();
				rec_id = Environment.untrustedInput();
				host = Environment.untrustedInputString();
				port = Environment.untrustedInput();
				adversarySMTSender.sendTo(message, rec_id, host, port);

			case 6: // the adversary sends a message of his choice using AMT:
				message = Environment.untrustedInputMessage();
				rec_id = Environment.untrustedInput();
				host = Environment.untrustedInputString();
				port = Environment.untrustedInput();
				adversaryAMTSender.sendTo(message, rec_id, host, port);
			}
		}
	}
}
