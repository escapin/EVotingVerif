package de.uni.trier.infsec.eVotingVerif.core;

import de.uni.trier.infsec.environment.Environment;
import de.uni.trier.infsec.functionalities.smt.Receiver;
import de.uni.trier.infsec.functionalities.smt.SMT;
import de.uni.trier.infsec.functionalities.smt.SMT.RegistrationError;
import de.uni.trier.infsec.functionalities.smt.SMT.SMTError;
import de.uni.trier.infsec.functionalities.amt.AMT;
import de.uni.trier.infsec.functionalities.amt.AMT.AMTError;
import de.uni.trier.infsec.functionalities.amt.AMT.ConnectionError;

public final class Setup 
{
	private Voter[] voters;
	private final Server server;
	private final BulletinBoard BB;

	// one secret bit
	private static boolean secret;

	// the correct result
	static int[] correctResult; // CONSERVATIVE EXTENSION

	private Setup(int numberOfCandidates, int numberOfVoters) throws Throwable {
		// let the environment determine two vectors of choices
		byte[] choices0 = createChoices(numberOfVoters, numberOfCandidates);
        byte[] choices1 = createChoices(numberOfVoters, numberOfCandidates);

		// check that those vectors give the same result
		int[] r0 = computeResult(choices0, numberOfCandidates);
		int[] r1 = computeResult(choices1, numberOfCandidates);
		if (!equalResult(r0,r1))
			throw new Throwable();	// abort if the vectors do not yield the same result

		// store correct result
		correctResult = r1; // CONSERVATIVE EXTENSION

		// create voters, using the choices from the vectors
		// according to the secret bit        
		createVoters(numberOfVoters, choices0, choices1);

		// create the server
		server = createServer(numberOfCandidates, numberOfVoters);

		// create the bulletin board
		BB = createBulltetinBoard();
	}
	
	private byte[] createChoices(int numberOfVoters, int numberOfCandidates) {
	    final byte[] choices = new byte[numberOfVoters];
        for (int i=0; i<numberOfVoters; ++i) {
            // Daniel: this cast is really ugly; why not use byte from the beginning?
            choices[i] = (byte)(Environment.untrustedInput(numberOfCandidates));
        }
        return choices;
	}

    private void createVoters(int numberOfVoters, byte[] choices0,
                    byte[] choices1) throws SMTError, RegistrationError,
                    de.uni.trier.infsec.functionalities.smt.SMT.ConnectionError {
        voters = new Voter[numberOfVoters];
		for( int i=0; i<numberOfVoters; ++i ) {
			de.uni.trier.infsec.functionalities.smt.Sender sender = SMT.registerSender(i); // sender with identifier i
			byte choice = secret ? choices0[i] : choices1[i];
			voters[i] = new Voter(choice, sender);
		}
    }

    private Server createServer(int numberOfCandidates, int numberOfVoters)
                    throws SMTError,
                    RegistrationError,
                    de.uni.trier.infsec.functionalities.smt.SMT.ConnectionError,
                    AMTError,
                    de.uni.trier.infsec.functionalities.amt.AMT.RegistrationError,
                    ConnectionError {
        Receiver serverReceiver = SMT.registerReceiver(Params.SERVER_ID);
		de.uni.trier.infsec.functionalities.amt.Sender serverSender = AMT.registerSender(Params.SERVER_ID);
		return new Server(numberOfVoters, numberOfCandidates, serverReceiver, serverSender);
    }

    private BulletinBoard createBulltetinBoard() throws ConnectionError {
        return new BulletinBoard();
    }

	private static int[] computeResult (byte[] choices, int numberOfCandidates) {
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
        int numberOfCandidates = Environment.untrustedInput();
        int numberOfVoters = Environment.untrustedInput();
        if (numberOfVoters<=0 || numberOfCandidates<=0)
			throw new Throwable();	// abort 
		Setup s = new Setup(numberOfCandidates, numberOfVoters);
        int N = Environment.untrustedInput(); // the environment decides how long the system runs
        s.votingPhase(N);
        s.afterVotingPhase();
	}

	public void votingPhase(int N) throws Throwable {
        int voter = 0;
        for(int i=0; i<N; ++i ) {
            // the choice is already encoded in N
            if (Environment.evalUntrustedInput(N)) { // a voter (determined by the adversary) votes
				final Voter v = voters[voter++]; // better: v = voters[decision]
				v.onSendBallot();
            }
            else { // the server reads a message from a secure channel
				server.onCollectBallot();
            }
        }
        server.onPostResult();
    }

    public void afterVotingPhase() throws Throwable {
        while( Environment.untrustedInput() != 0 ) {
			int decision = Environment.untrustedInput();
            if (decision >= 0){ // the bulletin board reads a message:
				BB.onPost();
            }
			else {
            	byte[] content = BB.onRequestContent();
            	Environment.untrustedOutputMessage(content);
            }
        }
    }

}
