package de.uni.trier.infsec.eVotingVerif.apps;

import de.uni.trier.infsec.eVotingVerif.core.Params;
import de.uni.trier.infsec.functionalities.pki.PKI;
import de.uni.trier.infsec.lib.network.NetworkClient;
import de.uni.trier.infsec.lib.network.NetworkError;
import de.uni.trier.infsec.utils.Utilities;

public class AppShowOutcome {

	public static void main(String[] args) {
		PKI.useRemoteMode();
		run();
	}

	private static void run() {
		try {
			byte[] response = NetworkClient.sendRequest(new byte[] {0x01}, Params.DEFAULT_HOST_BBOARD, 
					Params.LISTEN_PORT_BBOARD_REQUEST);
			if (response != null && response.length > 0) {
				System.out.println("Received data from bulletin board:\n0x" + Utilities.byteArrayToHexString(response));
			} else {
				System.out.println("Did not receive any response from bulletin board.");
			}
		} catch (NetworkError e) {
			e.printStackTrace();
		}
	}
}
