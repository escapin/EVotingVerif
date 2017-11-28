package eVotingVerif.apps;

import eVotingVerif.core.Params;
import funct.pki.PKI;
import lib.network.NetworkClient;
import lib.network.NetworkError;
import utils.Utilities;

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
