package eVotingVerif.apps;


import java.io.File;

import eVotingVerif.core.BulletinBoard;
import eVotingVerif.core.Params;
import funct.amt.AMT.AMTError;
import funct.pki.PKI;
import lib.network.NetworkServer;

public class AppBulletinBoard {

	// public static final String PATH = System.getProperty("java.io.tmpdir") + File.separator + "smtvote" + File.separator + "bulletinBoard.amt";
	
	public static void main(String[] args) {
		//System.setProperty("remotemode", Boolean.toString(true));
		PKI.useRemoteMode();
		run();
	}

	static BulletinBoard bb;
	
	private static void run() {
		try {
			bb = new BulletinBoard();
			
			
			NetworkServer.listenForRequests(Params.LISTEN_PORT_BBOARD_REQUEST);
			System.out.println("Bulletin Board: ready to collect election outcome...");
			while (true) {							
				bb.onPost();
				
				try {					
					byte[] req = NetworkServer.nextRequest(Params.LISTEN_PORT_BBOARD_REQUEST);
					// if (req == null || req.length == 0){ 
					if(req!=null && req.length!=0){
						NetworkServer.response(bb.onRequestContent());
						System.out.println("Election outcome requested.");
					}
				} catch (Exception e) {
					e.printStackTrace();
				}
				Thread.sleep(500);
			}
		} catch (AMTError e) {
			e.printStackTrace();
		} catch (Exception e) {
			e.printStackTrace();
		}
	}
	
	
}
