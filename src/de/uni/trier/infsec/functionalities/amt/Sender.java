package de.uni.trier.infsec.functionalities.amt;

import de.uni.trier.infsec.environment.Environment;
import de.uni.trier.infsec.environment.AMTEnv;
import de.uni.trier.infsec.functionalities.amt.AMT.LogEntry;
import de.uni.trier.infsec.functionalities.smt.SMT;
import de.uni.trier.infsec.lib.network.NetworkClient;
import de.uni.trier.infsec.lib.network.NetworkError;
import de.uni.trier.infsec.utils.MessageTools;

public class Sender 
{
	public final int id;

    /*@ ensures \new_elems_fresh(SMT.rep);
      @ diverges true;
      @ assignable \set_union(SMT.rep, \singleton(Environment.counter));
      @ helper
      @*/
	public void sendTo(byte[] message, int receiver_id, String server, int port) throws AMTError, ConnectionError {
		if (AMT.registrationInProgress) throw new AMTError();

		// get from the simulator a message to be later sent out
		byte[] output_message = AMTEnv.sendTo(MessageTools.copyOf(message), id, receiver_id, server, port);
		// log the sent message along with the sender and receiver identifiers			
		AMT.log.add(new LogEntry(MessageTools.copyOf(message), id, receiver_id));
		// sent out the message from the simulator
		try {
			NetworkClient.send(output_message, server, port);
		}
		catch (NetworkError e) {
			throw new ConnectionError();
		}
	}

	Sender(int id) {
		this.id = id;
	}
}