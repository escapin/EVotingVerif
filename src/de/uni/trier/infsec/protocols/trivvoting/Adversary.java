package de.uni.trier.infsec.protocols.trivvoting;

import de.uni.trier.infsec.functionalities.samt.ideal.SAMT;


/**
 *
 * @author christoph
 */
public class Adversary {
    	public final SAMT.AgentProxy proxy;
	public final SAMT.Channel channel_to_server;
	public final SAMT.Channel channel_to_BB;

        public Adversary() {
                proxy = SAMT.register(Identifiers.ADVERSARY_ID);
                channel_to_server = proxy.channelTo(Identifiers.SERVER_ID);
                channel_to_BB = proxy.channelTo(Identifiers.BULLETIN_BOARD_ID);
        }
}
