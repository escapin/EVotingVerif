package de.uni.trier.infsec.protocols.trivvoting;

import de.uni.trier.infsec.functionalities.amt.ideal.AMT;
import de.uni.trier.infsec.functionalities.samt.ideal.SAMT;


/**
 *
 * @author christoph
 */
public class Adversary {
    	public final SAMT.AgentProxy samt_proxy;
        public final AMT.AgentProxy amt_proxy;
        public final SAMT.Channel channel_to_server;
	public final AMT.Channel channel_to_BB;

        public Adversary() {
                samt_proxy = SAMT.register(Identifiers.ADVERSARY_ID);
                channel_to_server = samt_proxy.channelTo(Identifiers.SERVER_ID);
                amt_proxy = AMT.register(Identifiers.ADVERSARY_ID);
                channel_to_BB = amt_proxy.channelTo(Identifiers.BULLETIN_BOARD_ID);
        }
}
