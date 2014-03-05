Prerequisites:

	*	Java 1.7 SDK

	*	To run this project within the Oracle (previously Sun) distribution of Java,
		you need to download and install:
		
			Java Cryptography Extension (JCE) Unlimited Strength Jurisdiction Policy Files
	
		For instance, see at the bottom of this page:
	 			http://www.oracle.com/technetwork/java/javase/downloads/index.html
	
	*	On the other hand, OpenJDK does not require special handling of the JCE policy files 
		since it is open source and therefore not export-restricted in the United States.
	

How-To run the E-voting System process:

 1. Run class de.uni.trier.infsec.functionalities.pki.PKIServerApp

    This starts the public key environment which is needed for
    registration and lookup of public and verification keys.  The
    PKIServer stores the registered keys at %TEMP%/evoting_server.db -
    if you want to delete registered keys, you'll have to delete this
    file.

 2. Run class de.uni.trier.infsec.eVotingVerif.apps.RegisterServer

    This will run the servers registration process. Server will
    register it's keys at the PKI environment and store the serialized
    keys to folder %TEMP%/smtvote

 3. Run class de.uni.trier.infsec.eVotingVerif.apps.AppServer

    The server will read the stored credentials and start listening for votes


 4. Run class de.uni.trier.infsec.eVotingVerif.apps.AppBulletinBoard

    This will run the bulletin board. It will keep listening for
    messages from the server and for requests for its content

6.1. Run class de.uni.trier.infsec.eVotingVerif.apps.RegisterVoter

  	In order to submit a vote, you first have to register the voter
    by running class de.uni.trier.infsec.protocols.smt_voting.VoterRegisterStandalone
    with parameter <voter-id> which is expected as number in range 0 to 49

**	After registration is finished, the generated keys get stored to
    folder %TEMP%/smtvote

	For sending the vote to the server, the voter has to be
    registered (6.1) and the credential is expected to be stored in the
    folder %TEMP%/smtvote

6.2	Run class de.uni.trier.infsec.eVotingVerif.apps.AppVoter
	with parameters <vote> <voter-id> 
	
	The vote is expected as a two-digit HEX string 00 or 01, the
    ID is expected as number in range 0 to 49

**	After all votes have been cast, the server automatically posts
    it's content and the result to the bulletin board and terminates.

 7. Run class de.uni.trier.infsec.eVotingVerif.apps.AppShowOutcome
 
    The bulletin board will send its content and the request tool will
    print this content as hex to the shell.
    
 9. Run class de.uni.trier.infsec.eVotingSystem.apps.DeleteLocalFiles
    In order to delete local files created (e.g. the databases) which are stored
    in your %TEMP%/PKIServer.db, %TEMP%/smtvote and both the Collecting and Final servers' output


EXAMPLE:
========

Run following commands from bin-folder of the compiled project:

1. java -cp ".:../lib/*" de.uni.trier.infsec.functionalities.pki.PKIServerApp
2. java -cp ".:../lib/*" de.uni.trier.infsec.eVotingVerif.apps.RegisterServer
3. java -cp ".:../lib/*" de.uni.trier.infsec.eVotingVerif.apps.AppServer

4. java -cp ".:../lib/*" de.uni.trier.infsec.eVotingVerif.apps.AppBulletinBoard

5.1. java -cp ".:../lib/*" de.uni.trier.infsec.eVotingVerif.apps.RegisterVoter 0
5.2. java -cp ".:../lib/*" de.uni.trier.infsec.eVotingVerif.apps.AppVoter 01 0

6. java -cp ".:../lib/*" de.uni.trier.infsec.eVotingVerif.apps.AppShowOutcome

7. java -cp ".:../lib/*" de.uni.trier.infsec.eVotingVerif.apps.DeleteLocalFiles
