# A simple E-voting System

The e-voting system involves **voters**, a **collecting server**, and a
**bulletin board**.  Voters send their choices to the server via a
secure and authenticated channel implemented using the __Secure Message
Transmission__ (SMT) functionality. The server, after having received
the choices of all voters, computes the result of the election and posts
it on the bulletin board via an authenticated channel implemented using
the __Authenticated Message Transmission__ (AMT) functionality.
Everybody can now contact the bulletin board to learn the outcome of the
election.

	
## Dependencies

* Java JDK (tested with both `openjdk-7` and `oraclejdk-8`)
* Java Cryptography Extension (only needed for `oraclejdk`)
* Bouncy Castle Cryptographic API and Test Classes (tested with `{bcprov | bctest}-jdk15on-147.jar`)
* SQLJet (tested with `sqljet-1.1.6.jar`)


## Usage

 1. Run class `funct.pki.PKIServerApp`

    This starts the public key infrastructure which is needed for
    registration and lookup of public and verification keys.  The
    PKIServer stores the registered keys at %TEMP%/evoting_server.db -
    if you want to delete registered keys, you'll have to delete this
    file.

 2. Run class `eVotingVerif.apps.RegisterServer`

    This will run the registration process for the server. Server will
    register it's keys at the PKI environment and store the serialized
    keys to folder %TEMP%/smtvote

 3. Run class `eVotingVerif.apps.AppServer`

    The server will read the stored credentials and start waiting to
    receive votes.


 4. Run class `eVotingVerif.apps.AppBulletinBoard`

    This will run the bulletin board. It will keep listening for
    messages from the server and for requests for its content.

 5. Run class `eVotingVerif.apps.RegisterVoter <voter-id>` 

    In order to submit a vote, you first have to register the voter with
    parameter <voter-id> which is expected as number in range 0 to 49.
    After registration is finished, the generated keys get stored to
    folder %TEMP%/smtvote

    For sending the vote to the server, the voter has to be registered
    and the credential is expected to be stored in the folder
    %TEMP%/smtvote

 6. Run class `eVotingVerif.apps.AppVoter <vote> <voter-id>`
	
    The vote is expected as a two-digit HEX string 00 or 01, the ID is
    expected as number in range 0 to 49

    After all votes have been cast, the server automatically posts it's
    content and the result to the bulletin board and terminates.

 7. Run class `eVotingVerif.apps.AppShowOutcome`
 
    The bulletin board will send its content and the request tool will
    print this content as hex to the shell.
    
 9. Run class `eVotingSystem.apps.DeleteLocalFiles`

    To delete the local files created (e.g., the databases) which are
    stored in your %TEMP%/PKIServer.db, %TEMP%/smtvote and both the
    Collecting and Final servers' output.


## Example


Run following commands from bin-folder of the compiled project:

```
java -cp ".:../lib/*" funct.pki.PKIServerApp
java -cp ".:../lib/*" eVotingVerif.apps.RegisterServer
java -cp ".:../lib/*" eVotingVerif.apps.AppServer

java -cp ".:../lib/*" eVotingVerif.apps.AppBulletinBoard

java -cp ".:../lib/*" eVotingVerif.apps.RegisterVoter 0
java -cp ".:../lib/*" eVotingVerif.apps.AppVoter 01 0

java -cp ".:../lib/*" eVotingVerif.apps.AppShowOutcome

java -cp ".:../lib/*" eVotingVerif.apps.DeleteLocalFiles
```