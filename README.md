# A simple E-voting System

The e-voting system involves **voters**, a **collecting server**, and a
**bulletin board**.  Voters send their choices to the server via a
secure and authenticated channel implemented using the _Secure Message
Transmission_ (SMT) functionality. The server, after having received
the choices of all voters, computes the result of the election and posts
it on the bulletin board via an authenticated channel implemented using
the _Authenticated Message Transmission_ (AMT) functionality.
Everybody can now contact the bulletin board to learn the outcome of the
election.

	
## Dependencies

* Java JDK (tested with both `openjdk-7` and `oraclejdk-8`)
* Java Cryptography Extension (only needed for `oraclejdk`)
* Bouncy Castle Cryptographic API and Test Classes (tested with `{bcprov | bctest}-jdk15on-147.jar`)
* SQLJet (tested with `sqljet-1.1.6.jar`)


## Usage

 1. Run class `funct.pki.PKIServerApp`

    This class handles the public key infrastructure which is needed for
    registration and lookup of public and verification keys.  The
    PKIServer stores the registered keys in the
    `%TEMP%/evoting_server.db` folder.
    
    If you want to delete registered keys, you'll have to delete this
    file.

 2. Run class `eVotingVerif.apps.RegisterServer`

    This class runs the registration process for the collecting
    server. The collecting server registers its public keys at the PKI
    environment and stores the serialized keys in the `%TEMP%/smtvote`
    folder.

 3. Run class `eVotingVerif.apps.AppServer`

    The collecting server reads the stored credentials and starts
    collecting votes.


 4. Run class `eVotingVerif.apps.AppBulletinBoard`

    This bulletin board listens for messages from the server and for
    requests for its content.

 5. Run class `eVotingVerif.apps.RegisterVoter <voter-id>` 

    In order to submit a vote, you first have to register the voter with
    parameter <voter-id> which is expected as number in the range 0 to
    49.  After the registration is finished, the generated keys are
    stored in the `%TEMP%/smtvote` folder.

    For sending a vote to the server, the voter has to be registered and
    her credentials are stored in the `%TEMP%/smtvote` folder.

 6. Run class `eVotingVerif.apps.AppVoter <vote> <voter-id>`
	
    The vote is a two-digit HEX string 00 or 01, while the voter ID is
    as number between 0 and 49.

    After all the votes have been cast, the server automatically posts
    all the votes and the result of the election to the bulletin board.
  

 7. Run class `eVotingVerif.apps.AppShowOutcome`
 
    The class retreive from the bulletin board the result of the
    election and publish it.
    
 9. Run class `eVotingSystem.apps.DeleteLocalFiles`

    To delete the local files in `%TEMP%/PKIServer.db` and in
    `%TEMP%/smtvote` and the output of both the Collecting Server and
    the Bulletin Board.


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