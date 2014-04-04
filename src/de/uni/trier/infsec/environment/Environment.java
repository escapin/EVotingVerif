package de.uni.trier.infsec.environment;

public final class Environment {

	private static boolean result; // the LOW variable
    private static int[] input = {1,7,2}; // an example only; the information-flow property should hold for all possible values
    private static int counter = 0;

    public static int untrustedInput() {
        if (counter >= input.length)
            return 0;
        else
            return input[counter++];
	}
	
    public static void untrustedOutput(int x) {
		if (untrustedInput()==0) {
			result = (x==untrustedInput());
			throw new Error();  // abort
		}
	}

    public static int untrustedInput(int n) {
        int a;
        do {
            a = untrustedInput();
        } while (a<0 || a>=n);
        return a;
	}
    
    public static byte[] untrustedInputMessage() {
		int len = untrustedInput();
		if (len<0) return null;
		byte[] returnval = new byte[len];
		for (int i = 0; i < len; i++) {
			returnval[i] = (byte) Environment.untrustedInput();
		}
		return returnval;    
    }

    public static String untrustedInputString() {
    	return untrustedInputMessage().toString();
    }


    public static void untrustedOutputMessage(byte[] t) {
    	untrustedOutput(t.length);
		for (int i = 0; i < t.length; i++) {
			untrustedOutput(t[i]);
		}
    }

    
    public static void untrustedOutputString(String s) {
    	untrustedOutput(s.length());
    	for (int i = 0; i < s.length(); i++) {
    		untrustedOutput((int)s.charAt(i));
    	}
    }
}        
