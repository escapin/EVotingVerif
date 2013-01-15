package de.uni.trier.infsec.environment;

//class Node {
//	int value;
//	Node next;
//	Node(int v, Node n) {
//		value = v; next = n;
//	}
//}

public class Environment {
	
//	private static boolean result; // the LOW variable
//	
//	private static Node list = null;
//	private static boolean listInitialized = false;
//		
//	private static Node initialValue() {
//		// Unknown specification of the following form:
//		// return new Node(U1, new Node(U2, ...));
//		// where U1, U2, ...Un are constant integers.
//		return new Node(1, new Node(7,null));  // just an example
//	}

    
    /*@ public static model \locset envLocs;
      @ accessible envLocs : envLocs;
      @
      @ public static model \seq envObs;
      @ accessible envObs : envLocs;
      @*/
    
    /*@ normal_behavior
      @     ensures     \new_elems_fresh(envLocs);
      @     assignable  envLocs;
//      @     respects    envObs, \result;
      @*/
    public static int untrustedInput() {
//    	if (!listInitialized) {
//    		list = initialValue();
//    	    listInitialized = true;        
//    	}
//    	if (list==null) return 0;
//    	int tmp = list.value;
//    	list = list.next;
//    	return tmp;
        return 0;
	}
		
    /*@ normal_behavior
      @     ensures     \new_elems_fresh(envLocs);
      @     assignable  envLocs;
//      @     respects    envObs, x;
      @*/
    public static void untrustedOutput(int x) {
//		if (untrustedInput()==0) {
//			result = (x==untrustedInput());
//			throw new Error();  // abort
//		}
	}
    
    /*@ normal_behavior
      @     ensures     \disjoint(\result[*], Environment.envLocs);
      @     ensures     \new_elems_fresh(Environment.envLocs);
      @     assignable  Environment.envLocs;
      @*/
    public static byte[] untrustedInputMessage() {
		int len = untrustedInput();
		if (len<0) return new byte[0];
		byte[] returnval = new byte[len];
		return untrustedInputMessage_helper(returnval);    
    }
    
    /*@ normal_behavior
      @     requires    \disjoint(returnval[*], Environment.envLocs);
      @     ensures     \disjoint(\result[*], Environment.envLocs);
      @     ensures     \new_elems_fresh(Environment.envLocs);
      @     assignable  Environment.envLocs, returnval[*];
      @*/
    private static byte[] untrustedInputMessage_helper(byte[] returnval) {
        /*@ loop_invariant  0 <= i && i <= returnval.length;
          @ loop_invariant  \disjoint(returnval[*], Environment.envLocs);
          @ loop_invariant  \new_elems_fresh(Environment.envLocs);
          @ assignable      Environment.envLocs, returnval[*];
          @ decreases       returnval.length - i;
          @*/
		for (int i = 0; i < returnval.length; i++) {
			returnval[i] = (byte) Environment.untrustedInput();
		}
		return returnval;    
    }
    
    
    /*@ normal_behavior
      @     requires    \disjoint(t[*], Environment.envLocs);
      @     ensures     \new_elems_fresh(Environment.envLocs);
      @     assignable  Environment.envLocs;
      @*/
    public static void untrustedOutputMessage(byte[] t) {
    	untrustedOutput(t.length);
        untrustedOutputMessage_helper(t);
    }
    
    /*@ normal_behavior
      @     requires    \disjoint(t[*], Environment.envLocs);
      @     ensures     \new_elems_fresh(Environment.envLocs);
      @     assignable  Environment.envLocs;
      @*/
    private static void untrustedOutputMessage_helper(byte[] t) {
        /*@ loop_invariant  0 <= i && i <= t.length;
          @ loop_invariant  \disjoint(t[*], Environment.envLocs);
          @ loop_invariant  \new_elems_fresh(Environment.envLocs);
          @ assignable      Environment.envLocs;
          @ decreases       t.length - i;
          @*/
        for (int i = 0; i < t.length; i++) {
			untrustedOutput(t[i]);
		}
    }
    
    
}        
