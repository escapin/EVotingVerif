package de.uni.trier.infsec.utils;

public class MessageTools {
	
	public static byte[] copyOf(byte[] message) {
		if (message==null) return null;
		byte[] copy = new byte[message.length];
		for (int i = 0; i < message.length; i++) {
			copy[i] = message[i];
		}
		return copy;
	}

	public static byte[] concatenate(byte[] m1, byte[] m2) {
		byte[] out = new byte[m1.length + m2.length + 4]; // we allocate 4 additional bytes for the length of m1
		byte[] len = intToByteArray(m1.length);

		// copy all bytes to the output array
		int j = 0;
		for( int i=0; i<len.length; ++i ) out[j++] = len[i]; // the length of m1
		for( int i=0; i<m1.length;  ++i ) out[j++] = m1[i];  // m1
		for( int i=0; i<m2.length;  ++i ) out[j++] = m2[i];  // m2

		return out;
	}

	public static final byte[] intToByteArray(int value) {
	        return new byte[] {
	                (byte)(value >>> 24),
	                (byte)(value >>> 16),
	                (byte)(value >>> 8),
	                (byte)value};
	}
}
