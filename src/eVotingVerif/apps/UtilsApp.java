package eVotingVerif.apps;


import java.io.ByteArrayOutputStream;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileOutputStream;
import java.io.IOException;


public class UtilsApp 
{
	public static void storeAsFile(byte[] data, String sFile) throws IOException {
		File f = new File(sFile);
		File fdir = f.getParentFile();
		
		if (f.exists()) f.delete();
		fdir.mkdir();
		f.createNewFile();

		FileOutputStream file = new FileOutputStream(f);
		file.write(data);
		file.flush();
		file.close();
	}

	public static byte[] readFromFile(String path) throws IOException {
		FileInputStream f = new FileInputStream(path);
		ByteArrayOutputStream bos = new ByteArrayOutputStream();
		while (f.available() > 0){			
			bos.write(f.read());
		}
		f.close();
		byte[] data = bos.toByteArray();
		return data;
	}


	public static void deleteFile(String filename) {
		File f = new File(filename);
		if (f.exists()) f.delete();
		
	}
}
