import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;

public class FileIOExample {
    public void foo() throws IOException {
        String filename = "foo";
        File dir = File.createTempFile(filename.toUpperCase(), "zip");
        FileOutputStream stream = new FileOutputStream(dir);
    }
}
