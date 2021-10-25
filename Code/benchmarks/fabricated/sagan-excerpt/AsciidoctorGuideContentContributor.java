import java.io.File;
import java.io.IOException;

public class AsciidoctorGuideContentContributor {

    public String README_FILENAME = "README";

    public String getAbsolutePath() {
        return "hihi";
    }

    public void contribute() {
        File readmeAdocFile = new File(getAbsolutePath() + File.separator + README_FILENAME);
    }
}
