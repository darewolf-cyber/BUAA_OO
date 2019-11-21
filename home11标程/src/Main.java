import com.oocourse.specs3.AppRunner;
import utils.MyPath;
import utils.MyRailwaySystem;

public class Main {
    public static void main(String[] args) throws Exception {
        AppRunner runner = AppRunner.newInstance(
                MyPath.class, MyRailwaySystem.class);
        runner.run(args);
    }
}
