import com.oocourse.specs3.AppRunner;

public class Main {
    static int cnt=0;
    public static void main(String[] args) throws Exception {
        //long before = System.currentTimeMillis();
        AppRunner runner = AppRunner.newInstance(
                MyPath.class, MyRailwaySystem.class);
        runner.run(args);
        //long after = System.currentTimeMillis();
        //System.err.println(after - before+"ms");
        System.err.println(cnt);
    }
}