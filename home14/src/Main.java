import com.oocourse.uml2.interact.AppRunner;

public class Main {
    public static void main(String[] args) throws Exception {
        AppRunner appRunner = AppRunner.newInstance(
                MyUmlGeneralInteraction.class);
        appRunner.run(args);
    }
}