import java.util.Scanner;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

public class Main {

    public static void main(String[] args) {
        final String strLegal = "[\\r\\n\\f\\v]";
        //final String strNum = "[+-]?\\d+";
        //final String strPower = "\\s*x\\s*(\\^\\s*[+-]?\\d+)?";
        final String strTerm = "(?<=[-+]|^|\\s)" +
                "((((\\s*[+-]?\\d+\\s*\\*)|\\s*\\+|\\s*-)?\\s*x\\s*" +
                "(\\^\\s*[+-]?\\d+)?\\s*)|(\\s*[+-]?\\d+\\s*))";
        final String strOp = "(?<=\\d|\\s|x)[-+]";
        final String strExp = "\\s*[+-]?\\s*" + strTerm +
                "\\s*(" + "\\s*" + strOp + "\\s*" + strTerm + "\\s*)*+\\s*";

        Scanner in = new Scanner(System.in);
        String str = in.nextLine();
        Matcher maLegal = Pattern.compile(strLegal).matcher(str);
        if (maLegal.find()) {
            System.out.println("WRONG FORMAT!");
            System.exit(0);
        }
        Matcher maExp = Pattern.compile(strExp).matcher(str);
        if (!maExp.matches()) {
            System.out.println("WRONG FORMAT!");
            System.exit(0);
        }
        str = str.trim();
        Matcher maTerm = Pattern.compile(strTerm).matcher(str);
        if (!maTerm.find()) { //first term
            System.out.println("WRONG FORMAT!");
            System.exit(0);
        }
        else if (maTerm.start() >= 2 ||
                    (maTerm.start() == 1 &&
                            str.charAt(0) != '+' && str.charAt(0) != '-')) {
            System.out.println("WRONG FORMAT!");
            System.exit(0);
        }
        Poly po = new Poly(2048);
        if (maTerm.start() == 1) {
            po.parsePoly(maTerm.group(), str.charAt(0));
        }
        else {
            po.parsePoly(maTerm.group(), '+');
        }
        Matcher maOp = Pattern.compile(strOp).matcher(str);
        while (maOp.find(maTerm.end())) {
            if (maTerm.find(maOp.end())) {
                po.parsePoly(maTerm.group().trim(),
                        maOp.group().trim().charAt(0));
            }
        }
        po.diffe();
        System.out.print(po.toString());
    }
}
