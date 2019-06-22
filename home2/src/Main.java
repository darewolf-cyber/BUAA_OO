import java.util.Scanner;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

public class Main {

    public static void wrongFormat() {
        System.out.println("WRONG FORMAT!");
        System.exit(0);
    }

    static final String strLegal = "[\\r\\n\\f\\v]";
    static final String strNum = "\\s*[+-]?\\d+";
    static final String strPower = "\\s*x\\s*(\\^\\s*[+-]?\\d+)?";
    static final String strTri = "\\s*(sin|cos)\\s*\\(\\s*x\\s*\\)\\s*" +
            "(\\^\\s*[+-]?\\d+)?";
    static final String strSin = "\\s*sin\\s*\\(\\s*x\\s*\\)" +
            "\\s*(\\^\\s*[+-]?\\d+)?";
    static final String strCos = "\\s*cos\\s*\\(\\s*x\\s*\\)" +
            "\\s*(\\^\\s*[+-]?\\d+)?";
    static final String strFactor = "(" + strTri + "|" + strPower
            + "|" + strNum + ")";
    static final String strTerm = "\\s*[+-]?\\s*" + strFactor +
            "\\s*(\\s*\\*" + strFactor + "\\s*)*+\\s*";
    static final String strOp = "(?<=\\d|\\s|x|\\))[-+]";
    static final String strExp = "\\s*[+-]?\\s*" + strTerm +
            "\\s*(" + "\\s*" + strOp + "\\s*" + strTerm + "\\s*)*+\\s*";

    public static void main(String[] args) {
        try {
            Scanner in = new Scanner(System.in);
            for (int i=0;i<3000;i++) {
                if (!in.hasNextLine()) {
                    wrongFormat();
                }
                String str = in.nextLine();
                //System.out.println(str);
                Matcher maLegal = Pattern.compile(strLegal).matcher(str);
                if (maLegal.find()) {
                    wrongFormat();
                }
                Matcher maExp = Pattern.compile(strExp).matcher(str);
                if (!maExp.matches()) {
                    wrongFormat();
                }
                str = str.trim();
                Exp t = new Exp(64);
                Matcher maTerm = Pattern.compile(strTerm).matcher(str);
                maTerm.find(); //first term
                //System.out.println("term:start=" + maTerm.start());
                if (maTerm.start() == 1) {
                    t.parseTerm(maTerm.group(), str.charAt(0));
                } else {
                    t.parseTerm(maTerm.group(), '+');
                }
                Matcher maOp = Pattern.compile(strOp).matcher(str);
                while (maOp.find(maTerm.end())) {
                    if (maTerm.find(maOp.end())) {
                        t.parseTerm(maTerm.group().trim(),
                                maOp.group().trim().charAt(0));
                    }
                }
                //System.out.println(t);
                //t.simplify();
                //System.out.println(t);
                Exp diffTerm = t.diff();
                diffTerm.simplify();
                System.out.println(diffTerm.toString());
            }
        }
        catch (Exception e) {
            wrongFormat();
        }
    }

}
