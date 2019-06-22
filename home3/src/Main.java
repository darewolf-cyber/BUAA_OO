import java.util.LinkedList;
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
    static final String strExpon = "(?<=\\^)[+-]?\\d+";
    static final String sinCos = "(sin|cos)\\s*\\(";

    static final String fac = "((sin|cos)\\(x\\)(\\^[+-]?\\d+)?|" +
            "x(\\^[+-]?\\d+)?|[+-]?\\d+)";
    static final String strFacDouble = "\\(+" + fac + "\\)+";
    static final String strterm = "[+-]?" + fac + "(\\*" + fac + ")*+";
    static final String op = "(?<=\\d|\\s|x|\\))[-+]";
    static final String exp = "[+-]?" + strterm + "(" + op + strterm + ")*+";
    static final String strExpDouble = "\\(+(\\(" + exp + "\\))\\)+";

    private static int[] poi;
    private static String str;

    public static int getPoi(int i) {
        return poi[i];
    }

    public static String getStr() {
        return str;
    }

    public static void calPoi(String str) {
        for (int i = 0;i < poi.length;i++) {
            poi[i] = -1;
        }
        LinkedList<Integer> stack = new LinkedList<>();
        for (int i = 0;i < str.length();i++) {
            if (str.charAt(i) == '(') {
                stack.push(i);
            }
            else if (str.charAt(i) == ')') {
                if (stack.isEmpty()) {
                    wrongFormat();
                }
                else {
                    poi[stack.pop()] = i;
                }
            }
        }
        if (!stack.isEmpty()) {
            wrongFormat();
        }
        //for (int i = 0;i < poi.length;i++) {
        //    if (poi[i] != -1) {
        //        System.out.println(i + " " + poi[i]);
        //    }
        //}
    }

    public static void reParse(int l,int r,int kind) {
        StringBuilder sb = new StringBuilder(str.substring(l,r + 1));
        int[] expfac = new int[200];
        int[] sincos = new int[200];
        int ef = 0;
        int sc = 0;
        int last = l;
        int len = 0;
        Matcher maSinCos = Pattern.compile(sinCos).matcher(str);
        Matcher maadd = Pattern.compile("[+-]").matcher(str);
        for (int i = l;i <= r;i++) {
            if (poi[i] != -1) {
                if (maSinCos.find(last) && maSinCos.end() - 1 == i) {
                    sb.replace(i + 1 - len - l,poi[i] - len - l,"x");
                    len += (poi[i] - i - 2);
                    sincos[sc++] = i;
                }
                else {
                    if (maadd.find(last) && maadd.start() < i && kind == 1) {
                        wrongFormat();
                    }
                    sb.replace(i - len - l,poi[i] + 1 - len - l,"1");
                    len += (poi[i] - i);
                    expfac[ef++] = i;
                }
                last = poi[i];
                i = last;
            }
        }
        //System.out.println(sb);
        if (kind == 0) {
            Matcher maExp = Pattern.compile(strExp).matcher(sb);
            if (!maExp.matches()) {
                wrongFormat();
            }
        }
        else if (kind == 1) {
            Matcher maFac = Pattern.compile(strFactor + "\\s*").matcher(sb);
            if (!maFac.matches()) {
                wrongFormat();
            }
        }
        for (int i = 0;i < ef;i++) {
            reParse(expfac[i] + 1,poi[expfac[i]] - 1,0);
        }
        for (int i = 0;i < sc;i++) {
            reParse(sincos[i] + 1,poi[sincos[i]] - 1,1);
        }
    }

    public static void main(String[] args) {
        try {
            Scanner in = new Scanner(System.in);
            if (!in.hasNextLine()) {
                wrongFormat();
            }
            str = in.nextLine();
            Matcher maLegal = Pattern.compile(strLegal).matcher(str);
            if (maLegal.find()) {
                wrongFormat();
            }
            poi = new int[200];
            calPoi(str);
            reParse(0, str.length() - 1, 0);
            str = str.replaceAll("\\s", "");
            Matcher maExpon = Pattern.compile(strExpon).matcher(str);
            while (maExpon.find()) {
                if (maExpon.group().length() <= 6) {
                    if (Integer.parseInt(maExpon.group()) > 10000) {
                        wrongFormat();
                    }
                } else {
                    wrongFormat();
                }
            }
            calPoi(str); //remove space make poi change
            Exp e = new Exp();
            e.diff(0, str.length() - 1);
            e.merge();
            System.out.println(e.toString());
        }
        catch (Exception e) {
            wrongFormat();
        }
    }
}
