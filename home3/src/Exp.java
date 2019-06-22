import java.math.BigInteger;
import java.util.ArrayList;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

public class Exp {
    private ArrayList<Term> list = new ArrayList<>();

    static final String strNum = "[+-]?\\d+";
    static final String strPower = "x(\\^[+-]?\\d+)?";
    static final String strTri = "(sin|cos)\\([x#]\\)(\\^[+-]?\\d+)?";
    static final String strSin = "sin\\([x#]\\)(\\^[+-]?\\d+)?";
    static final String strCos = "cos\\([x#]\\)(\\^[+-]?\\d+)?";
    static final String strFactor = "(" + strTri + "|" + strPower +
            "|" + "%" + "|" + strNum + ")";
    static final String strTerm = "[+-]?" + strFactor +
            "(\\*" + strFactor + ")*+";
    static final String strOp = "(?<=\\d|%|x|\\))[-+]";
    static final String strExp = "\\s*[+-]?" + strTerm +
            "(" + strOp + strTerm + ")*+";
    static final String sinCos = "(sin|cos)\\(";

    public Exp() { }

    public ArrayList<Term> diff(int l,int r) {
        StringBuilder sb = new StringBuilder(Main.getStr().substring(l,r + 1));
        int last = l;
        int len = 0;
        int[] expfac = new int[200];
        int[] sincos = new int[200];
        int ef = 0;
        int sc = 0;
        Matcher maSinCos = Pattern.compile(sinCos).matcher(Main.getStr());
        for (int i = l;i <= r;i++) {
            if (Main.getPoi(i) != -1) {
                if (maSinCos.find(last) && maSinCos.end() - 1 == i) {
                    if (Main.getStr().charAt(maSinCos.end()) == 'x'
                            && Main.getStr().charAt(maSinCos.end() + 1)
                            == ')') { //..
                    }
                    else {
                        sb.replace(i + 1 - len - l,Main.getPoi(i) - len - l,
                                "#");
                        len += (Main.getPoi(i) - i - 2);
                        sincos[sc++] = i;
                    }
                }
                else {
                    sb.replace(i - len - l,Main.getPoi(i) + 1 - len - l,"%");
                    len += (Main.getPoi(i) - i);
                    expfac[ef++] = i;
                }
                last = Main.getPoi(i);
                i = last;
            }
        }
        //System.out.println(sb);
        Matcher maTerm = Pattern.compile(strTerm).matcher(sb);
        Matcher maOp = Pattern.compile(strOp).matcher(sb);
        if (maTerm.find()) {
            Term t;
            if (maTerm.start() == 1) {
                t = new Term(maTerm.group(),sb.charAt(0),expfac,sincos,ef,sc); }
            else { t = new Term(maTerm.group(),'+',expfac,sincos,ef,sc); }
            list.addAll(t.diff());
        }
        while (maOp.find(maTerm.end())) {
            maTerm.find(maOp.end());
            Term t = new Term(maTerm.group(),maOp.group().trim().charAt(0),
                    expfac,sincos,ef,sc);
            list.addAll(t.diff());
        }
        //System.out.println("list=" + list);
        return list;
    }

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();
        for (Term t : list) {
            sb.append(t.toString());
        }
        if (sb.length() == 0) {
            return "0";
        }
        else if (sb.charAt(0) == '+') {
            return sb.substring(1);
        }
        else {
            return sb.toString();
        }
    }

    public void merge() {
        int i;
        for (i = 0;i < list.size();i++) {
            if (list.get(i).getCoff().compareTo(BigInteger.ZERO) > 0) {
                break;
            }
        }
        if (i != 0 && i != list.size()) {
            Term t = list.get(0);
            list.set(0,list.get(i));
            list.set(i,t);
        }
        for (Term t : list) {
            for (Term s : list) {
                if (t == s) {
                    continue;
                }
                else {
                    if (t.compareTwo(s)) {
                        t.setCoff(t.getCoff().add(s.getCoff()));
                        s.setCoff(BigInteger.ZERO);
                    }
                }
            }
        }
    }
}
