import java.util.ArrayList;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

public class Add {
    private int strPoi;

    public Add(int strPoi) {
        this.strPoi = strPoi;
    }

    @Override
    public String toString() {
        String str = Main.getStr().substring(strPoi,Main.getPoi(strPoi - 1));
        Matcher m1 = Pattern.compile(Main.strFacDouble).matcher(str);
        Matcher m2 = Pattern.compile(Main.strExpDouble).matcher(str);
        if (m1.matches()) {
            return m1.group(1);
        }
        else if (m2.matches()) {
            return m2.group(1);
        }
        else {
            return "(" + str + ")";
        }
    }

    public ArrayList<Term> diff() {
        Exp exp = new Exp();
        return exp.diff(strPoi,Main.getPoi(strPoi - 1) - 1);
    }

    public int getStrPoi() {
        return strPoi;
    }

    public boolean compareTwo(Add t) {
        if ((t == null && this != null) || (t != null && this == null)) {
            return false;
        }
        else if (t == null && this == null) {
            return true;
        }
        else {
            return ((this.strPoi == t.strPoi) || (Main.getStr()
                    .substring(this.strPoi,Main.getPoi(strPoi - 1)).compareTo(
                            Main.getStr().substring(
                                    t.strPoi,Main.getPoi(t.strPoi - 1))
                    ) == 0));
        }
    }
}
