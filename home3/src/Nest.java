import java.math.BigInteger;
import java.util.ArrayList;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

public class Nest {
    private String outer;
    private BigInteger expon;
    private int inPoi;

    public Nest(String outer, BigInteger expon,int innerPoi) {
        this.outer = outer;
        this.expon = expon;
        this.inPoi = innerPoi;
    }

    @Override
    public String toString() {
        String inner = Main.getStr().substring(inPoi,Main.getPoi(inPoi - 1));
        if (expon.compareTo(BigInteger.ZERO) != 0) {
            Matcher m1 = Pattern.compile(Main.strFacDouble).matcher(inner);
            Matcher m2 = Pattern.compile(Main.strExpDouble).matcher(inner);
            if (m1.matches()) {
                inner = m1.group(1);
            }
            else if (m2.matches()) {
                inner = m2.group(1);
            }
            if (expon.compareTo(BigInteger.ONE) != 0) {
                return outer + "(" + inner + ")^" + expon;
            }
            else {
                return outer + "(" + inner + ")";
            }
        }
        else {
            return "";
        }
    }

    public ArrayList<Term> diff() {
        Exp p = new Exp();
        ArrayList<Term> l = p.diff(inPoi,Main.getPoi(inPoi - 1) - 1);
        Term t = null;
        if (outer.compareTo("sin") == 0) {
            Nest[] ns = new Nest[3];
            ns[0] = new Nest("cos",BigInteger.ONE,inPoi);
            if (expon.compareTo(BigInteger.ONE) != 0) {
                ns[1] = new Nest("sin",expon.subtract(BigInteger.ONE),inPoi);
            }
            t = new Term(null,null,null,null, ns,new Constant(expon));
        }
        else if (outer.compareTo("cos") == 0) {
            Nest[] ns = new Nest[3];
            ns[0] = new Nest("sin",BigInteger.ONE,inPoi);
            if (expon.compareTo(BigInteger.ONE) != 0) {
                ns[1] = new Nest("cos",expon.subtract(BigInteger.ONE),inPoi);
            }
            t = new Term(null,null,null,null, ns,new Constant(expon.negate()));
        }
        for (Term tmp : l) {
            tmp = tmp.merge(t);
        }
        return l;
    }

    public String getOuter() {
        return outer;
    }

    public BigInteger getExpon() {
        return expon;
    }

    public int getInnerPoi() {
        return inPoi;
    }

    public boolean compareTwo(Nest t) {
        if ((t == null && this != null) || (t != null && this == null)) {
            return false;
        }
        else if (t == null && this == null) {
            return true;
        }
        else {
            return ((this.expon.compareTo(t.expon) == 0) &&
                    (this.inPoi == t.inPoi || Main.getStr().substring(
                            this.inPoi,Main.getPoi(this.inPoi - 1))
                            .compareTo(Main.getStr().substring(t.inPoi,
                                    Main.getPoi(t.inPoi - 1))) == 0) &&
                    (this.outer.compareTo(t.outer) == 0));
        }
    }
}
