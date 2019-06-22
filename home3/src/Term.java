import java.math.BigInteger;
import java.util.ArrayList;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

public class Term {
    private Cos cos;
    private Sin sin;
    private Power pow;
    private Add[] add;
    private Nest[] nest;
    private Constant con;
    private String str;
    private int addNum;
    private int nestNum;

    static final String strNum = "[+-]?\\d+";
    static final String strPower = "(?<!\\()x(\\^[+-]?\\d+)?";
    static final String strNest = "(sin|cos)\\(#\\)(\\^[+-]?\\d+)?";
    static final String strSin = "sin\\(x\\)(\\^[+-]?\\d+)?";
    static final String strCos = "cos\\(x\\)(\\^[+-]?\\d+)?";
    static final String strExpon = "(?<=\\^)[+-]?\\d+"; //^+2 ^2 ^-2
    static final String strTri = "(sin|cos)\\(x\\)(\\^[+-]?\\d+)?";
    static final String strFac = "(" + strTri + "|" + strPower
            + "|" + strNum + ")";

    public Term(Cos cos, Sin sin, Power pow, Add[] add, Nest[] nest,
                Constant con) {
        if (cos != null) {
            this.cos = new Cos(cos.getExpon());
        }
        else {
            this.cos = null;
        }
        if (sin != null) {
            this.sin = new Sin(sin.getExpon());
        }
        else {
            this.sin = null;
        }
        if (pow != null) {
            this.pow = new Power(pow.getExpon());
        }
        else {
            this.pow = null;
        }
        if (con != null) {
            this.con = new Constant(con.getCoff());
        }
        else {
            this.con = null;
        }
        int i;
        this.nest = new Nest[200];
        if (nest != null) {
            for (i = 0;i < nest.length;i++) {
                if (nest[i] == null) {
                    break;
                }
                this.nest[i] = new Nest(nest[i].getOuter(),nest[i].getExpon(),
                        nest[i].getInnerPoi());
            }
            this.nestNum = i;
        }
        else {
            this.nestNum = 0;
            this.nest = null;
        }
        this.add = new Add[200];
        if (add != null) {
            for (i = 0;i < add.length;i++) {
                if (add[i] == null) {
                    break;
                }
                this.add[i] = new Add(add[i].getStrPoi());
            }
            this.addNum = i;
        }
        else {
            this.addNum = 0;
            this.add = null;
        }
    }

    public int getAddNum() {
        return addNum;
    }

    public int getNestNum() {
        return nestNum;
    }

    public void setAddNum(int addNum) {
        this.addNum = addNum;
    }

    public void setNestNum(int nestNum) {
        this.nestNum = nestNum;
    }

    public BigInteger getCoff() { return con.getCoff(); }

    public void setCoff(BigInteger t) {
        this.con = new Constant(t);
    }

    public Term(String str,char op,int[] expfac,int[] sincos,int ef,int sc) {
        this.str = str;
        Matcher maCos = Pattern.compile(strCos).matcher(str);
        mergeCommon(maCos,1);
        Matcher maSin = Pattern.compile(strSin).matcher(str);
        mergeCommon(maSin,2);
        Matcher maPow = Pattern.compile(strPower).matcher(str);
        mergeCommon(maPow,3);
        Matcher maNum = Pattern.compile(strNum).matcher(str);
        Matcher maExpon = Pattern.compile(strExpon).matcher(str);
        mergeConstant(maNum,maExpon,op);
        Matcher maExpFac = Pattern.compile("%").matcher(str);
        mergeExpFac(maExpFac,expfac,ef);
        Matcher maNest = Pattern.compile(strNest).matcher(str);
        mergeNest(maNest,sincos,sc);
    }

    public void mergeCommon(Matcher m, int kind) {
        BigInteger t = BigInteger.ZERO;
        while (m.find()) {
            int poi = m.group().indexOf('^');
            if (poi != -1) {
                t = t.add(new BigInteger(m.group().substring(poi + 1)));
            }
            else {
                t = t.add(BigInteger.ONE);
            }
        }
        if (t.compareTo(BigInteger.ZERO) != 0) {
            switch (kind) {
                case 1 : {
                    cos = new Cos(t);
                    break;
                }
                case 2 : {
                    sin = new Sin(t);
                    break;
                }
                case 3 : {
                    pow = new Power(t);
                    break;
                }
                default: { }
            }
        }
    }

    public void mergeConstant(Matcher maNum, Matcher maExpon,char op) {
        BigInteger t = BigInteger.ONE;
        while (maNum.find()) {
            if (maExpon.find(maNum.start()) && maExpon.start() == maNum.start()
                    && maExpon.end() == maNum.end()) {
                //...
            }
            else {
                t = t.multiply(new BigInteger(maNum.group()));
            }
        }
        if (op == '-') {
            t = t.negate();
        }
        Matcher maFac = Pattern.compile(Exp.strFactor).matcher(str);
        maFac.find();
        if (maFac.start() == 1 && str.charAt(0) == '-') {
            t = t.negate();
        }
        con = new Constant(t);
    }

    public void mergeExpFac(Matcher m,int[] expfac,int ef) {
        add = new Add[200];
        int i = 0;
        while (m.find()) {
            add[i] = new Add(expfac[i] + 1);
            i++;
        }
        for (int j = 0;j < ef - i;j++) {
            expfac[j] = expfac[j + i];
        }
        addNum = i;
    }

    public void mergeNest(Matcher m,int[] sincos,int sc) {
        nest = new Nest[200];
        int i = 0;
        int truei = 0;
        while (m.find()) {
            int poi = m.group().indexOf('^');
            BigInteger t;
            if (poi != -1) {
                t = new BigInteger(m.group().substring(poi + 1));
            }
            else {
                t = BigInteger.ONE;
            }
            if (t.compareTo(BigInteger.ZERO) != 0) {
                if (m.group().charAt(0) == 's') {
                    nest[truei] = new Nest("sin",t,sincos[i] + 1);
                }
                else if (m.group().charAt(0) == 'c') {
                    nest[truei] = new Nest("cos",t,sincos[i] + 1);
                }
                truei++;  // real num of nest[] in this term
            }
            i++; // even sin(#)^0==1 but i++ to occupy ths sincos[]
        }
        for (int j = 0;j < sc - i;j++) {
            sincos[j] = sincos[j + i];
        }
        nestNum = truei;
    }

    public Term merge(Term t) {
        BigInteger tmp = BigInteger.ZERO;
        if (cos != null) {
            tmp = tmp.add(this.cos.getExpon());
        }
        if (t.cos != null) {
            tmp = tmp.add(t.cos.getExpon());
        }
        if (tmp.compareTo(BigInteger.ZERO) != 0) {
            this.cos = new Cos(tmp);
        }
        tmp = BigInteger.ZERO;
        if (sin != null) {
            tmp = tmp.add(this.sin.getExpon());
        }
        if (t.sin != null) {
            tmp = tmp.add(t.sin.getExpon());
        }
        if (tmp.compareTo(BigInteger.ZERO) != 0) {
            this.sin = new Sin(tmp);
        }
        tmp = BigInteger.ZERO;
        if (pow != null) {
            tmp = tmp.add(this.pow.getExpon());
        }
        if (t.pow != null) {
            tmp = tmp.add(t.pow.getExpon());
        }
        if (tmp.compareTo(BigInteger.ZERO) != 0) {
            this.pow = new Power(tmp);
        }
        tmp = BigInteger.ONE;
        if (con != null) {
            tmp = tmp.multiply(con.getCoff());
        }
        if (t.con != null) {
            tmp = tmp.multiply(t.con.getCoff());
        }
        this.con = new Constant(tmp); // even ==0 new too
        if (t.add != null) {
            for (int i = 0;i < t.addNum;i++) {
                if (t.add[i] != null) {
                    this.add[this.addNum++] = t.add[i];
                }
            }
        }
        if (t.nest != null) {
            for (int i = 0;i < t.nestNum;i++) {
                if (t.nest[i] != null) {
                    this.nest[this.nestNum++] = t.nest[i];
                }
            }
        }
        return this;
    }

    public ArrayList<Term> diff() {
        ArrayList<Term> l = new ArrayList<>();
        if (con.getCoff().compareTo(BigInteger.ZERO) == 0) {
            return l;
        }
        if (cos != null) {
            Term ans = new Term(null,sin,pow,add,nest,con);
            ans = ans.merge(cos.diff());
            l.add(ans);
        }
        if (sin != null) {
            Term ans = new Term(cos,null,pow,add,nest,con);
            ans = ans.merge(sin.diff());
            l.add(ans);
        }
        if (pow != null) {
            Term ans = new Term(cos,sin,null,add,nest,con);
            ans = ans.merge(pow.diff());
            l.add(ans);
        }
        for (int i = 0;i < addNum;i++) {
            Term ans = new Term(cos,sin,pow,add,nest,con);
            ans.add[i] = null;
            ArrayList<Term> tmpl = add[i].diff();
            for (Term t : tmpl) {
                t = t.merge(ans);
            }
            l.addAll(tmpl);
        }
        for (int i = 0;i < nestNum;i++) {
            Term ans = new Term(cos,sin,pow,add,nest,con);
            ans.nest[i] = null;
            ArrayList<Term> tmpl = nest[i].diff();
            for (Term t : tmpl) {
                t = t.merge(ans);
            }
            l.addAll(tmpl);
        }
        return l;
    }

    public void termString(StringBuilder sb) {
        if (con != null) {
            if (con.getCoff().compareTo(BigInteger.ZERO) > 0) {
                sb.append("+");
                if (con.getCoff().compareTo(BigInteger.ONE) != 0) {
                    sb.append(con.getCoff());
                    sb.append("*");
                }
            }
            else {
                if (con.getCoff().compareTo(new BigInteger("-1")) != 0) {
                    sb.append(con.getCoff());
                    sb.append("*");
                }
                else {
                    sb.append("-");
                }
            }
        }
        if (pow != null && pow.getExpon().compareTo(BigInteger.ZERO) != 0) {
            sb.append(pow);
            sb.append("*");
        }
        if (cos != null && cos.getExpon().compareTo(BigInteger.ZERO) != 0) {
            sb.append(cos);
            sb.append("*");
        }
        if (sin != null && sin.getExpon().compareTo(BigInteger.ZERO) != 0) {
            sb.append(sin);
            sb.append("*");
        }
        for (int i = 0;i < addNum;i++) {
            sb.append(add[i]);
            sb.append("*");
        }
        for (int i = 0;i < nestNum;i++) {
            if (nest[i].getExpon().compareTo(BigInteger.ZERO) != 0) {
                sb.append(nest[i]);
            }
            sb.append("*");
        }
        if (sb.charAt(sb.length() - 1) == '*') {
            sb.delete(sb.length() - 1,sb.length()); //delete last *
        }
    }

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();
        if (con != null && con.getCoff().compareTo(BigInteger.ZERO) == 0) {
            return "";
        }
        if (cos == null && sin == null && pow == null
                && (add == null || addNum == 0)
                && (nest == null || nestNum == 0)) {
            if (con != null) {
                if (con.getCoff().compareTo(BigInteger.ZERO) > 0) {
                    sb.append("+");
                }
                sb.append(con);
            }
        }
        else {
            termString(sb);
        }
        return sb.toString();
    }

    public boolean nullAndNull(Object o1,Object o2) {
        return ((o1 == null && o2 != null) || (o1 != null && o2 == null));
    }

    public boolean getf1(Term t) {
        if (nullAndNull(t.cos,this.cos)) { return false; }
        else if (t.cos == null && this.cos == null) { return true; }
        else { return this.cos.compareTwo(t.cos); }
    }

    public boolean getf2(Term t) {
        if (nullAndNull(t.sin,this.sin)) { return false; }
        else if (t.sin == null && this.sin == null) { return true; }
        else { return this.sin.compareTwo(t.sin); }
    }

    public boolean getf3(Term t) {
        if (nullAndNull(t.pow,this.pow)) { return false; }
        else if (t.pow == null && this.pow == null) { return true; }
        else { return this.pow.compareTwo(t.pow); }
    }

    public boolean compareTwo(Term t) {
        if (this == t) {
            return true;
        }
        boolean f5 = false;
        if (nestNum == t.nestNum) {
            f5 = true;
            for (int i = 0;i < nestNum;i++) {
                if (nullAndNull(t.nest[i],this.nest[i])) {
                    f5 = false;
                    break;
                }
                else if (t.nest[i] == null && this.nest[i] == null) {
                    f5 = true;
                }
                else {
                    f5 = this.nest[i].compareTwo(t.nest[i]);
                    if (f5 == false) {
                        break;
                    }
                }
            }
        }
        else {
            f5 = false;
        }
        boolean f6 = false;
        if (addNum == t.addNum) {
            f6 = true;
            for (int i = 0;i < addNum;i++) {
                if (nullAndNull(t.add[i],this.add[i])) {
                    f6 = false;
                    break;
                }
                else if (t.add[i] == null && this.add[i] == null) {
                    f6 = true;
                }
                else {
                    f6 = this.add[i].compareTwo(t.add[i]);
                    if (f6 == false) {
                        break;
                    }
                }
            }
        }
        else {
            f6 = false;
        }
        boolean f1 = getf1(t);
        boolean f2 = getf2(t);
        boolean f3 = getf3(t);
        return f1 && f2 && f3 && f5 && f6;
    }
}
