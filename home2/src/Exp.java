import java.math.BigInteger;
import java.util.HashMap;
import java.util.Map;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

public class Exp {
    private HashMap<HashMap<Func,BigInteger>, BigInteger> map;

    // use to merge cos^2+sin^2=1
    private HashMap<Func,BigInteger> c2 = new HashMap<>();
    private HashMap<Func,BigInteger> s2 = new HashMap<>();
    private HashMap<Func,BigInteger> c4 = new HashMap<>();
    private HashMap<Func,BigInteger> s4 = new HashMap<>();
    private HashMap<Func,BigInteger> con = new HashMap<>();
    private HashMap<Func,BigInteger> cs2 = new HashMap<>();

    public Exp() {
        map = null;
    }

    public Exp(int n) {
        map = new HashMap<>(n);
    }

    public void merge(Matcher m,String kind,HashMap<Func,BigInteger> map) {
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
            map.put(new Func(kind,"x"),t);
        }
        //t==0 sin^0=1 factor* 1*anything not use
    }

    public void parseTerm(String term, char op) {
        String s = term.replaceAll("\\s","");
        Matcher maSin = Pattern.compile(Main.strSin).matcher(s);
        Matcher maCos = Pattern.compile(Main.strCos).matcher(s);
        String strPower = "(?<!\\()x(\\^[+-]?\\d+)?";//common x not find sin(x)
        Matcher maPower = Pattern.compile(strPower).matcher(s);

        HashMap<Func,BigInteger> fmap = new HashMap<>(64); //term
        merge(maSin,"sin",fmap); //put factors to fmap
        merge(maCos,"cos",fmap);
        merge(maPower,"x",fmap);

        BigInteger t = BigInteger.ONE;
        Matcher maNum = Pattern.compile(Main.strNum).matcher(s); //all num
        String strExpon = "(?<=\\^)[+-]?\\d+"; //^+2 ^2 ^-2
        Matcher maExpon = Pattern.compile(strExpon).matcher(s);
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
            t = t.multiply(new BigInteger("-1"));
        }
        Matcher maFac = Pattern.compile(Main.strFactor).matcher(s);
        maFac.find();
        //System.out.println("fac:start=" + maFac.start());
        if (maFac.start() == 1 && s.charAt(0) == '-') {
            t = t.multiply(new BigInteger("-1"));
        }
        //System.out.println("fmap" + fmap);
        this.add(fmap,t);
        //System.out.println("map" + map);
    }

    public HashMap<HashMap<Func,BigInteger>,BigInteger> cal(
                Map.Entry<Func,BigInteger> fac,BigInteger coff) {
        HashMap<HashMap<Func,BigInteger>,BigInteger> res = new HashMap<>();
        HashMap<Func,BigInteger> m = new HashMap<>();
        if (fac.getValue().compareTo(BigInteger.ZERO) == 0) {
            res.put(m,BigInteger.ZERO);
            return res;
        }
        if (fac.getKey().getOuter() == "x") {
            if (!fac.getValue().equals(BigInteger.ONE)) {
                m.put(new Func("x", "x"),
                        fac.getValue().subtract(BigInteger.ONE));
            }
            res.put(m,fac.getValue().multiply(coff));
        }
        else if (fac.getKey().getOuter() == "sin") {
            if (!fac.getValue().equals(BigInteger.ONE)) {
                m.put(new Func("sin","x"),
                        fac.getValue().subtract(BigInteger.ONE));
            }
            m.put(new Func("cos","x"),BigInteger.ONE);
            res.put(m,fac.getValue().multiply(coff));
        }
        else if (fac.getKey().getOuter() == "cos") {
            if (!fac.getValue().equals(BigInteger.ONE)) {
                m.put(new Func("cos","x"),
                        fac.getValue().subtract(BigInteger.ONE));
            }
            m.put(new Func("sin","x"),BigInteger.ONE);
            res.put(m,fac.getValue().multiply(coff).
                    multiply(new BigInteger("-1")));
        }
        return res;
    }

    public void scannTerm(Map.Entry<HashMap<Func,BigInteger>,BigInteger> tmpE,
                          HashMap<Func,BigInteger> fm,
                          HashMap<HashMap<Func,BigInteger>, BigInteger> res) {
        for (Map.Entry<Func,BigInteger> en : tmpE.getKey().entrySet()) {
            if (fm.containsKey(en.getKey())) {
                BigInteger sum = en.getValue().add(fm.get(en.getKey()));
                if (sum.compareTo(BigInteger.ZERO) != 0) {
                    fm.put(en.getKey(),sum);
                }
                else {
                    fm.remove(en.getKey());
                }
            }
            else {
                if (en.getValue().compareTo(BigInteger.ZERO) != 0) {
                    fm.put(en.getKey(),en.getValue());
                }
            }
        }
        //System.out.println("tmpdiff=" + fm);
        if (res.containsKey(fm)) {
            res.put(fm,tmpE.getValue().add(res.get(fm)));
        }
        else {
            res.put(fm,tmpE.getValue());
        }
    }

    public HashMap<HashMap<Func,BigInteger>, BigInteger> reDiff(int n,
                     Map.Entry<HashMap<Func,BigInteger>,BigInteger> t) {
        if (n == 0) {
            HashMap<HashMap<Func,BigInteger>, BigInteger> res = new HashMap<>();
            res.put(new HashMap<Func,BigInteger>(),BigInteger.ZERO);
            return res;
        }
        else if (n == 1) {
            return cal(t.getKey().entrySet().iterator().next(),t.getValue());
        }
        else { //t is term has n factors
            // && first factor is t.getKey().entrySet().iterator().next()
            Map.Entry<Func,BigInteger> firFac =
                    t.getKey().entrySet().iterator().next();
            HashMap<HashMap<Func,BigInteger>, BigInteger>
                    tmp = cal(firFac,t.getValue());
            //System.out.println("tmp=" + tmp); //tmp has no +
            HashMap<Func,BigInteger> diff1 = new HashMap<>(t.getKey());
            diff1.remove(firFac.getKey());
            HashMap<HashMap<Func,BigInteger>,BigInteger> res = new HashMap<>();
            for (Map.Entry<HashMap<Func,BigInteger>,BigInteger> tmpE :
                                                        tmp.entrySet()) {
                scannTerm(tmpE,diff1,res);
            }
            //System.out.println("res=" + res);
            HashMap<Func,BigInteger> diff2 = new HashMap<>();
            diff2.put(firFac.getKey(),firFac.getValue());
            t.getKey().remove(firFac.getKey());
            tmp = reDiff(n - 1,t);
            //System.out.println("tmp=" + tmp);
            //System.out.println("diff2=" + diff2);
            for (Map.Entry<HashMap<Func,BigInteger>, BigInteger> tmpE :
                                                            tmp.entrySet()) {
                scannTerm(tmpE,diff2,res);
                diff2 = new HashMap<>();
                diff2.put(firFac.getKey(),firFac.getValue());
            }
            //System.out.println("diff2=" + diff2);
            //System.out.println("res=" + res);
            return res;
        }
    }

    public Exp diff() {
        Exp diff = new Exp(64);
        for (Map.Entry<HashMap<Func,BigInteger>,BigInteger> term :
                                                        map.entrySet()) {
            HashMap<HashMap<Func,BigInteger>, BigInteger> res =
                    reDiff(term.getKey().size(),term);
            //System.out.println("term_diff=" + res);
            for (Map.Entry<HashMap<Func,BigInteger>,BigInteger> termRes :
                                                        res.entrySet()) {
                diff.add(termRes.getKey(),termRes.getValue());
            }
        }
        return diff;
    }

    public void add(HashMap<Func,BigInteger> fm,BigInteger c) {
        if (map.containsKey(fm)) {
            BigInteger sum = c.add(map.get(fm));
            if (sum.compareTo(BigInteger.ZERO) != 0) {
                map.put(fm,sum);
            }
            else {
                map.remove(fm);
            }
        }
        else {
            if (c.compareTo(BigInteger.ZERO) != 0) {
                map.put(fm,c);
            }
        }
    }

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder("");
        for (Map.Entry<HashMap<Func,BigInteger>,BigInteger> term :
                                                        map.entrySet()) {
            BigInteger tmp = term.getValue();
            if (tmp.compareTo(BigInteger.ZERO) == 0) {
                continue;
            }
            if (term.getKey().size() == 0) { // const term
                if (tmp.compareTo(BigInteger.ZERO) > 0) {
                    sb.append("+");
                }
                sb.append(tmp);
                continue;
            }
            if (tmp.compareTo(BigInteger.ZERO) > 0) {
                sb.append("+");
                if (tmp.compareTo(BigInteger.ONE) != 0) {
                    sb.append(tmp);
                    sb.append("*");
                }
            }
            else {
                if (tmp.compareTo(new BigInteger("-1")) != 0) {
                    sb.append(tmp);
                    sb.append("*");
                }
                else {
                    sb.append("-");
                }
            }
            sb = appendFac(term,sb);
        }
        if (sb.length() == 0) {
            return "0";
        }
        else if (sb.charAt(0) == '+') {
            return sb.substring(1);
        }
        else if (sb.charAt(0) == '-' && sb.toString().indexOf('+') != -1) {
            sb.append(sb.substring(0,sb.toString().indexOf('+')));
            return sb.substring(sb.toString().indexOf('+') + 1);
        }
        else {
            return sb.toString();
        }
    }

    public StringBuilder appendFac(Map.Entry<HashMap<Func,BigInteger>,
                BigInteger> term,  StringBuilder sb) {
        for (Map.Entry<Func,BigInteger> fac : term.getKey().entrySet()) {
            BigInteger expon = fac.getValue();
            if (expon.compareTo(BigInteger.ZERO) == 0) {
                if (sb.charAt(sb.length() - 1) != '*'
                        && term.getKey().size() == 0) {
                    sb.append("1");
                    sb.append("*");
                }
                continue;
            }
            sb.append(fac.getKey());
            if (expon.compareTo(BigInteger.ONE) != 0) {
                sb.append("^");
                sb.append(expon);
            }
            sb.append("*");
        }
        if (sb.charAt(sb.length() - 1) == '*') {
            sb.delete(sb.length() - 1,sb.length()); //delete last *
        }
        return sb;
    }

    public void simplifyC4S4(BigInteger bc4,BigInteger bs4,BigInteger bcs2,
                           BigInteger bc2,BigInteger bs2) {
        if (bc4.multiply(bs4).compareTo(BigInteger.ZERO) > 0 && bcs2 != null) {
            if (bc4.compareTo(BigInteger.ZERO) > 0 &&
                    bcs2.compareTo(BigInteger.ZERO) > 0) {
                BigInteger min = bc4.min(bs4);
                min = min.min(bcs2.divide(new BigInteger("2")));
                this.add(s4,min.negate());
                this.add(c4,min.negate());
                this.add(cs2,min.multiply(new BigInteger("-2")));
                this.add(con,min);
                //System.out.println("77" + map);
            }
            else if (bc4.compareTo(BigInteger.ZERO) < 0 &&
                    bcs2.compareTo(BigInteger.ZERO) < 0) {
                BigInteger max = bc4.max(bs4);
                max = max.max(bcs2.divide(new BigInteger("2")));
                this.add(s4,max.negate());
                this.add(c4,max.negate());
                this.add(cs2,max.multiply(new BigInteger("-2")));
                this.add(con,max);
                //System.out.println("88" + map);
            }
        }
        else if (bc4.multiply(bs4).compareTo(BigInteger.ZERO) < 0) {
            int flag = 0;
            if (bc4.add(bs4).compareTo(BigInteger.ZERO) == 0) {
                flag = 1;
            }
            if (bc2 != null && bc2.compareTo(BigInteger.ZERO) != 0) {
                flag = 1;
            }
            if (bs2 != null && bs2.compareTo(BigInteger.ZERO) != 0) {
                flag = 1;
            }
            if (flag == 1) {
                if (bc4.abs().compareTo(bs4.abs()) > 0) {
                    this.add(s2,bs4);
                    this.add(c2,bs4.negate());
                    this.add(c4,bs4);
                    map.remove(s4);
                    //System.out.println("55" + map);
                }
                else {
                    this.add(c2,bc4);
                    this.add(s2,bc4.negate());
                    this.add(s4,bc4);
                    map.remove(c4);
                    //System.out.println("66" + map);
                }
            }
        }
    }

    public void simplifyC2S2(BigInteger bc2,BigInteger bs2) {
        if (bc2.multiply(bs2).compareTo(BigInteger.ZERO) > 0) {
            if (bc2.compareTo(BigInteger.ZERO) > 0) {
                BigInteger min = bc2.min(bs2);
                this.add(c2,min.negate());
                this.add(s2,min.negate());
                this.add(con,min);
                //System.out.println("11" + map);
            }
            else {
                BigInteger max = bc2.max(bs2);
                this.add(c2,max.negate());
                this.add(s2,max.negate());
                this.add(con,max);
                //System.out.println("22" + map);
            }
        }
        else if (bc2.multiply(bs2).compareTo(BigInteger.ZERO) < 0) {
            if (bc2.abs().compareTo(bs2.abs()) > 0) {
                this.add(con,bs2);
                this.add(c2,bs2.negate());
                map.remove(s2);
                //System.out.println("33" + map);
            }
            else {
                this.add(con,bc2);
                this.add(s2,bc2.negate());
                map.remove(c2);
                //System.out.println("44" + map);
            }
        }
    }

    public int simplifySameCandS(BigInteger b2,BigInteger bcon) {
        int flag = 0;
        if (b2.multiply(bcon).compareTo(BigInteger.ZERO) > 0) {
            if (b2.compareTo(BigInteger.ZERO) < 0) {
                if (b2.add(bcon).abs().toString().length() <
                        bcon.toString().length()) {
                    flag = 1;
                }
            }
        }
        else {
            if (b2.add(bcon).compareTo(BigInteger.ZERO) == 0) {
                flag = 1;
            }
            if (b2.compareTo(BigInteger.ZERO) < 0) {
                if (b2.add(bcon).abs().toString().length() <
                        bcon.toString().length()) {
                    flag = 1;
                }
            }
            else {
                if (b2.add(bcon).toString().length() <
                        bcon.abs().toString().length()) {
                    flag = 1;
                }
            }
        }
        return flag;
    }

    public void simplifyC2(BigInteger bc2,BigInteger bcon) {
        int flag = simplifySameCandS(bc2,bcon);
        if (flag == 1) {
            this.add(con,bc2);
            this.add(s2,bc2.negate());
            map.remove(c2);
            //System.out.println("99" + map);
        }
    }

    public void simplifyS2(BigInteger bs2,BigInteger bcon) {
        int flag = simplifySameCandS(bs2,bcon);
        if (flag == 1) {
            this.add(con,bs2);
            this.add(c2,bs2.negate());
            map.remove(s2);
            //System.out.println("1010" + map);
        }
    }

    public void simplify() {
        c2.put(new Func("cos","x"),new BigInteger("2"));
        s2.put(new Func("sin","x"),new BigInteger("2"));
        c4.put(new Func("cos","x"),new BigInteger("4"));
        s4.put(new Func("sin","x"),new BigInteger("4"));
        cs2.put(new Func("sin","x"),new BigInteger("2"));
        cs2.put(new Func("cos","x"),new BigInteger("2"));

        BigInteger bc4 = map.get(c4);
        BigInteger bs4 = map.get(s4);
        BigInteger bcs2 = map.get(cs2);
        BigInteger bc2 = map.get(c2);
        BigInteger bs2 = map.get(s2);
        if (bc4 != null && bs4 != null) {
            simplifyC4S4(bc4,bs4,bcs2,bc2,bs2);
        }
        bc2 = map.get(c2);
        bs2 = map.get(s2);
        if (bc2 != null && bs2 != null) {
            simplifyC2S2(bc2,bs2);
        }
        bc2 = map.get(c2);
        bs2 = map.get(s2);
        BigInteger bcon = map.get(con);
        if (bcon != null) {
            if (bc2 != null) {
                simplifyC2(bc2,bcon);
            }
            else if (bs2 != null) {
                simplifyS2(bs2,bcon);
            }
        }
    }
}
