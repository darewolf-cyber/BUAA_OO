import java.math.BigInteger;
import java.util.HashMap;
import java.util.Map;

public class Poly {
    private HashMap<BigInteger,BigInteger> poly;
    private HashMap<BigInteger,BigInteger> diffPoly;

    public Poly() {
        poly = null;
        diffPoly = null;
    }

    public Poly(int n) {
        poly = new HashMap<>(n);
        diffPoly = new HashMap<>(n);
    }

    public void parsePoly(String s, char op) {
        //System.out.println("s:" + op + " " + s);
        String tmps = s.replaceAll("\\s","");
        BigInteger coff = null;
        BigInteger expon = null;
        //System.out.println("tmps:" + op + " " + tmps);
        if (tmps.indexOf('x') == -1) {
            expon = new BigInteger("0");
            coff = new BigInteger(tmps);
        }
        else {
            if (tmps.indexOf('^') != -1) {
                expon = new BigInteger(tmps.substring(tmps.indexOf('^') + 1));
            }
            else {
                expon = new BigInteger("1");
            }
            if (tmps.indexOf('*') != -1) {
                coff = new BigInteger(tmps.substring(0,tmps.indexOf('*')));
            }
            else {
                if (tmps.charAt(0) == '+' || tmps.charAt(0) == '-') {
                    coff = new BigInteger(tmps.charAt(0) + "1");
                }
                else {
                    coff = new BigInteger("1");
                }
            }
        }
        if (op == '-') {
            coff = new BigInteger("0").subtract(coff);
        }
        if (poly.containsKey(expon)) {
            poly.put(expon,coff.add(poly.get(expon)));
        }
        else {
            poly.put(expon,coff);
        }
    }

    public void diffe() {
        for (Map.Entry<BigInteger,BigInteger> entry : poly.entrySet()) {
            //System.out.println(entry.getValue() + " " + entry.getKey());
            if (entry.getKey().compareTo(new BigInteger("0")) != 0) {
                diffPoly.put(entry.getKey().subtract(new BigInteger("1")),
                        entry.getValue().multiply(entry.getKey()));
            }
            else {
                diffPoly.put(new BigInteger("0"),new BigInteger("0"));
            }
        }
        //for (Map.Entry<BigInteger,BigInteger> entry : diffPoly.entrySet()) {
        //    System.out.println(entry.getValue() + " " + entry.getKey());
        //}
    }

    @Override
    public String toString() {
        StringBuilder str = new StringBuilder();
        for (Map.Entry<BigInteger,BigInteger> entry : diffPoly.entrySet()) {
            if (entry.getKey().compareTo(new BigInteger("0")) == 0) {
                if (entry.getValue().compareTo(new BigInteger("0")) > 0) {
                    str.append("+");
                    str.append(entry.getValue());
                }
                else if (entry.getValue().compareTo(new BigInteger("0")) < 0) {
                    str.append(entry.getValue());
                }
            }
            else {
                if (entry.getValue().compareTo(new BigInteger("0")) > 0) {
                    str.append("+");
                    if (entry.getValue().compareTo(new BigInteger("1")) != 0) {
                        str.append(entry.getValue());
                        str.append("*x");
                    }
                    else {
                        str.append("x");
                    }
                    if (entry.getKey().compareTo(new BigInteger("1")) != 0) {
                        str.append("^");
                        str.append(entry.getKey());
                    }
                }
                else if (entry.getValue().compareTo(new BigInteger("0")) < 0) {
                    if (entry.getValue().compareTo(new BigInteger("-1")) != 0) {
                        str.append(entry.getValue());
                        str.append("*x");
                    }
                    else {
                        str.append("-x");
                    }
                    if (entry.getKey().compareTo(new BigInteger("1")) != 0) {
                        str.append("^");
                        str.append(entry.getKey());
                    }
                }
            }
        }
        if (str.toString().length() == 0) {
            return "0";
        }
        else if (str.charAt(0) == '+') {
            return str.substring(1);
        }
        else if (str.charAt(0) == '-' && str.toString().indexOf('+') != -1) {
            str.append(str.substring(0,str.toString().indexOf('+')));
            return str.substring(str.toString().indexOf('+') + 1);
        }
        else {
            return str.toString();
        }
    }

}
