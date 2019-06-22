import java.math.BigInteger;

public class Sin {
    private BigInteger expon;

    public Sin(BigInteger expon) {
        this.expon = expon;
    }

    @Override
    public String toString() {
        if (expon.compareTo(BigInteger.ZERO) != 0) {
            if (expon.compareTo(BigInteger.ONE) != 0) {
                return "sin(x)^" + expon;
            }
            else {
                return "sin(x)";
            }
        }
        else {
            return "";
        }
    }

    public Term diff() {
        if (expon.compareTo(BigInteger.ZERO) != 0) {
            if (expon.compareTo(BigInteger.ONE) != 0) {
                return new Term(new Cos(BigInteger.ONE),
                        new Sin(expon.subtract(BigInteger.ONE)),
                        null,null,null,new Constant(expon));
            }
            else {
                return new Term(new Cos(BigInteger.ONE),null,
                        null,null,null,new Constant(expon));
            }
        }
        else {
            return new Term(null,null,null,null,
                    null,new Constant(BigInteger.ZERO));
        }
    }

    public BigInteger getExpon() {
        return expon;
    }

    public boolean compareTwo(Sin t) {
        if ((t == null && this != null) || (t != null && this == null)) {
            return false;
        }
        else if (t == null && this == null) {
            return true;
        }
        else {
            return (this.expon.compareTo(t.expon) == 0);
        }
    }
}
