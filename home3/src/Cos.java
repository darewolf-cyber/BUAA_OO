import java.math.BigInteger;

public class Cos {
    private BigInteger expon;

    public Cos(BigInteger expon) {
        this.expon = expon;
    }

    @Override
    public String toString() {
        if (expon.compareTo(BigInteger.ZERO) != 0) {
            if (expon.compareTo(BigInteger.ONE) != 0) {
                return "cos(x)^" + expon;
            }
            else {
                return "cos(x)";
            }
        }
        else {
            return "";
        }
    }

    public Term diff() {
        if (expon.compareTo(BigInteger.ZERO) != 0) {
            if (expon.compareTo(BigInteger.ONE) != 0) {
                return new Term(new Cos(expon.subtract(BigInteger.ONE)),
                        new Sin(BigInteger.ONE), null,null,
                        null,new Constant(expon.negate()));
            }
            else {
                return new Term(null, new Sin(BigInteger.ONE),
                        null,null, null,new Constant(expon.negate()));
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

    public boolean compareTwo(Cos t) {
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
