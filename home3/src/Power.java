import java.math.BigInteger;

public class Power {
    private BigInteger expon;

    public Power(BigInteger expon) {
        this.expon = expon;
    }

    @Override
    public String toString() {
        if (expon.compareTo(BigInteger.ZERO) != 0) {
            if (expon.compareTo(BigInteger.ONE) != 0) {
                return "x^" + expon;
            }
            else {
                return "x";
            }
        }
        else {
            return "";
        }
    }

    public Term diff() {
        if (expon.compareTo(BigInteger.ZERO) != 0) {
            if (expon.compareTo(BigInteger.ONE) != 0) {
                return new Term(null,null,
                        new Power(expon.subtract(BigInteger.ONE)),
                        null,null,new Constant(expon));
            }
            else {
                return new Term(null,null,null,
                        null,null,new Constant(expon));
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

    public boolean compareTwo(Power t) {
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
