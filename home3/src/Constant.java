import java.math.BigInteger;

public class Constant {
    private BigInteger coff;

    public Constant(BigInteger coff) {
        this.coff = coff;
    }

    @Override
    public String toString() {
        return coff.toString();
    }

    public Term diff() {
        return new Term(null,null,null,null,
                null,new Constant(BigInteger.ZERO));
    }

    public BigInteger getCoff() {
        return coff;
    }

    public boolean compareTwo(Constant t) {
        if ((t == null && this != null) || (t != null && this == null)) {
            return false;
        }
        else if (t == null && this == null) {
            return true;
        }
        else {
            return (this.coff.compareTo(t.coff) == 0);
        }
    }
}
