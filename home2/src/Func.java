public class Func {
    private String outer;
    private String inner;

    public Func() {
        outer = "";
        inner = "";
    }

    public Func(String out, String in) {
        outer = out;
        inner = in;
    }

    public String getOuter() {
        return outer;
    }

    public String getInner() {
        return inner;
    }

    @Override
    public String toString() {
        if (outer == "x") {
            return "x";
        }
        else {
            return outer + "(" + inner + ")";
        }
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) {
            return true;
        }
        if (o == null || !(o instanceof Func)) {
            return false;
        }
        Func f = (Func) o;
        return f.inner == inner && f.outer == outer;
    }

    @Override
    public int hashCode() {
        final int prime = 31;
        int result = 1;
        if (inner == null) {
            result *= prime;
        }
        else {
            result = prime * result + inner.hashCode();
        }
        if (outer == null) {
            result *= prime;
        }
        else {
            result = prime * result + outer.hashCode();
        }
        return result;
    }

}
