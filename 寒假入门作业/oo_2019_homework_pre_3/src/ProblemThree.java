import java.math.BigInteger;
import java.util.Scanner;

public class ProblemThree {
    public static void main(String[] args) {
        Scanner in = new Scanner(System.in);
        int inA = in.nextInt();
        BigInteger a = in.nextBigInteger(inA);
        int inB = in.nextInt();
        BigInteger b = in.nextBigInteger(inB);
        int inC = in.nextInt();
        BigInteger c = a.add(b);
        System.out.println(c.toString(inC));
    }
}
