import java.math.BigInteger;
import java.util.Scanner;
import java.util.regex.Pattern;

public class ProblemTwo {
    public static void main(String[] args) {
        Scanner in = new Scanner(System.in);
        String str = in.nextLine();
        String[] strs = str.split("\\s+");
        if (strs.length != 2) {
            System.out.println("WRONG FORMAT!");
            return;
        }
        String pattern = "[-+]?\\d+";
        Pattern r = Pattern.compile(pattern);
        BigInteger[] big = new BigInteger[3];
        for (int i = 0; i < strs.length; i++) {
            //System.out.println(strings[i]);
            if (!r.matcher(strs[i]).matches()) {
                System.out.println("WRONG FORMAT!");
                return;
            }
            big[i] = new BigInteger(strs[i]);
        }
        System.out.println(big[0].add(big[1]));
    }
}
