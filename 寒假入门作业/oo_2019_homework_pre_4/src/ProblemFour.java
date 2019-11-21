import java.math.BigInteger;
import java.util.Scanner;

public class ProblemFour {
    public static void main(String[] args) {
        Scanner in = new Scanner(System.in);
        String str = in.nextLine();
        String strMovedSpace = str.replaceAll(" ","");
        String strMerged = strMovedSpace.replaceAll("\\+\\+|--","+");
        strMerged = strMerged.replaceAll("\\+-|-\\+","-");
        strMerged = "0" + strMerged;
        String[] strs = strMerged.split("-|\\+");
        //for (String  s : strs) {
        //    System.out.println(s);
        //}
        char[] chs = new char[100009];
        int i = 0;
        for (char c : strMerged.toCharArray()) {
            if (c == '+' || c == '-') {
                chs[i++] = c;
            }
        }
        //System.out.println(chs);
        BigInteger a = new BigInteger(strs[0]);
        for (int j = 1; j < strs.length; j++) {
            BigInteger b = new BigInteger(strs[j]);
            if (chs[j - 1] == '+') {
                a = a.add(b);
            }
            else if (chs[j - 1] == '-') {
                a = a.subtract(b);
            }
        }
        System.out.println(a);
    }
}
