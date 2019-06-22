import com.oocourse.specs1.models.Path;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Set;

public class MyPath implements Path {
    //@ public instance model non_null int[] nodes;
    private ArrayList<Integer> path;
    private int disNum;

    public MyPath(int... nodeList) {
        path = new ArrayList<>();
        for (int i = 0;i < nodeList.length;i++) {
            path.add(nodeList[i]);
        }
        disNum = -1;
    }

    @Override
    //@ ensures \result == nodes.length;
    public /*@pure@*/int size() {
        return path.size();
    }

    @Override
    /*@ requires index >= 0 && index < size();
      @ assignable \nothing;
      @ ensures \result == nodes[index];
      @*/
    public /*@pure@*/ int getNode(int index) {
        return path.get(index);
    }

    @Override
    //@ ensures \result == (\exists int i; 0 <= i &&
    //@ i < nodes.length; nodes[i] == node);
    public /*@pure@*/ boolean containsNode(int node) {
        return path.contains(node);
    }

    @Override
    /*@ ensures \result == (\num_of int i, j; 0 <= i && i < j
                && j < nodes.length;nodes[i] != nodes[j]);
      @*/
    public /*pure*/ int getDistinctNodeCount() {
        if (disNum == -1) {
            Set<Integer> set = new HashSet<>();
            set.addAll(path);
            disNum = set.size();
        }
        return disNum;
    }

    @Override
    //@ ensures \result == (nodes.length >= 2);
    public /*@pure@*/ boolean isValid() {
        return path.size() >= 2;
    }

    /*@ also
      @ public normal_behavior
      @ requires obj != null && obj instanceof Path;
      @ assignable \nothing;
      @ ensures \result == ((Path) obj).nodes.length == nodes.length) &&
      @                      (\forall int i; 0 <= i && i < nodes.length;
      @                           nodes[i] == ((Path) obj).nodes[i]);
      @ also
      @ public normal_behavior
      @ requires obj == null || !(obj instanceof Path);
      @ assignable \nothing;
      @ ensures \result == false;
      @*/
    public boolean equals(Object obj) {
        if (obj == null || !(obj instanceof Path)) {
            return false;
        }
        else {
            if (path.size() != ((Path) obj).size()) {
                return false;
            }
            boolean flag = true;
            for (int i = 0;i < path.size(); i++) {
                if (path.get(i) != ((Path) obj).getNode(i)) {
                    flag = false;
                    break;
                }
            }
            return flag;
        }
    }

    @Override
    public int compareTo(Path o) {
        for (int i = 0;i < Math.min(path.size(),o.size()); i++) {
            if (path.get(i) < o.getNode(i)) {
                return -1;
            }
            else if (path.get(i) > o.getNode(i)) {
                return 1;
            }
        }
        return path.size() - o.size();
    }

    @Override
    public Iterator<Integer> iterator() {
        return path.iterator();
    }

    @Override
    public int hashCode() {
        return path.hashCode();
    }
}
