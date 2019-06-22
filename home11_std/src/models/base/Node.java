package models.base;

import java.util.Arrays;

/**
 * 节点对象
 */
public class Node {
    private final int id;

    public Node(int id) {
        this.id = id;
    }

    public int getId() {
        return id;
    }

    @Override
    public int hashCode() {
        return Arrays.hashCode(new Object[]{this.getId()});
    }

    @Override
    public boolean equals(Object obj) {
        if (obj == this) {
            return true;
        } else if (obj instanceof Node) {
            return ((Node) obj).getId() == this.getId();
        } else {
            return false;
        }
    }

    @Override
    public String toString() {
        return "models.base.Node{" +
                "id=" + id +
                '}';
    }
}
