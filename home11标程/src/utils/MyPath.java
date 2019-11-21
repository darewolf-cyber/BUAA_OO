package utils;

import com.oocourse.specs3.models.Path;
import models.base.Node;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;

@SuppressWarnings("Duplicates")
public class MyPath implements Path {
    private final ArrayList<Node> nodes;
    private final HashSet<Node> nodeHashSet;

    public MyPath() {
        this.nodes = new ArrayList<>();
        this.nodeHashSet = new HashSet<>();
    }

    public MyPath(int... nodeList) {
        this();
        for (int node : nodeList) {
            appendNode(node);
        }
    }

    private void appendNode(Integer nodeId) {
        Node node = new Node(nodeId);
        nodes.add(node);
        nodeHashSet.add(node);
    }

    public int size() {
        return this.nodes.size();
    }

    @Override
    public int getDistinctNodeCount() {
        return nodeHashSet.size();
    }

    public int getNode(int index) {
        return this.nodes.get(index).getId();
    }

    @Override
    public boolean containsNode(int i) {
        Node node = new Node(i);
        return this.nodeHashSet.contains(node);
    }

    @Override
    public int hashCode() {
        return Arrays.hashCode(this.nodes.toArray());
    }

    private boolean equals(MyPath path) {
        return compareTo(path) == 0;
    }

    @Override
    public boolean equals(Object obj) {
        if (this == obj) {
            return true;
        } else if (obj instanceof MyPath) {
            return this.equals((MyPath) obj);
        } else {
            return false;
        }
    }

    private ArrayList<Integer> getIntegerNodeList() {
        ArrayList<Integer> list = new ArrayList<>();
        for (Node node : this.nodes) {
            list.add(node.getId());
        }
        return list;
    }

    @Override
    public Iterator<Integer> iterator() {
        return getIntegerNodeList().iterator();
    }

    @Override
    public String toString() {
        StringBuilder builder = new StringBuilder();
        builder.append("Path(");
        int size = this.size();
        for (int i = 0; i < size; i++) {
            builder.append(this.getNode(i));
            if (i < size - 1) {
                builder.append(", ");
            }
        }
        builder.append(")");
        return builder.toString();
    }

    @Override
    public int compareTo(Path o) {
        int minSize = Math.min(this.size(), o.size());
        for (int i = 0; i < minSize; i++) {
            int compare = Integer.compare(this.getNode(i), o.getNode(i));
            if (compare != 0) {
                return compare;
            }
        }
        return Integer.compare(this.size(), o.size());
    }

    @Override
    public boolean isValid() {
        return this.size() >= 2;
    }

    private static final HashMap<Integer, Integer> hFunction =
            new HashMap<Integer, Integer>() {{
                put(0, 1);
                put(1, 4);
                put(2, 16);
                put(3, 64);
                put(4, 256);
            }};

    @Override
    public int getUnpleasantValue(int i) {
        return hFunction.get((i % 5 + 5) % 5);
    }
}
