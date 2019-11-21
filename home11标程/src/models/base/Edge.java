package models.base;

import java.util.Arrays;

public class Edge {
    private final Node fromNode;
    private final Node toNode;

    public Edge(Node fromNode, Node toNode) {
        this.fromNode = fromNode;
        this.toNode = toNode;
    }

    public Node getFromNode() {
        return fromNode;
    }

    public Node getToNode() {
        return toNode;
    }

    public Edge getReversedEdge() {
        return new Edge(this.toNode, this.fromNode);
    }

    public Edge getReversedEdgeIfReversed() {
        if (Integer.compare(this.fromNode.getId(), this.toNode.getId()) > 0) {
            return this.getReversedEdge();
        } else {
            return this;
        }
    }

    @Override
    public int hashCode() {
        return Arrays.hashCode(new Object[]{this.fromNode, this.toNode});
    }

    @Override
    public boolean equals(Object obj) {
        if (obj == this) {
            return true;
        } else if (obj instanceof Edge) {
            return (((Edge) obj).fromNode.equals(this.fromNode) &&
                    ((Edge) obj).toNode.equals(this.toNode));
        } else {
            return false;
        }
    }

    @Override
    public String toString() {
        return "models.base.Edge{" +
                "fromNode=" + fromNode +
                ", toNode=" + toNode +
                '}';
    }
}
