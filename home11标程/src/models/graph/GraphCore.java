package models.graph;

import models.base.Edge;
import models.base.Node;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Set;

public abstract class GraphCore {
    private final HashMap<Node, HashSet<Node>> edgeSet;
    private final HashMap<Edge, Integer> weight;

    public GraphCore() {
        this.edgeSet = new HashMap<>();
        this.weight = new HashMap<>();
    }

    public Integer getEdgeWeight(Edge edge) {
        return this.weight.getOrDefault(edge, null);
    }

    public boolean containsEdge(Edge edge) {
        return this.getEdgeWeight(edge) != null;
    }

    private void addSingleEdge(Edge edge) {
        Node fromNode = edge.getFromNode();
        Node toNode = edge.getToNode();
        if (!this.edgeSet.containsKey(fromNode)) {
            this.edgeSet.put(fromNode, new HashSet<>());
        }
        HashSet<Node> nodeSet = this.edgeSet.get(fromNode);
        nodeSet.add(toNode);
    }

    public void addEdge(Edge edge, int weight) {
        if (this.containsEdge(edge)) {
            this.weight.put(edge, Math.min(weight, this.getEdgeWeight(edge)));
        } else {
            this.addSingleEdge(edge);
            this.weight.put(edge, weight);
        }
    }

    private void removeSingleEdge(Edge edge) {
        Node fromNode = edge.getFromNode();
        Node toNode = edge.getToNode();
        if (this.edgeSet.containsKey(fromNode)) {
            HashSet<Node> nodeSet = this.edgeSet.get(fromNode);
            nodeSet.remove(toNode);
        }
    }

    public void removeEdge(Edge edge) {
        this.removeSingleEdge(edge);
        this.weight.remove(edge);
    }

    public Set<Node> getTargetNodeSet(Node fromNode) {
        Set<Node> set = this.edgeSet.getOrDefault(fromNode, null);
        if (set == null) {
            set = new HashSet<>();
        }
        return set;
    }

    public void clear() {
        this.edgeSet.clear();
        this.weight.clear();
    }
}
