package models.core;

import models.base.Edge;
import models.base.Node;
import models.graph.DirectedGraphCore;

import java.util.HashSet;
import java.util.LinkedList;
import java.util.Queue;

public class PathCalculationGraphCore extends DirectedGraphCore {
    private final DirectedGraphCore pathCache;
    private final HashSet<Node> calculatedFromNodes;

    public PathCalculationGraphCore() {
        super();
        this.pathCache = new DirectedGraphCore();
        this.calculatedFromNodes = new HashSet<>();
    }

    @Override
    public void addEdge(Edge edge, int weight) {
        super.addEdge(edge, weight);
        this.pathCache.addEdge(edge, weight);
    }

    @Override
    public void removeEdge(Edge edge) {
        super.removeEdge(edge);
        this.pathCache.removeEdge(edge);
    }

    @Override
    public void clear() {
        super.clear();
        this.clearCache();
    }

    public void clearCache() {
        this.pathCache.clear();
        this.calculatedFromNodes.clear();
    }

    public synchronized Integer getShortestPath(Node fromNode, Node toNode) {
        if (this.calculatedFromNodes.contains(fromNode)) {
            return this.pathCache.getEdgeWeight(new Edge(fromNode, toNode));
        }

        Queue<Node> queue = new LinkedList<>();
        queue.offer(fromNode);
        HashSet<Node> isInQueue = new HashSet<>();
        isInQueue.add(fromNode);
        HashSet<Node> isNotFirstTime = new HashSet<>();
        isNotFirstTime.add(fromNode);
        this.pathCache.addEdge(new Edge(fromNode, fromNode), 0);

        while (!queue.isEmpty()) {
            Node headNode = queue.peek();
            int headNodeWeight = this.pathCache
                    .getEdgeWeight(new Edge(fromNode, headNode));
            for (Node nextNode : this.pathCache.getTargetNodeSet(headNode)) {
                int nextWeight = this.pathCache
                        .getEdgeWeight(new Edge(headNode, nextNode));
                Integer nextNodeOriginalWeight = this.pathCache
                        .getEdgeWeight(new Edge(fromNode, nextNode));
                int nextNodeWeight = headNodeWeight + nextWeight;

                if (!isNotFirstTime.contains(nextNode) ||
                        ((nextNodeOriginalWeight == null) ||
                                (nextNodeOriginalWeight > nextNodeWeight))) {
                    this.pathCache.addEdge(
                            new Edge(fromNode, nextNode), nextNodeWeight);
                    if (!isInQueue.contains(nextNode)) {
                        queue.offer(nextNode);
                        isInQueue.add(nextNode);
                    }
                    isNotFirstTime.add(nextNode);
                }
            }
            queue.poll();
            isInQueue.remove(headNode);
        }

        this.calculatedFromNodes.add(fromNode);
        return this.pathCache.getEdgeWeight(new Edge(fromNode, toNode));
    }
}
