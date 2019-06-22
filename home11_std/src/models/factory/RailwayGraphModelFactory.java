package models.factory;

import com.oocourse.specs3.models.Path;
import models.base.Edge;
import models.base.Node;
import models.core.PathCalculationGraphCore;

import java.util.HashMap;
import java.util.Set;

@SuppressWarnings("WeakerAccess")
public abstract class RailwayGraphModelFactory implements GraphModelFactory {
    private final PathCalculationGraphCore graphCore;
    private final HashMap<Integer, Integer> sideStartNodes;
    private final HashMap<Integer, Integer> sideEndNodes;

    protected RailwayGraphModelFactory(
            Set<? extends Path> paths, boolean initialize) {
        this.graphCore = new PathCalculationGraphCore();
        this.sideStartNodes = new HashMap<>();
        this.sideEndNodes = new HashMap<>();
        if (initialize) {
            this.init(paths);
        }
    }

    public RailwayGraphModelFactory(Set<? extends Path> paths) {
        this(paths, true);
    }

    protected abstract int getSwitchWeight(Node node);

    protected abstract int getEdgeWeight(Node fromNode, Node toNode);

    protected void init(Set<? extends Path> paths) {
        this.graphCore.clear();
        this.sideStartNodes.clear();
        this.sideEndNodes.clear();
        int maxNodeId = 0;
        for (Path path : paths) {
            HashMap<Integer, Integer> currentNodeIds = new HashMap<>();
            Integer lastNodeId = null;
            Integer lastNewNodeId = null;
            for (Integer currentNodeId : path) {
                if (!sideStartNodes.containsKey(currentNodeId)) {
                    maxNodeId += 1;
                    sideStartNodes.put(currentNodeId, maxNodeId);
                }
                int startNodeId = sideStartNodes.get(currentNodeId);

                if (!sideEndNodes.containsKey(currentNodeId)) {
                    maxNodeId += 1;
                    sideEndNodes.put(currentNodeId, maxNodeId);
                }
                int endNodeId = sideEndNodes.get(currentNodeId);

                if (!currentNodeIds.containsKey(currentNodeId)) {
                    maxNodeId += 1;
                    currentNodeIds.put(currentNodeId, maxNodeId);
                }
                int currentNewNodeId = currentNodeIds.get(currentNodeId);

                this.graphCore.addEdge(new Edge(
                        new Node(currentNewNodeId), new Node(startNodeId)), 0
                );
                this.graphCore.addEdge(new Edge(
                        new Node(endNodeId), new Node(currentNewNodeId)), 0
                );
                this.graphCore.addEdge(
                        new Edge(new Node(startNodeId), new Node(endNodeId)),
                        this.getSwitchWeight(new Node(currentNodeId))
                );
                if (lastNewNodeId != null) {
                    int weight = this.getEdgeWeight(
                            new Node(lastNodeId), new Node(currentNodeId)
                    );
                    this.graphCore.addDoubleEdge(
                            new Edge(new Node(lastNewNodeId),
                                    new Node(currentNewNodeId)), weight
                    );
                }
                lastNodeId = currentNodeId;
                lastNewNodeId = currentNewNodeId;
            }
        }
    }

    public void reset(Set<? extends Path> paths) {
        this.init(paths);
    }

    public Integer getShortestPath(Node fromNode, Node toNode) {
        Integer startNodeId = this.sideEndNodes
                .getOrDefault(fromNode.getId(), null);
        Integer endNodeId = this.sideStartNodes
                .getOrDefault(toNode.getId(), null);
        if (startNodeId == null || endNodeId == null) {
            return null;
        }

        Node startNode = new Node(startNodeId);
        Node endNode = new Node(endNodeId);
        return this.graphCore.getShortestPath(startNode, endNode);
    }
}
