package utils;

import com.oocourse.specs3.models.Graph;
import com.oocourse.specs3.models.NodeIdNotFoundException;
import com.oocourse.specs3.models.NodeNotConnectedException;
import models.base.Edge;
import models.base.Node;
import models.core.ColorMapCore;
import models.factory.GraphModelFactory;
import models.factory.NormalGraphModelFactory;
import models.graph.UndirectedGraphCore;

import java.util.HashMap;

@SuppressWarnings("WeakerAccess")
public class MyGraph extends MyPathContainer implements Graph {
    private final HashMap<Edge, Integer> edgeCount;
    private final UndirectedGraphCore graph;
    private final ColorMapCore colorMapCore;
    private final GraphModelFactory distanceGraphFactory;

    public MyGraph() {
        super();
        this.edgeCount = new HashMap<>();
        this.graph = new UndirectedGraphCore();
        this.colorMapCore = new ColorMapCore(graph);
        this.distanceGraphFactory = new NormalGraphModelFactory(getPathSet());
    }

    @Override
    protected void structureChangedEvent() {
        super.structureChangedEvent();
        this.colorMapCore.clear();
        this.distanceGraphFactory.reset(getPathSet());
    }

    @Override
    protected void edgeAddEvent(Node fromNode, Node toNode) {
        super.edgeAddEvent(fromNode, toNode);
        Edge edge = new Edge(fromNode, toNode).getReversedEdgeIfReversed();
        int originalEdgeCount = this.edgeCount.getOrDefault(edge, 0);
        this.edgeCount.put(edge, originalEdgeCount + 1);
        this.graph.addEdge(edge, 1);
    }

    @Override
    protected void edgeRemoveEvent(Node fromNode, Node toNode) {
        super.edgeRemoveEvent(fromNode, toNode);
        Edge edge = new Edge(fromNode, toNode).getReversedEdgeIfReversed();
        int originalEdgeCount = this.edgeCount.getOrDefault(edge, 0);
        int newEdgeCount = originalEdgeCount - 1;
        if (newEdgeCount > 0) {
            this.edgeCount.put(edge, newEdgeCount);
        } else {
            this.edgeCount.remove(edge);
            this.graph.removeEdge(edge);
        }
    }

    public boolean containsEdge(int fromNodeId, int toNodeId) {
        Edge edge = new Edge(new Node(fromNodeId), new Node(toNodeId))
                .getReversedEdgeIfReversed();
        return this.edgeCount.containsKey(edge);
    }

    protected int getNodeColor(Node node) {
        return this.colorMapCore.getColorForNode(node);
    }

    public boolean isConnected(int fromNodeId, int toNodeId)
            throws NodeIdNotFoundException {
        Node fromNode = new Node(fromNodeId);
        if (!this.containsNode(fromNodeId)) {
            throw new NodeIdNotFoundException(fromNodeId);
        }

        Node toNode = new Node(toNodeId);
        if (!this.containsNode(toNodeId)) {
            throw new NodeIdNotFoundException(toNodeId);
        }

        return getNodeColor(fromNode) == getNodeColor(toNode);
    }

    protected void getPathPretreated(int fromNodeId, int toNodeId)
            throws NodeIdNotFoundException, NodeNotConnectedException {
        if (!this.containsNode(fromNodeId)) {
            throw new NodeIdNotFoundException(fromNodeId);
        }
        if (!this.containsNode(toNodeId)) {
            throw new NodeIdNotFoundException(toNodeId);
        }
        if (!this.isConnected(fromNodeId, toNodeId)) {
            throw new NodeNotConnectedException(fromNodeId, toNodeId);
        }
    }

    public int getShortestPathLength(int fromNodeId, int toNodeId)
            throws NodeIdNotFoundException, NodeNotConnectedException {
        getPathPretreated(fromNodeId, toNodeId);
        Node fromNode = new Node(fromNodeId);
        Node toNode = new Node(toNodeId);
        return this.distanceGraphFactory.getShortestPath(fromNode, toNode);
    }
}
