package utils;

import com.oocourse.specs3.models.NodeIdNotFoundException;
import com.oocourse.specs3.models.NodeNotConnectedException;
import com.oocourse.specs3.models.Path;
import com.oocourse.specs3.models.RailwaySystem;
import models.base.Node;
import models.factory.GraphModelFactory;
import models.factory.PleasantGraphModelFactory;
import models.factory.SimpleRailwayGraphModelFactory;

import java.util.HashSet;

public class MyRailwaySystem extends MyGraph implements RailwaySystem {
    private final GraphModelFactory transferGraphFactory;
    private final GraphModelFactory ticketGraphFactory;
    private final GraphModelFactory pleasantGraphFactory;
    private Integer blockCount;

    public MyRailwaySystem() {
        super();
        this.transferGraphFactory = new SimpleRailwayGraphModelFactory(
                getPathSet(), 0, 1);
        this.ticketGraphFactory = new SimpleRailwayGraphModelFactory(
                getPathSet(), 1, 2);
        this.pleasantGraphFactory = new PleasantGraphModelFactory(getPathSet());
        this.blockCount = null;
    }

    @Override
    protected void structureChangedEvent() {
        super.structureChangedEvent();
        this.transferGraphFactory.reset(getPathSet());
        this.ticketGraphFactory.reset(getPathSet());
        this.pleasantGraphFactory.reset(getPathSet());
        this.blockCount = null;
    }

    public int getLeastTicketPrice(int fromNodeId, int toNodeId)
            throws NodeIdNotFoundException, NodeNotConnectedException {
        getPathPretreated(fromNodeId, toNodeId);
        Node fromNode = new Node(fromNodeId);
        Node toNode = new Node(toNodeId);

        return this.ticketGraphFactory.getShortestPath(fromNode, toNode);
    }

    public int getLeastTransferCount(int fromNodeId, int toNodeId)
            throws NodeIdNotFoundException, NodeNotConnectedException {
        getPathPretreated(fromNodeId, toNodeId);
        Node fromNode = new Node(fromNodeId);
        Node toNode = new Node(toNodeId);

        return this.transferGraphFactory.getShortestPath(fromNode, toNode);
    }

    @Override
    public int getUnpleasantValue(Path path, int fromNodeId, int toNodeId) {
        return 0;
    }

    public int getLeastUnpleasantValue(int fromNodeId, int toNodeId)
            throws NodeIdNotFoundException, NodeNotConnectedException {
        getPathPretreated(fromNodeId, toNodeId);
        Node fromNode = new Node(fromNodeId);
        Node toNode = new Node(toNodeId);

        return this.pleasantGraphFactory.getShortestPath(fromNode, toNode);
    }

    public int getConnectedBlockCount() {
        if (this.blockCount == null) {
            HashSet<Integer> colors = new HashSet<>();
            for (Node node : this.getNodeSet()) {
                int color = this.getNodeColor(node);
                colors.add(color);
            }
            this.blockCount = colors.size();
        }
        return this.blockCount;
    }
}
