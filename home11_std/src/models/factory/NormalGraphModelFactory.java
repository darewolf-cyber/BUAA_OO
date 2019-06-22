package models.factory;

import com.oocourse.specs3.models.Path;
import models.base.Edge;
import models.base.Node;
import models.core.PathCalculationGraphCore;

import java.util.Set;

public class NormalGraphModelFactory implements GraphModelFactory {
    private final PathCalculationGraphCore graphCore;

    public NormalGraphModelFactory(Set<? extends Path> paths) {
        this.graphCore = new PathCalculationGraphCore();
        this.init(paths);
    }

    private void init(Set<? extends Path> paths) {
        this.graphCore.clear();
        for (Path path : paths) {
            Node lastNode = null;
            for (Integer nodeId : path) {
                Node node = new Node(nodeId);

                if (lastNode != null) {
                    this.graphCore.addDoubleEdge(new Edge(lastNode, node), 1);
                }
                lastNode = node;
            }
        }
    }

    public void reset(Set<? extends Path> paths) {
        this.init(paths);
    }

    public Integer getShortestPath(Node fromNode, Node toNode) {
        return this.graphCore.getShortestPath(fromNode, toNode);
    }
}
