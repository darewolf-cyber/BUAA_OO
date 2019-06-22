package models.factory;

import com.oocourse.specs3.models.Path;
import models.base.Node;

import java.util.HashMap;
import java.util.Set;

public class PleasantGraphModelFactory
        extends RailwayGraphModelFactory implements GraphModelFactory {

    private static final int SWITCH_WEIGHT = 32;
    private static HashMap<Integer, Integer> nodeWeights =
            new HashMap<Integer, Integer>() {{
                put(4, 256);
                put(0, 1);
                put(1, 4);
                put(2, 16);
                put(3, 64);
            }};

    public PleasantGraphModelFactory(Set<Path> paths) {
        super(paths);
    }

    private int getNodeWeight(Node node) {
        int category = (node.getId() % 5 + 5) % 5;
        return nodeWeights.get(category);
    }

    @Override
    protected int getEdgeWeight(Node fromNode, Node toNode) {
        return Math.max(getNodeWeight(fromNode), getNodeWeight(toNode));
    }

    @Override
    protected int getSwitchWeight(Node node) {
        return SWITCH_WEIGHT;
    }
}
