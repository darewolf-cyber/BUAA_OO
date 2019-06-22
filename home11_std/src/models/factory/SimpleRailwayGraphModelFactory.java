package models.factory;

import com.oocourse.specs3.models.Path;
import models.base.Node;

import java.util.Set;

@SuppressWarnings("WeakerAccess")
public class SimpleRailwayGraphModelFactory
        extends RailwayGraphModelFactory implements GraphModelFactory {
    private final int stepWeight;
    private final int switchWeight;

    public SimpleRailwayGraphModelFactory(
            Set<? extends Path> paths, int stepWeight, int switchWeight) {
        super(paths, false);
        this.stepWeight = stepWeight;
        this.switchWeight = switchWeight;
        this.init(paths);
    }

    @Override
    protected int getEdgeWeight(Node fromNode, Node toNode) {
        return this.stepWeight;
    }

    @Override
    protected int getSwitchWeight(Node node) {
        return this.switchWeight;
    }
}
