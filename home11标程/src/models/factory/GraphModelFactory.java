package models.factory;

import com.oocourse.specs3.models.Path;
import models.base.Node;

import java.util.Set;

public interface GraphModelFactory {
    void reset(Set<? extends Path> paths);

    Integer getShortestPath(Node fromNode, Node toNode);
}
