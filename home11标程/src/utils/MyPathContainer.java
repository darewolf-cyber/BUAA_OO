package utils;

import com.oocourse.specs3.models.Path;
import com.oocourse.specs3.models.PathContainer;
import com.oocourse.specs3.models.PathIdNotFoundException;
import com.oocourse.specs3.models.PathNotFoundException;
import models.base.Node;

import java.util.HashMap;
import java.util.Set;

@SuppressWarnings({"WeakerAccess", "BooleanMethodIsAlwaysInverted"})
public class MyPathContainer implements PathContainer {
    private final HashMap<Node, Integer> nodeCount;
    private final HashMap<Integer, Path> pathIdMap;
    private final HashMap<Path, Integer> pathMap;
    private int maxId;

    public MyPathContainer() {
        this.maxId = 0;
        this.pathMap = new HashMap<>();
        this.pathIdMap = new HashMap<>();
        this.nodeCount = new HashMap<>();
    }

    public int size() {
        return this.pathMap.size();
    }

    public boolean containsPath(Path path) {
        return this.pathMap.containsKey(path);
    }

    public boolean containsPathId(int pathId) {
        return this.pathIdMap.containsKey(pathId);
    }

    public Path getPathById(int pathId) throws PathIdNotFoundException {
        if (this.pathIdMap.containsKey(pathId)) {
            return this.pathIdMap.get(pathId);
        } else {
            throw new PathIdNotFoundException(pathId);
        }
    }

    protected Set<Path> getPathSet() {
        return this.pathMap.keySet();
    }

    protected Set<Node> getNodeSet() {
        return this.nodeCount.keySet();
    }

    protected void nodeAddEvent(Node node) {
        int originalNodeCount = this.nodeCount.getOrDefault(node, 0);
        this.nodeCount.put(node, originalNodeCount + 1);
    }

    protected void nodeRemoveEvent(Node node) {
        int originalNodeCount = this.nodeCount.getOrDefault(node, 0);
        int newNodeCount = originalNodeCount - 1;
        if (newNodeCount > 0) {
            this.nodeCount.put(node, newNodeCount);
        } else {
            this.nodeCount.remove(node);
        }
    }

    protected void edgeAddEvent(Node fromNode, Node toNode) {
        // pass
    }

    protected void edgeRemoveEvent(Node fromNode, Node toNode) {
        // pass
    }

    protected void structureChangedEvent() {
        // pass
    }

    @Override
    public int getPathId(Path path) throws PathNotFoundException {
        if (this.pathMap.containsKey(path)) {
            return this.pathMap.get(path);
        } else {
            throw new PathNotFoundException(path);
        }
    }

    public int addPath(Path path) {
        try {
            return this.getPathId(path);
        } catch (PathNotFoundException e) {  // path not exist
            this.maxId += 1;
            this.pathMap.put(path, this.maxId);
            this.pathIdMap.put(this.maxId, path);
            Node lastNode = null;
            for (Integer nodeId : path) {
                Node node = new Node(nodeId);

                nodeAddEvent(node);
                if (lastNode != null) {
                    edgeAddEvent(lastNode, node);
                }
                lastNode = node;
            }
            structureChangedEvent();
            return this.maxId;
        }
    }

    public int removePath(Path path) throws PathNotFoundException {
        if (containsPath(path)) {
            int pathId = this.pathMap.get(path);
            this.pathMap.remove(path);
            this.pathIdMap.remove(pathId);
            Node lastNode = null;
            for (Integer nodeId : path) {
                Node node = new Node(nodeId);

                nodeRemoveEvent(node);
                if (lastNode != null) {
                    edgeRemoveEvent(lastNode, node);
                }
                lastNode = node;
            }
            structureChangedEvent();
            return pathId;
        } else {
            throw new PathNotFoundException(path);
        }
    }

    public void removePathById(int pathId) throws PathIdNotFoundException {
        try {
            Path path = getPathById(pathId);
            removePath(path);
        } catch (PathNotFoundException e) {
            throw new PathIdNotFoundException(pathId);
        }
    }

    public int getDistinctNodeCount() {
        return this.nodeCount.size();
    }

    public boolean containsNode(int nodeId) {
        return this.nodeCount.containsKey(new Node(nodeId));
    }
}
