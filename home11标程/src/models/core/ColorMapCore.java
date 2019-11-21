package models.core;

import models.base.Node;
import models.graph.UndirectedGraphCore;

import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.Queue;

/**
 * 图染色（联通性判断，均摊复杂度O(1)）
 */
public class ColorMapCore {
    private final UndirectedGraphCore core;
    private final HashMap<Node, Integer> colorMap;
    private int maxColorId;

    public ColorMapCore(UndirectedGraphCore core) {
        this.core = core;
        this.maxColorId = 0;
        this.colorMap = new HashMap<>();
    }

    public UndirectedGraphCore getCore() {
        return core;
    }

    private void drawColor(Node sourceNode, int colorId) {
        Queue<Node> queue = new LinkedList<>();
        queue.offer(sourceNode);

        HashSet<Node> nodeSet = new HashSet<>();
        nodeSet.add(sourceNode);
        while (!queue.isEmpty()) {
            Node fromNode = queue.poll();
            this.colorMap.put(fromNode, colorId);
            for (Node toNode : this.core.getTargetNodeSet(fromNode)) {
                if (nodeSet.contains(toNode)) {
                    continue;
                }
                queue.offer(toNode);
                nodeSet.add(toNode);
            }
        }
    }

    public int getColorForNode(Node node) {
        Integer color = this.colorMap.getOrDefault(node, null);
        if (color == null) {
            this.maxColorId += 1;
            color = this.maxColorId;
            drawColor(node, color);
        }
        return color;
    }

    public void clear() {
        this.colorMap.clear();
        this.maxColorId = 0;
    }
}
