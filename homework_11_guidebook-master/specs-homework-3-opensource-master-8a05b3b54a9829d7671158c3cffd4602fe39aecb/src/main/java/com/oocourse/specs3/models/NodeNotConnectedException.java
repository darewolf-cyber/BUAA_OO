package com.oocourse.specs3.models;

/**
 * 节点不连通异常
 */
public class NodeNotConnectedException extends NodePairException {
    /**
     * 构造函数
     *
     * @param fromNodeId 出发点id
     * @param toNodeId   目标点id
     */
    public NodeNotConnectedException(int fromNodeId, int toNodeId) {
        super(
                String.format("Node %s and %d not connected.", fromNodeId, toNodeId),
                fromNodeId, toNodeId
        );
    }
}
