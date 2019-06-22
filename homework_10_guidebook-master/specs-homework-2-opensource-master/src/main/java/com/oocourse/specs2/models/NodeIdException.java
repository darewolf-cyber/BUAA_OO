package com.oocourse.specs2.models;

/**
 * 节点id异常
 */
public abstract class NodeIdException extends ApplicationModelException {
    private final int nodeId;

    /**
     * 构造函数
     *
     * @param message 异常信息
     * @param nodeId  节点id
     */
    public NodeIdException(String message, int nodeId) {
        super(message);
        this.nodeId = nodeId;
    }

    /**
     * 获取节点id
     *
     * @return 节点id
     */
    public int getNodeId() {
        return nodeId;
    }
}
