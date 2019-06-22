package com.oocourse.specs3.models;

/**
 * 点对异常
 */
public abstract class NodePairException extends ApplicationModelException {
    private final int fromNodeId;
    private final int toNodeId;

    /**
     * 构造函数
     *
     * @param message    异常信息
     * @param fromNodeId 出发点id
     * @param toNodeId   目标点id
     */
    NodePairException(String message, int fromNodeId, int toNodeId) {
        super(message);
        this.fromNodeId = fromNodeId;
        this.toNodeId = toNodeId;
    }

    /**
     * 获取出发点id
     *
     * @return 出发点id
     */
    public int getFromNodeId() {
        return fromNodeId;
    }

    /**
     * 获取目标点id
     *
     * @return 目标点id
     */
    public int getToNodeId() {
        return toNodeId;
    }
}
