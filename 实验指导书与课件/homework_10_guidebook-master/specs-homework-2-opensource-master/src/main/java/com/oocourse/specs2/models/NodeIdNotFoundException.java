package com.oocourse.specs2.models;

/**
 * 节点id未找到异常
 */
public class NodeIdNotFoundException extends NodeIdException {
    /**
     * 构造函数
     *
     * @param nodeId 节点id
     */
    public NodeIdNotFoundException(int nodeId) {
        super(String.format("Node id not found - %s.", nodeId), nodeId);
    }
}
