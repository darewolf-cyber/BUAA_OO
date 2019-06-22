package com.oocourse.specs1.models;

/**
 * 路径ID异常类
 */
public abstract class PathIdException extends ApplicationModelException {
    private final int pathId;

    /**
     * 构造函数
     *
     * @param message 异常消息
     * @param pathId  路径ID
     */
    public PathIdException(String message, int pathId) {
        super(message);
        this.pathId = pathId;
    }

    /**
     * 获取路径ID
     *
     * @return 路径ID
     */
    public int getPathId() {
        return pathId;
    }
}
