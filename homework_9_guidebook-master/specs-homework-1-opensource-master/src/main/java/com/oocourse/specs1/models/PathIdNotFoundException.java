package com.oocourse.specs1.models;

/**
 * 路径ID未找到异常类
 */
public class PathIdNotFoundException extends PathIdException {
    /**
     * 构造函数
     *
     * @param pathId 路径ID
     */
    public PathIdNotFoundException(int pathId) {
        super(String.format("Path id not found - %s.", pathId), pathId);
    }
}
