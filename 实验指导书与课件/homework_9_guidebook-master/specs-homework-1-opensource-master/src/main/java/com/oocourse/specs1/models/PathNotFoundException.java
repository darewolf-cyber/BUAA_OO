package com.oocourse.specs1.models;

/**
 * 路径未找到异常类
 */
public class PathNotFoundException extends PathException {
    /**
     * 构造函数
     *
     * @param path 路径对象
     */
    public PathNotFoundException(Path path) {
        super(String.format("Path not found - %s.", path), path);
    }
}
