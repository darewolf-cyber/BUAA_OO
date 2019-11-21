package com.oocourse.specs1.models;

/**
 * 路径重复异常类
 */
public class DuplicatedPathException extends PathException {
    /**
     * 构造函数
     *
     * @param path 路径对象
     */
    public DuplicatedPathException(Path path) {
        super(String.format("Duplicated path - %s.", path), path);
    }
}
