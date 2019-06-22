package com.oocourse.specs1.models;

/**
 * 路径异常类
 */
public abstract class PathException extends ApplicationModelException {
    private final Path path;

    /**
     * 构造函数
     *
     * @param message 异常消息
     * @param path    路径对象
     */
    public PathException(String message, Path path) {
        super(message);
        this.path = path;
    }

    /**
     * 获取路径对象
     *
     * @return 路径对象
     */
    public Path getPath() {
        return path;
    }
}
