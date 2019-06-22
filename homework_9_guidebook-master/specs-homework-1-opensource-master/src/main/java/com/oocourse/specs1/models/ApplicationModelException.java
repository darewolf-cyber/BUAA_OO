package com.oocourse.specs1.models;

/**
 * 应用模型异常类
 */
public abstract class ApplicationModelException extends Exception {
    /**
     * 构造函数
     *
     * @param message 异常消息
     */
    public ApplicationModelException(String message) {
        super(message);
    }
}
