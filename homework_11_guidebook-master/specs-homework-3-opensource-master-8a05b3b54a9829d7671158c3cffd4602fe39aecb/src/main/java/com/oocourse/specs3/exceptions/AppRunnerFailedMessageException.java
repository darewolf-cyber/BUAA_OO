package com.oocourse.specs3.exceptions;

/**
 * AppRunner失败结果异常
 * 用于传出Failed消息
 */
public class AppRunnerFailedMessageException extends AppRunnerException {
    /**
     * 构造函数
     *
     * @param message Failed消息
     */
    public AppRunnerFailedMessageException(String message) {
        super(message);
    }
}
