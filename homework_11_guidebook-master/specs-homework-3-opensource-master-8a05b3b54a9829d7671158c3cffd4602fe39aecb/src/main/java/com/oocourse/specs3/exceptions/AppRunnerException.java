package com.oocourse.specs3.exceptions;

/**
 * AppRunner异常
 */
public abstract class AppRunnerException extends ApplicationException {
    /**
     * 构造函数
     *
     * @param message 异常消息
     */
    AppRunnerException(String message) {
        super(message);
    }
}
