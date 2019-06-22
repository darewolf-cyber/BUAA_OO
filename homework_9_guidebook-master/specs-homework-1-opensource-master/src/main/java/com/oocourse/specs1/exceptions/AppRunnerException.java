package com.oocourse.specs1.exceptions;

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
