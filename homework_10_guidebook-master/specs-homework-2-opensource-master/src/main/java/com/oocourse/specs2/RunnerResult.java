package com.oocourse.specs2;

import java.util.HashMap;

/**
 * 运行结果对象
 */
class RunnerResult {
    private final String message;
    private final HashMap<String, Object> data;

    /**
     * 构造函数
     *
     * @param message 消息
     * @param data    附加数据
     */
    RunnerResult(String message, HashMap<String, Object> data) {
        this.message = message;
        this.data = data;
    }

    /**
     * 构造函数（附加数据位null）
     *
     * @param message 消息
     */
    RunnerResult(String message) {
        this(message, null);
    }

    /**
     * 获取消息
     *
     * @return 消息
     */
    String getMessage() {
        return message;
    }

    /**
     * 获取附加数据
     *
     * @return 附加数据
     */
    HashMap<String, Object> getData() {
        return data;
    }
}
