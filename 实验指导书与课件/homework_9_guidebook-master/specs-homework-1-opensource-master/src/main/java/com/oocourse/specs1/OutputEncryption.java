package com.oocourse.specs1;


import java.util.HashMap;

/**
 * 输出加密模块
 */
class OutputEncryption {
    /**
     * 原字符串
     */
    private final String message;
    private final Boolean error;
    private final Boolean success;
    private final HashMap<String, Object> data;

    /**
     * 构造函数
     *
     * @param message 原字符串
     * @param error   是否有异常
     * @param success 是否成功
     * @param data    数据信息
     */
    OutputEncryption(String message, boolean error, boolean success, HashMap<String, Object> data) {
        this.message = message;
        this.error = error;
        this.success = success && !error;
        this.data = data;
    }

    /**
     * 获取原字符串
     *
     * @return 原字符串
     */
    String getMessage() {
        return message;
    }

    /**
     * 获取是否有异常
     *
     * @return 是否有异常
     */
    public Boolean getError() {
        return error;
    }

    /**
     * 获取是否成功
     *
     * @return 是否成功
     */
    public Boolean getSuccess() {
        return success;
    }

    /**
     * 获取数据信息
     *
     * @return 数据信息
     */
    HashMap<String, Object> getData() {
        return data;
    }

    /**
     * 获取加密后的字符串
     *
     * @return 加密后的字符串
     */
    String getEncrypted() {
        return message;
    }
}

