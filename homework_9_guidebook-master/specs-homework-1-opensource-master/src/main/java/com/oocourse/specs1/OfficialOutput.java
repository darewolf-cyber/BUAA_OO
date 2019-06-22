package com.oocourse.specs1;

import java.io.PrintStream;
import java.util.HashMap;

/**
 * 输出类
 */
@SuppressWarnings("SameParameterValue")
class OfficialOutput {
    private final PrintStream outputStream;

    /**
     * 构造函数
     *
     * @param outputStream 输出流
     */
    OfficialOutput(PrintStream outputStream) {
        this.outputStream = outputStream;
    }

    /**
     * 输出数据执行
     *
     * @param message 字符串消息
     * @param success 是否成功
     * @param data    数据信息
     */
    private void printlnExecute(String message, boolean error, boolean success, HashMap<String, Object> data) {
        OutputEncryption encryption = new OutputEncryption(message, error, success, data);
        this.outputStream.println(encryption.getEncrypted());
    }

    /**
     * 输出数据
     *
     * @param message 字符串消息
     * @param success 是否成功
     * @param data    数据信息
     */
    void println(String message, boolean error, boolean success, HashMap<String, Object> data) {
        this.printlnExecute(message, error, success, data);
    }
}
