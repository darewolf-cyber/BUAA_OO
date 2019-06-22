package com.oocourse.specs1;

import java.util.Arrays;

/**
 * 任意解析类
 * 作为解析类型使用，可以解析任意字符串类型
 */
public class Anything {
    private final String content;

    /**
     * 构造函数
     *
     * @param content 文本内容
     */
    private Anything(String content) {
        this.content = content;
    }

    /**
     * 解析函数
     *
     * @param content 文本内容
     * @return 任意内容对象
     */
    public static Anything valueOf(String content) {
        return new Anything(content);
    }

    /**
     * 获取文本内容
     *
     * @return 文本内容
     */
    public String getContent() {
        return content;
    }

    /**
     * 获取哈希值
     *
     * @return 哈希值
     */
    @Override
    public int hashCode() {
        return Arrays.hashCode(new Object[]{this.content});
    }

    /**
     * 判断是否相等
     *
     * @param obj 对象
     * @return 是否相等
     */
    @Override
    public boolean equals(Object obj) {
        if (this == obj) {
            return true;
        } else if (obj instanceof Anything) {
            return this.content.equals(((Anything) obj).content);
        } else {
            return false;
        }
    }

    /**
     * 获取字符串形式
     *
     * @return 字符串形式
     */
    @Override
    public String toString() {
        return this.content;
    }
}
