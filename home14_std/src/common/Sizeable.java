package common;

/**
 * 大小接口
 * 一般用于各类Collections性质的对象
 */
public interface Sizeable {
    /**
     * 获取大小
     *
     * @return 大小
     */
    int size();

    /**
     * 判断是否为空
     *
     * @return 是否为空
     */
    default boolean isEmpty() {
        return size() == 0;
    }
}
