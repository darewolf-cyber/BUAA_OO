package common;

import java.util.Iterator;
import java.util.stream.Stream;
import java.util.stream.StreamSupport;

/**
 * 流支持迭代器
 *
 * @param <T>
 */
public interface IterableWithStreamSupport<T> extends Iterable<T> {
    /**
     * 获取迭代器
     *
     * @return 迭代器
     */
    @Override
    Iterator<T> iterator();

    /**
     * 获取普通函数式流
     *
     * @return 流
     */
    default Stream<T> stream() {
        return this.stream(false);
    }

    /**
     * 获取函数式流
     *
     * @param parallel 是否并行
     * @return 流
     */
    default Stream<T> stream(boolean parallel) {
        return StreamSupport.stream(this.spliterator(), parallel);
    }

    /**
     * 获取函数式并行流
     *
     * @return 流
     */
    default Stream<T> parallelStream() {
        return this.stream(true);
    }
}
