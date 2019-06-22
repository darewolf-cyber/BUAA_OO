package elements;

import com.oocourse.uml2.models.elements.UmlElement;
import common.IterableWithStreamSupport;
import common.Sizeable;

import java.util.Arrays;
import java.util.Collections;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.StreamSupport;

/**
 * 元素池
 *
 * @param <E> 元素类型
 */
@SuppressWarnings({"unchecked", "WeakerAccess"})
public class ElementPool<E extends UmlElement> implements
        IterableWithStreamSupport<E>, Sizeable {
    private final Set<E> elements;
    private final Map<String, E> elementIdMap;
    private final Map<String, Set<E>> elementParentIdMap;
    private final Map<Class<? extends UmlElement>, Set<E>> elementTypeGroups;

    /**
     * 构造函数
     *
     * @param elements 元素迭代器
     */
    ElementPool(Iterable<E> elements) {
        this.elements = Collections.unmodifiableSet(
                StreamSupport.stream(elements.spliterator(), false)
                        .collect(Collectors.toSet())
        );
        this.elementIdMap = Collections.unmodifiableMap(
                this.elements.stream()
                        .collect(Collectors.toMap(E::getId, e -> e))
        );
        this.elementParentIdMap = Collections.unmodifiableMap(
                this.elements.stream()
                        .collect(Collectors.groupingBy(
                                E::getParentId,
                                Collectors.toSet()
                        ))
        );
        this.elementTypeGroups = Collections.unmodifiableMap(
                this.elements.stream()
                        .collect(Collectors.groupingBy(
                                E::getClass, Collectors.toSet()))
        );
    }

    /**
     * 构造函数
     *
     * @param elements 元素数组
     */
    ElementPool(E... elements) {
        this(Arrays.asList(elements));
    }

    /**
     * 根据id获取元素
     *
     * @param elementId 元素id
     * @return 元素
     */
    public E getElementById(String elementId) {
        return this.elementIdMap.get(elementId);
    }

    /**
     * 根据元素id获取指定类型的元素
     *
     * @param elementId 元素id
     * @param clazz     类型对象
     * @param <E1>      类型
     * @return 指定类型的元素
     */
    public <E1 extends E> E1 getElementById(
            String elementId, Class<E1> clazz) {
        return (E1) this.elementIdMap.get(elementId);
    }

    /**
     * 获取指定parentId的元素集合
     *
     * @param parentId parentId
     * @return 元素集合
     */
    public Set<E> getElementsWithParentId(String parentId) {
        return Collections.unmodifiableSet(this.elementParentIdMap
                .getOrDefault(parentId, new HashSet<>()));
    }

    /**
     * 获取指定parentId下指定类型的元素集合
     *
     * @param parentId parentId
     * @param clazz    类型对象
     * @param <E1>     类型
     * @return 元素集合
     */
    public <E1 extends E> Set<E1> getElementsWithParentId(
            String parentId, Class<E1> clazz) {
        return Collections.unmodifiableSet(
                this.getElementsWithParentId(parentId).stream()
                        .filter(clazz::isInstance)
                        .map(element -> (E1) element)
                        .collect(Collectors.toSet())
        );
    }

    /**
     * 判断是否包含指定元素id的元素
     *
     * @param elementId 元素id
     * @return 元素
     */
    public boolean containsElementId(String elementId) {
        return this.elementIdMap.containsKey(elementId);
    }

    /**
     * 判断是否包含指定元素id且类型为指定类型的元素
     *
     * @param elementId 元素id
     * @param clazz     元素类型
     * @return 是否包含
     */
    public boolean containsElementIdAndType(String elementId,
                                            Class<? extends UmlElement> clazz) {
        if (this.containsElementId(elementId)) {
            UmlElement element = this.getElementById(elementId);
            return clazz.isInstance(element);
        } else {
            return false;
        }
    }

    /**
     * 判断是否包含元素
     *
     * @param element 元素
     * @return 是否包含
     */
    public boolean containsElement(E element) {
        return this.elements.contains(element);
    }

    /**
     * 获取指定类型的元素集合
     *
     * @param clazz 类型对象
     * @param <E1>  类型
     * @return 指定类型的元素集合
     */
    public <E1 extends E> Set<E1> getElementsWithType(Class<E1> clazz) {
        Set<E> result = this.elementTypeGroups
                .getOrDefault(clazz, new HashSet<>());
        return Collections.unmodifiableSet(
                result.stream().
                        map(element -> (E1) element)
                        .collect(Collectors.toSet())
        );
    }

    /**
     * 获取数量
     *
     * @return 数量
     */
    public int size() {
        return this.elements.size();
    }

    /**
     * 获取迭代器
     *
     * @return 迭代器
     */
    @Override
    public Iterator<E> iterator() {
        return this.elements.iterator();
    }
}
