package elements;

import com.oocourse.uml2.interact.exceptions.user.ClassDuplicatedException;
import com.oocourse.uml2.interact.exceptions.user.ClassNotFoundException;
import com.oocourse.uml2.models.elements.UmlClass;
import com.oocourse.uml2.models.elements.UmlElement;
import com.oocourse.uml2.models.elements.UmlGeneralization;
import common.IterableWithStreamSupport;
import common.Sizeable;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

/**
 * 类管理器
 */
@SuppressWarnings("WeakerAccess")
public class ClassManager implements
        Sizeable, IterableWithStreamSupport<UmlClass> {
    private final ElementPool<UmlElement> elementPool;
    private final Set<UmlClass> umlClasses;
    private final Map<String, List<UmlClass>> umlClassNameGroups;
    private final Map<UmlClass, UmlClass> umlClassParents;

    /**
     * 构造函数
     *
     * @param elementPool 元素池
     */
    ClassManager(ElementPool<UmlElement> elementPool) {
        this.elementPool = elementPool;
        this.umlClasses = this.elementPool.getElementsWithType(UmlClass.class);
        this.umlClassNameGroups = this.umlClasses.stream()
                .collect(Collectors.groupingBy(UmlClass::getName));
        this.umlClassParents = this.elementPool
                .getElementsWithType(UmlGeneralization.class).stream()
                .filter(umlGeneralization -> this.containsUmlClassById(
                        umlGeneralization.getSource())
                        && this.containsUmlClassById(
                        umlGeneralization.getTarget()))
                .collect(Collectors.toMap(umlGeneralization -> (UmlClass)
                        this.getUmlClassById(
                                umlGeneralization.getSource()
                        ), umlGeneralization
                        -> (UmlClass) this.getUmlClassById(
                        umlGeneralization.getTarget())
                ));
    }

    /**
     * 根据名称获取类元素列表
     *
     * @param className 类名称
     * @return 类元素列表
     */
    private List<UmlClass> getUmlClassesByName(String className) {
        if (this.umlClassNameGroups.containsKey(className)) {
            return this.umlClassNameGroups.get(className);
        } else {
            return new ArrayList<>();
        }
    }

    /**
     * 根据类名称获取类元素
     *
     * @param className 类名称
     * @return 类元素
     * @throws ClassNotFoundException   类未找到异常
     * @throws ClassDuplicatedException 类重名异常
     */
    public UmlClass getUmlClassByName(String className)
            throws ClassNotFoundException, ClassDuplicatedException {
        List<UmlClass> classes = getUmlClassesByName(className);
        if (classes.size() > 1) {
            throw new ClassDuplicatedException(className);
        } else if (classes.isEmpty()) {
            throw new ClassNotFoundException(className);
        } else {
            return classes.get(0);
        }
    }

    /**
     * 获取父类元素
     *
     * @param umlClass 类元素
     * @return 父类元素
     */
    public UmlClass getParentClass(UmlClass umlClass) {
        return this.umlClassParents.getOrDefault(umlClass, null);
    }

    /**
     * 判断是否包含指定元素id的类元素
     *
     * @param elementId 元素id
     * @return 是否包含
     */
    public boolean containsUmlClassById(String elementId) {
        return this.elementPool.containsElementIdAndType(
                elementId, UmlClass.class)
                && this.umlClasses.contains(this.elementPool
                .getElementById(elementId, UmlClass.class));
    }

    /**
     * 根据id获取指定的类元素
     *
     * @param elementId 元素id
     * @return 类元素
     */
    public UmlClass getUmlClassById(String elementId) {
        if (this.containsUmlClassById(elementId)) {
            return (UmlClass) this.elementPool.getElementById(elementId);
        } else {
            return null;
        }
    }

    /**
     * 判断是否包含类元素
     *
     * @param umlClass 类元素
     * @return 是否包含类元素
     */
    public boolean containsUmlClass(UmlClass umlClass) {
        return this.umlClasses.contains(umlClass);
    }

    /**
     * 获取数量
     *
     * @return 数量
     */
    public int size() {
        return this.umlClasses.size();
    }

    /**
     * 获取迭代器
     *
     * @return 迭代器
     */
    @Override
    public Iterator<UmlClass> iterator() {
        return this.umlClasses.iterator();
    }
}
