package elements;

import com.oocourse.uml2.models.elements.UmlClass;
import com.oocourse.uml2.models.elements.UmlClassOrInterface;
import com.oocourse.uml2.models.elements.UmlElement;
import com.oocourse.uml2.models.elements.UmlGeneralization;
import com.oocourse.uml2.models.elements.UmlInterface;
import com.oocourse.uml2.models.elements.UmlInterfaceRealization;
import common.IterableWithStreamSupport;
import common.Sizeable;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Queue;
import java.util.Set;
import java.util.stream.Collectors;

/**
 * 接口管理器
 */
@SuppressWarnings("WeakerAccess")
public class InterfaceManager implements
        Sizeable, IterableWithStreamSupport<UmlInterface> {
    private final ElementPool<UmlElement> elementPool;
    private final ClassManager classManager;
    private final Set<UmlInterface> umlInterfaces;
    private final Map<String, Set<UmlInterface>> umlInterfaceNameGroups;
    private final Map<UmlInterface, Set<UmlInterface>> interfaceExtends;
    private final Map<UmlInterface, List<UmlInterface>> interfaceExtendList;
    private final Map<UmlClass, Set<UmlInterface>> interfaceImplements;
    private final Map<UmlClass, List<UmlInterface>> interfaceImplementList;

    /**
     * 构造函数
     *
     * @param elementPool  元素池
     * @param classManager 类管理器
     */
    InterfaceManager(ElementPool<UmlElement> elementPool,
                     ClassManager classManager) {
        this.elementPool = elementPool;
        this.classManager = classManager;
        this.umlInterfaces = this.elementPool
                .getElementsWithType(UmlInterface.class);
        this.umlInterfaceNameGroups = this.umlInterfaces.stream()
                .collect(Collectors.groupingBy(
                        UmlInterface::getName, Collectors.toSet()));
        this.interfaceExtendList = this.elementPool
                .getElementsWithType(UmlGeneralization.class).stream()
                .filter(umlGeneralization -> this.elementPool
                        .containsElementIdAndType(
                                umlGeneralization.getSource(),
                                UmlInterface.class)
                        && this.elementPool.containsElementIdAndType(
                        umlGeneralization.getTarget(), UmlInterface.class))
                .collect(Collectors.groupingBy(umlGeneralization ->
                                (UmlInterface) this.elementPool
                                        .getElementById(
                                                umlGeneralization.getSource()),
                        Collectors.mapping(umlGeneralization ->
                                        (UmlInterface) this.elementPool
                                                .getElementById(
                                                        umlGeneralization
                                                                .getTarget()),
                                Collectors.toList()
                        )
                ));
        this.interfaceExtends = this.interfaceExtendList.entrySet().stream()
                .collect(Collectors.toMap(Map.Entry::getKey, entry ->
                        new HashSet<>(entry.getValue())
                ));
        this.interfaceImplementList = this.elementPool
                .getElementsWithType(UmlInterfaceRealization.class).stream()
                .filter(umlInterfaceRealization -> this.elementPool
                        .containsElementIdAndType(
                                umlInterfaceRealization.getSource()
                                , UmlClass.class)
                        && this.elementPool.containsElementIdAndType(
                        umlInterfaceRealization.getTarget(),
                        UmlInterface.class))
                .collect(Collectors.groupingBy(umlInterfaceRealization ->
                                (UmlClass) this.elementPool
                                        .getElementById(
                                                umlInterfaceRealization
                                                        .getSource()),
                        Collectors.mapping(umlInterfaceRealization ->
                                        (UmlInterface) this.elementPool
                                                .getElementById(
                                                        umlInterfaceRealization
                                                                .getTarget()),
                                Collectors.toList()
                        )
                ));
        this.interfaceImplements = this.interfaceImplementList
                .entrySet().stream()
                .collect(Collectors.toMap(Map.Entry::getKey, entry ->
                        new HashSet<>(entry.getValue())
                ));
    }

    /**
     * 是否包含指定接口元素
     *
     * @param umlInterface 接口元素
     * @return 是否包含
     */
    public boolean containsUmlInterface(UmlInterface umlInterface) {
        return this.umlInterfaces.contains(umlInterface);
    }

    /**
     * 是否包含指定的接口元素id
     *
     * @param interfaceId 接口元素id
     * @return 是否包含
     */
    public boolean containsUmlInterfaceById(String interfaceId) {
        return this.elementPool.containsElementIdAndType(
                interfaceId, UmlInterface.class)
                && this.umlInterfaces.contains(this.elementPool
                .getElementById(interfaceId, UmlInterface.class));
    }

    /**
     * 是否包含指定的接口名称
     *
     * @param interfaceName 接口名称
     * @return 是否包含
     */
    public boolean containsUmlInterfaceName(String interfaceName) {
        return this.umlInterfaceNameGroups.containsKey(interfaceName);
    }

    /**
     * 获取类直接实现的接口列表
     *
     * @param umlClass 类元素
     * @return 接口列表
     */
    public List<UmlInterface> getDirectlyImplementInterfaceListByClass(
            UmlClass umlClass) {
        return this.interfaceImplementList
                .getOrDefault(umlClass, new ArrayList<>());
    }

    /**
     * 获取类直接实现的接口集合
     *
     * @param umlClass 类元素
     * @return 接口集合
     */
    public Set<UmlInterface> getDirectlyImplementInterfacesByClass(
            UmlClass umlClass) {
        return this.interfaceImplements
                .getOrDefault(umlClass, new HashSet<>());
    }

    /**
     * 获取类实现的全部接口集合
     *
     * @param umlClass 类元素
     * @return 全部接口集合
     */
    public Set<UmlInterface> getImplementInterfacesByClass(UmlClass umlClass) {
        Set<UmlInterface> umlInterfaces = new HashSet<>();
        Set<UmlClass> umlClasses = new HashSet<>();
        Queue<UmlClassOrInterface> queue = new LinkedList<>();
        queue.offer(umlClass);

        while (!queue.isEmpty()) {
            UmlClassOrInterface classOrInterface = queue.poll();
            if (classOrInterface instanceof UmlClass) {
                UmlClass umlClass1 = (UmlClass) classOrInterface;
                UmlClass parentClass = this.classManager
                        .getParentClass(umlClass1);
                if (!umlClasses.contains(parentClass)) {
                    umlClasses.add(parentClass);
                    queue.offer(parentClass);
                }
                if (this.interfaceImplements.containsKey(umlClass1)) {
                    for (UmlInterface umlInterfaceItem : this
                            .interfaceImplements.get(umlClass1)) {
                        if (!umlInterfaces.contains(umlInterfaceItem)) {
                            umlInterfaces.add(umlInterfaceItem);
                            queue.offer(umlInterfaceItem);
                        }
                    }
                }
            } else if (classOrInterface instanceof UmlInterface) {
                UmlInterface umlInterface = (UmlInterface) classOrInterface;
                if (this.interfaceExtends.containsKey(umlInterface)) {
                    for (UmlInterface umlInterfaceItem : this
                            .interfaceExtends.get(umlInterface)) {
                        if (!umlInterfaces.contains(umlInterfaceItem)) {
                            umlInterfaces.add(umlInterfaceItem);
                            queue.offer(umlInterfaceItem);
                        }
                    }
                }
            }
        }
        return umlInterfaces;
    }

    /**
     * 获取接口直接继承的接口列表
     *
     * @param umlInterface 接口元素
     * @return 接口列表
     */
    public List<UmlInterface> getDirectlyExtendInterfaceListByInterface(
            UmlInterface umlInterface) {
        return this.interfaceExtendList
                .getOrDefault(umlInterface, new ArrayList<>());
    }

    /**
     * 获取接口直接继承的接口列表
     *
     * @param umlInterface 接口元素
     * @return 接口列表
     */
    public Set<UmlInterface> getDirectlyExtendInterfacesByInterface(
            UmlInterface umlInterface) {
        return this.interfaceExtends
                .getOrDefault(umlInterface, new HashSet<>());
    }

    /**
     * 获取数量
     *
     * @return 数量
     */
    @Override
    public int size() {
        return this.umlInterfaces.size();
    }

    /**
     * 获取迭代器
     *
     * @return 迭代器
     */
    @Override
    public Iterator<UmlInterface> iterator() {
        return this.umlInterfaces.iterator();
    }

}
