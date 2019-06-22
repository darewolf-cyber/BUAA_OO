package elements;

import com.oocourse.uml2.interact.exceptions.user.AttributeDuplicatedException;
import com.oocourse.uml2.interact.exceptions.user.AttributeNotFoundException;
import com.oocourse.uml2.models.elements.UmlAttribute;
import com.oocourse.uml2.models.elements.UmlClass;
import com.oocourse.uml2.models.elements.UmlElement;
import com.oocourse.uml2.utils.common.GenericPair;
import common.Sizeable;

import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

/**
 * 类属性管理器
 * 注意：
 * 1、本部分所处理的UmlAttribute均为类下的元素
 * 2、也就是说，顺序图中的UmlAttribute一概不参与此部分（构造函数中有相关的filter）
 */
@SuppressWarnings("WeakerAccess")
public class ClassAttributeManager implements Sizeable {
    private final ClassManager classManager;
    private final Set<UmlAttribute> umlAttributes;
    private final Map<UmlAttribute, UmlClass> umlClassesForAttributes;
    private final Map<UmlClass, Set<UmlAttribute>> umlAttributesForClass;
    private final Map<GenericPair<UmlClass, String>, List<UmlAttribute>>
            umlAttributesForClassAndName;

    /**
     * 构造函数
     *
     * @param elementPool  元素池
     * @param classManager 类管理器
     */
    ClassAttributeManager(ElementPool<UmlElement> elementPool,
                          ClassManager classManager) {
        this.classManager = classManager;
        this.umlAttributes = elementPool
                .getElementsWithType(UmlAttribute.class).stream()
                .filter(umlAttribute -> this.classManager
                        .containsUmlClassById(umlAttribute.getParentId()))
                .collect(Collectors.toSet());
        this.umlClassesForAttributes = this.umlAttributes.stream()
                .collect(Collectors.toMap(umlAttribute ->
                        umlAttribute, umlAttribute ->
                        (UmlClass) this.classManager.getUmlClassById(
                                umlAttribute.getParentId())
                ));
        this.umlAttributesForClass = this.umlAttributes.stream()
                .collect(Collectors.groupingBy(
                        this::getUmlClassForAttribute, Collectors.toSet()));
        this.umlAttributesForClassAndName = this.umlAttributes.stream()
                .collect(Collectors.groupingBy(umlAttribute ->
                        new GenericPair<>(getUmlClassForAttribute(umlAttribute),
                                umlAttribute.getName())
                ));
    }

    /**
     * 构造函数
     *
     * @param elementPool 元素池
     */
    ClassAttributeManager(ElementPool<UmlElement> elementPool) {
        this(elementPool, new ClassManager(elementPool));
    }

    /**
     * 根据属性元素获取类元素
     *
     * @param umlAttribute 属性元素
     * @return 类元素
     */
    public UmlClass getUmlClassForAttribute(UmlAttribute umlAttribute) {
        return this.umlClassesForAttributes.get(umlAttribute);
    }

    /**
     * 获取元素个数
     *
     * @return 元素个数
     */
    public int size() {
        return this.umlAttributes.size();
    }

    /**
     * 根据类元素获取属性元素集合
     *
     * @param umlClass 类元素
     * @return 属性元素集合
     */
    public Set<UmlAttribute> getAttributesForClass(UmlClass umlClass) {
        return this.umlAttributesForClass
                .getOrDefault(umlClass, new HashSet<>());
    }

    /**
     * 判断属性是否属于类
     *
     * @param umlClass     类对象
     * @param umlAttribute 属性对象
     * @return 属性是否属于类
     */
    public boolean containsUmlAttributeInClass(UmlClass umlClass,
                                               UmlAttribute umlAttribute) {
        if (this.classManager.containsUmlClass(umlClass)) {
            return this.getAttributesForClass(umlClass).contains(umlAttribute);
        } else {
            return false;
        }
    }

    /**
     * 判断类内是否含指定名称的属性
     *
     * @param umlClass      类元素
     * @param attributeName 属性名称
     * @return 是否含指定名称的属性
     */
    public boolean containsUmlAttributeNameInClass(
            UmlClass umlClass, String attributeName) {
        GenericPair<UmlClass, String> queryKey =
                new GenericPair<>(umlClass, attributeName);
        return this.umlAttributesForClassAndName.containsKey(queryKey)
                && this.umlAttributesForClassAndName.get(queryKey).size() > 0;
    }

    /**
     * 根据指定名称在类元素内获取属性元素
     *
     * @param umlClass      类元素
     * @param attributeName 属性名称
     * @return 属性元素
     * @throws AttributeNotFoundException   属性未找到异常
     * @throws AttributeDuplicatedException 属性重名异常
     */
    public UmlAttribute getUmlAttributeInClass(
            UmlClass umlClass, String attributeName)
            throws AttributeNotFoundException, AttributeDuplicatedException {
        GenericPair<UmlClass, String> queryKey =
                new GenericPair<>(umlClass, attributeName);
        if (this.umlAttributesForClassAndName.containsKey(queryKey)) {
            List<UmlAttribute> attributes =
                    this.umlAttributesForClassAndName.get(queryKey);
            if (attributes.size() > 1) {
                throw new AttributeDuplicatedException(
                        umlClass.getName(), attributeName);
            } else if (attributeName.isEmpty()) {
                throw new AttributeNotFoundException(
                        umlClass.getName(), attributeName);
            } else {
                return attributes.get(0);
            }
        } else {
            throw new AttributeNotFoundException(
                    umlClass.getName(), attributeName);
        }
    }

    /**
     * 根据属性名称在类及其父类内获取属性元素
     *
     * @param umlClass      类元素
     * @param attributeName 属性名称
     * @return 属性元素
     * @throws AttributeNotFoundException   属性未找到异常
     * @throws AttributeDuplicatedException 属性重名异常
     */
    public UmlAttribute getUmlAttributeInAllClasses(
            UmlClass umlClass, String attributeName)
            throws AttributeNotFoundException, AttributeDuplicatedException {
        UmlClass currentClass = umlClass;
        UmlAttribute umlAttribute = null;
        while (currentClass != null) {
            try {
                UmlAttribute attribute =
                        this.getUmlAttributeInClass(currentClass,
                                attributeName);
                if (umlAttribute != null) {
                    throw new AttributeDuplicatedException(
                            umlClass.getName(), attributeName);
                } else {
                    umlAttribute = attribute;
                }
            } catch (AttributeNotFoundException e) {
                // do nothing
            }
            currentClass = this.classManager.getParentClass(currentClass);
        }
        if (umlAttribute == null) {
            throw new AttributeNotFoundException(
                    umlClass.getName(), attributeName);
        } else {
            return umlAttribute;
        }
    }
}
