package elements;

import com.oocourse.uml2.models.elements.UmlAssociation;
import com.oocourse.uml2.models.elements.UmlAssociationEnd;
import com.oocourse.uml2.models.elements.UmlElement;
import com.oocourse.uml2.utils.common.GenericPair;

import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.Stream;

/**
 * 关联关系管理
 */
@SuppressWarnings("WeakerAccess")
public class AssociationManager {
    private final ElementPool<UmlElement> elementPool;
    private final Set<UmlAssociation> umlAssociations;
    private final Set<UmlAssociationEnd> umlAssociationEnds;
    private final Map<UmlAssociationEnd, UmlElement> umlAssociationEndElements;
    private final Map<UmlElement, Set<UmlAssociationEnd>>
            umlElementsAssociationEnds;
    private final Map<UmlAssociationEnd, UmlAssociationEnd> umlAssociationPairs;
    private final Map<UmlAssociationEnd, UmlAssociation>
            umlAssociationEndToAssociations;

    /**
     * 构造函数
     *
     * @param elementPool 元素池
     */
    AssociationManager(ElementPool<UmlElement> elementPool) {
        this.elementPool = elementPool;
        this.umlAssociations = this.elementPool
                .getElementsWithType(UmlAssociation.class).stream()
                .filter(umlAssociation -> this.elementPool
                        .containsElementIdAndType(
                                umlAssociation.getEnd1(),
                                UmlAssociationEnd.class))
                .filter(umlAssociation -> this.elementPool
                        .containsElementIdAndType(
                                umlAssociation.getEnd2(),
                                UmlAssociationEnd.class))
                .collect(Collectors.toSet());

        this.umlAssociationEnds = this.elementPool
                .getElementsWithType(UmlAssociationEnd.class).stream()
                .filter(umlAssociationEnd -> this.elementPool
                        .containsElementId(umlAssociationEnd.getReference()))
                .collect(Collectors.toSet());
        this.umlAssociationEndElements = this.umlAssociationEnds.stream()
                .collect(Collectors
                        .toMap(umlAssociationEnd ->
                                umlAssociationEnd, umlAssociationEnd ->
                                this.elementPool.getElementById(
                                        umlAssociationEnd.getReference())
                        ));
        this.umlElementsAssociationEnds = this.umlAssociationEndElements
                .entrySet().stream()
                .collect(Collectors.groupingBy(
                        Map.Entry::getValue,
                        Collectors.mapping(
                                Map.Entry::getKey,
                                Collectors.toSet()
                        )
                ));
        this.umlAssociationPairs = Stream.concat(
                this.umlAssociations.stream()
                        .map(umlAssociation -> new GenericPair<>(
                                this.elementPool.getElementById(
                                        umlAssociation.getEnd1(),
                                        UmlAssociationEnd.class),
                                this.elementPool.getElementById(
                                        umlAssociation.getEnd2(),
                                        UmlAssociationEnd.class)
                        )),
                this.umlAssociations.stream()
                        .map(umlAssociation -> new GenericPair<>(
                                this.elementPool.getElementById(
                                        umlAssociation.getEnd2(),
                                        UmlAssociationEnd.class),
                                this.elementPool.getElementById(
                                        umlAssociation.getEnd1(),
                                        UmlAssociationEnd.class)
                        ))
        ).collect(Collectors.toMap(
                GenericPair::getFirstValue,
                GenericPair::getSecondValue
        ));
        this.umlAssociationEndToAssociations = Stream.concat(
                this.umlAssociations.stream()
                        .map(umlAssociation -> new GenericPair<>(
                                this.elementPool.getElementById(
                                        umlAssociation.getEnd1(),
                                        UmlAssociationEnd.class),
                                umlAssociation
                        )),
                this.umlAssociations.stream()
                        .map(umlAssociation -> new GenericPair<>(
                                this.elementPool.getElementById(
                                        umlAssociation.getEnd2(),
                                        UmlAssociationEnd.class),
                                umlAssociation
                        ))
        ).collect(Collectors.toMap(
                GenericPair::getFirstValue,
                GenericPair::getSecondValue
        ));
    }

    /**
     * 判断是否包含关联
     *
     * @param umlAssociation 关联对象
     * @return 是否包含
     */
    public boolean containsUmlAssocation(UmlAssociation umlAssociation) {
        return this.umlAssociations.contains(umlAssociation);
    }

    /**
     * 判断是否包含关联端点
     *
     * @param umlAssociationEnd 关联端点对象
     * @return 是否包含
     */
    private boolean containsUmlAssociationEnd(
            UmlAssociationEnd umlAssociationEnd) {
        return this.umlAssociationEnds.contains(umlAssociationEnd);
    }

    /**
     * 根据元素获取关联端点集合
     *
     * @param umlElement 元素
     * @return 关联端点集合
     */
    public Set<UmlAssociationEnd> getUmlAssociationEnds(UmlElement umlElement) {
        return this.umlElementsAssociationEnds
                .getOrDefault(umlElement, new HashSet<>());
    }

    /**
     * 根据元素获取关联集合
     *
     * @param umlElement 元素
     * @return 关联集合
     */
    public Set<UmlAssociation> getUmlAssociations(UmlElement umlElement) {
        return this.getUmlAssociationEnds(umlElement).stream()
                .map(this.umlAssociationEndToAssociations::get)
                .collect(Collectors.toSet());
    }

    /**
     * 根据元素获取关联对端端点集合
     *
     * @param umlElement 元素
     * @return 关联对端端点集合
     */
    public Set<UmlAssociationEnd> getUmlAssociationOppositeEnds(
            UmlElement umlElement) {
        return this.getUmlAssociationEnds(umlElement).stream()
                .map(this.umlAssociationPairs::get)
                .collect(Collectors.toSet());
    }

    /**
     * 根据元素获取关联对端元素集合
     *
     * @param umlElement 元素
     * @return 关联对端元素集合
     */
    public Set<UmlElement> getUmlAssociatedElements(UmlElement umlElement) {
        return this.getUmlAssociationEnds(umlElement).stream()
                .map(this.umlAssociationPairs::get)
                .map(this.umlAssociationEndElements::get)
                .collect(Collectors.toSet());
    }
}
