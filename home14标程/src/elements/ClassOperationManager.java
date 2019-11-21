package elements;

import com.oocourse.uml2.interact.common.OperationQueryType;
import com.oocourse.uml2.models.common.Direction;
import com.oocourse.uml2.models.elements.UmlClass;
import com.oocourse.uml2.models.elements.UmlClassOrInterface;
import com.oocourse.uml2.models.elements.UmlElement;
import com.oocourse.uml2.models.elements.UmlInterface;
import com.oocourse.uml2.models.elements.UmlOperation;
import com.oocourse.uml2.models.elements.UmlParameter;

import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

/**
 * 类操作管理器
 */
@SuppressWarnings({"WeakerAccess", "FieldCanBeLocal"})
public class ClassOperationManager {
    private final ElementPool<UmlElement> elementPool;
    private final Set<UmlOperation> umlOperations;

    private final Map<UmlOperation, UmlClass> umlOperationsWithClasses;
    private final Map<UmlClass, Set<UmlOperation>> umlClassesWithOperations;

    private final Map<UmlOperation, UmlInterface> umlOperationsWithInterfaces;
    private final Map<UmlInterface, Set<UmlOperation>>
            umlInterfacesWithOperations;

    private final Set<UmlParameter> umlParameters;
    private final Map<UmlParameter, UmlOperation> umlParametersWithOperations;
    private final Map<UmlOperation, Set<UmlParameter>>
            umlOperationsWithParameters;

    /**
     * 构造函数
     *
     * @param elementPool 元素池
     */
    public ClassOperationManager(ElementPool<UmlElement> elementPool) {
        this.elementPool = elementPool;
        this.umlOperations = this.elementPool
                .getElementsWithType(UmlOperation.class);

        this.umlOperationsWithClasses = this.umlOperations.stream()
                .filter(umlOperation -> this.elementPool
                        .containsElementIdAndType(
                                umlOperation.getParentId(), UmlClass.class))
                .collect(Collectors.toMap(element -> element, umlOperation
                        -> this.elementPool
                        .getElementById(umlOperation.getParentId(),
                                UmlClass.class)
                ));
        this.umlClassesWithOperations = this.umlOperationsWithClasses
                .entrySet().stream()
                .collect(Collectors.groupingBy(
                        Map.Entry::getValue,
                        Collectors.mapping(
                                Map.Entry::getKey,
                                Collectors.toSet()
                        )
                ));

        this.umlOperationsWithInterfaces = this.umlOperations.stream()
                .filter(umlOperation -> this.elementPool
                        .containsElementIdAndType(umlOperation.getParentId(),
                                UmlInterface.class))
                .collect(Collectors.toMap(element -> element, umlOperation
                        -> this.elementPool
                        .getElementById(umlOperation.getParentId(),
                                UmlInterface.class)
                ));
        this.umlInterfacesWithOperations = this.umlOperationsWithInterfaces
                .entrySet().stream()
                .collect(Collectors.groupingBy(
                        Map.Entry::getValue,
                        Collectors.mapping(
                                Map.Entry::getKey,
                                Collectors.toSet()
                        )
                ));

        this.umlParameters = this.elementPool
                .getElementsWithType(UmlParameter.class);
        this.umlParametersWithOperations = this.umlParameters.stream()
                .filter(umlParameter -> this.elementPool
                        .containsElementIdAndType(umlParameter.getParentId(),
                                UmlOperation.class))
                .collect(Collectors.toMap(element -> element, umlParameter
                        -> this.elementPool
                        .getElementById(umlParameter.getParentId(),
                                UmlOperation.class)
                ));
        this.umlOperationsWithParameters = this.umlParametersWithOperations
                .entrySet().stream()
                .collect(Collectors.groupingBy(
                        Map.Entry::getValue,
                        Collectors.mapping(
                                Map.Entry::getKey,
                                Collectors.toSet()
                        )
                ));
    }

    /**
     * 获取指定操作所属的类或接口元素
     *
     * @param umlOperation 操作元素
     * @return 类或接口元素
     */
    private UmlClassOrInterface getParentElementForOperation(
            UmlOperation umlOperation) {
        if (this.umlOperationsWithInterfaces.containsKey(umlOperation)) {
            return this.umlOperationsWithInterfaces.get(umlOperation);
        } else {
            return this.umlOperationsWithClasses
                    .getOrDefault(umlOperation, null);
        }
    }

    /**
     * 判断是否包含操作元素
     *
     * @param umlOperation 操作元素
     * @return 是否包含
     */
    private boolean containsOperation(UmlOperation umlOperation) {
        return this.umlOperations.contains(umlOperation);
    }

    /**
     * 获取类或接口元素所属的操作元素列表
     *
     * @param umlClassOrInterface 类或接口元素
     * @return 操作元素列表
     */
    Set<UmlOperation> getUmlOperations(
            UmlClassOrInterface umlClassOrInterface) {
        if (umlClassOrInterface instanceof UmlClass) {
            return this.umlClassesWithOperations.getOrDefault(
                    umlClassOrInterface, new HashSet<>());
        } else if (umlClassOrInterface instanceof UmlInterface) {
            return this.umlInterfacesWithOperations.getOrDefault(
                    umlClassOrInterface, new HashSet<>());
        } else {
            return new HashSet<>();
        }
    }

    /**
     * 判断操作是否为特定类型
     *
     * @param umlOperation 操作元素
     * @param queryType    查询类型
     * @return 操作是否为特定类型
     */
    public boolean isType(UmlOperation umlOperation,
                          OperationQueryType queryType) {
        if (!this.umlOperations.contains(umlOperation)) {
            return false;
        }
        Set<UmlParameter> parameters = this.umlOperationsWithParameters
                .getOrDefault(umlOperation, new HashSet<>());
        long totalCount = parameters.size();
        long returnCount = parameters.stream()
                .filter(umlParameter -> umlParameter.getDirection()
                        == Direction.RETURN)
                .count();
        long paramCount = totalCount - returnCount;
        switch (queryType) {
            case NON_RETURN:
                return returnCount == 0;
            case RETURN:
                return returnCount > 0;
            case NON_PARAM:
                return paramCount == 0;
            case PARAM:
                return paramCount > 0;
            case ALL:
                return true;
            default:
                return false;
        }
    }
}
