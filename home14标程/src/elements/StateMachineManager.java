package elements;

import com.oocourse.uml2.interact.exceptions.user.StateDuplicatedException;
import com.oocourse.uml2.interact.exceptions.user.StateMachineDuplicatedException;
import com.oocourse.uml2.interact.exceptions.user.StateMachineNotFoundException;
import com.oocourse.uml2.interact.exceptions.user.StateNotFoundException;
import com.oocourse.uml2.models.elements.UmlElement;
import com.oocourse.uml2.models.elements.UmlFinalState;
import com.oocourse.uml2.models.elements.UmlPseudostate;
import com.oocourse.uml2.models.elements.UmlRegion;
import com.oocourse.uml2.models.elements.UmlState;
import com.oocourse.uml2.models.elements.UmlStateMachine;
import com.oocourse.uml2.models.elements.UmlTransition;

import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Set;
import java.util.stream.Collectors;

/**
 * 状态机管理器
 * 说明：
 * 1、官方接口中并没有对init/state/final三类元素统一抽象
 * 2、基于上述原因，此处的状态均以UmlElement的形式存储&管理
 */
@SuppressWarnings({"FieldCanBeLocal", "WeakerAccess"})
public class StateMachineManager {
    private final ElementPool<UmlElement> elementPool;
    private final Set<UmlStateMachine> umlStateMachines;
    private final Map<String, List<UmlStateMachine>> umlStateMachineNameGroups;
    private final Map<UmlStateMachine, UmlRegion> umlRegionForStateMachine;
    private final Set<UmlRegion> umlRegions;
    private final Map<UmlRegion, Set<UmlTransition>> umlTransitionsForRegion;
    private final Map<UmlRegion, Set<UmlElement>> umlStatesForRegions;
    private final Map<UmlTransition, UmlElement> umlTransitionSources;
    private final Map<UmlTransition, UmlElement> umlTransitionTargets;
    private final Map<UmlElement, Set<UmlElement>> umlTransitionsPairs;

    /**
     * 构造函数
     *
     * @param elementPool 元素池
     */
    StateMachineManager(ElementPool<UmlElement> elementPool) {
        this.elementPool = elementPool;
        this.umlStateMachines = this.elementPool
                .getElementsWithType(UmlStateMachine.class);
        this.umlStateMachineNameGroups = this.umlStateMachines.stream()
                .collect(Collectors.groupingBy(
                        UmlStateMachine::getName
                ));
        this.umlRegions = this.elementPool
                .getElementsWithType(UmlRegion.class);
        this.umlRegionForStateMachine = this.umlRegions.stream()
                .collect(Collectors.toMap(umlRegion -> this.elementPool
                        .getElementById(umlRegion.getParentId(),
                                UmlStateMachine.class), umlRegion -> umlRegion
                ));
        this.umlTransitionsForRegion = this.elementPool
                .getElementsWithType(UmlTransition.class).stream()
                .collect(Collectors.groupingBy(umlTransition -> this.elementPool
                                .getElementById(umlTransition.getParentId(),
                                        UmlRegion.class),
                        Collectors.toSet()
                ));
        this.umlStatesForRegions = this.elementPool.stream()
                .filter(umlElement -> (umlElement instanceof UmlState)
                        || (umlElement instanceof UmlPseudostate)
                        || (umlElement instanceof UmlFinalState))
                .collect(Collectors.groupingBy(umlState -> this.elementPool
                                .getElementById(umlState.getParentId(),
                                        UmlRegion.class),
                        Collectors.toSet()
                ));
        this.umlTransitionSources = this.elementPool
                .getElementsWithType(UmlTransition.class).stream()
                .collect(Collectors.toMap(umlTransition ->
                        umlTransition, umlTransition -> this.elementPool
                        .getElementById(umlTransition.getSource())
                ));
        this.umlTransitionTargets = this.elementPool
                .getElementsWithType(UmlTransition.class).stream()
                .collect(Collectors.toMap(umlTransition ->
                        umlTransition, umlTransition -> this.elementPool
                        .getElementById(umlTransition.getTarget())
                ));
        this.umlTransitionsPairs = this.elementPool
                .getElementsWithType(UmlTransition.class).stream()
                .collect(Collectors.groupingBy(umlTransition -> this.elementPool
                                .getElementById(umlTransition.getSource()),
                        Collectors.mapping(umlTransition -> this.elementPool
                                        .getElementById(
                                                umlTransition.getTarget()),
                                Collectors.toSet()
                        )
                ));
    }

    /**
     * 判断是否包含状态机元素
     *
     * @param umlStateMachine 状态机元素
     * @return 是否包含
     */
    public boolean containsStateMachine(UmlStateMachine umlStateMachine) {
        return this.umlStateMachines.contains(umlStateMachine);
    }

    /**
     * 根据名称获取状态机元素
     *
     * @param stateMachineName 状态机名称
     * @return 状态机元素
     * @throws StateMachineNotFoundException   状态机未找到异常
     * @throws StateMachineDuplicatedException 状态机重名异常
     */
    public UmlStateMachine getUmlStateMachineByName(String stateMachineName)
            throws StateMachineNotFoundException,
            StateMachineDuplicatedException {
        if (this.umlStateMachineNameGroups.containsKey(stateMachineName)) {
            List<UmlStateMachine> stateMachines =
                    this.umlStateMachineNameGroups.get(stateMachineName);
            if (stateMachines.size() > 1) {
                throw new StateMachineDuplicatedException(stateMachineName);
            } else if (stateMachines.isEmpty()) {
                throw new StateMachineNotFoundException(stateMachineName);
            } else {
                return stateMachines.get(0);
            }
        } else {
            throw new StateMachineNotFoundException(stateMachineName);
        }
    }

    /**
     * 获取状态机下的域元素
     *
     * @param umlStateMachine 状态机元素
     * @return 域元素
     */
    private UmlRegion getRegionForStateMachine(
            UmlStateMachine umlStateMachine) {
        return this.umlRegionForStateMachine.get(umlStateMachine);
    }

    /**
     * 获取状态机下的状态集合
     *
     * @param umlStateMachine 状态机元素
     * @return 域元素
     */
    public Set<UmlElement> getStatesFromStateMachine(
            UmlStateMachine umlStateMachine) {
        return this.umlStatesForRegions.getOrDefault(
                this.getRegionForStateMachine(umlStateMachine), new HashSet<>()
        );
    }

    /**
     * 根据名称在指定状态机元素下获取状态元素
     *
     * @param umlStateMachine 状态机元素
     * @param stateName       状态名称
     * @return 状态元素
     * @throws StateDuplicatedException 状态重名异常
     * @throws StateNotFoundException   状态未找到异常
     */
    public UmlState getStateByName(
            UmlStateMachine umlStateMachine, String stateName)
            throws StateDuplicatedException, StateNotFoundException {
        List<UmlState> states =
                this.getStatesFromStateMachine(umlStateMachine).stream()
                        .filter(umlElement -> Objects
                                .equals(umlElement.getName(), stateName))
                        .filter(umlElement -> (umlElement instanceof UmlState))
                        .map(umlElement -> (UmlState) umlElement)
                        .collect(Collectors.toList());
        if (states.size() > 1) {
            throw new StateDuplicatedException(
                    umlStateMachine.getName(), stateName);
        } else if (states.isEmpty()) {
            throw new StateNotFoundException(
                    umlStateMachine.getName(), stateName);
        } else {
            return states.get(0);
        }
    }

    /**
     * 获取状态的直接目标状态集合
     *
     * @param sourceState 状态
     * @return 目标状态集合
     */
    public Set<UmlElement> getTargetStates(UmlElement sourceState) {
        return this.umlTransitionsPairs
                .getOrDefault(sourceState, new HashSet<>());
    }

    /**
     * 获取状态机内全部的状态转移
     *
     * @param umlStateMachine 状态机元素
     * @return 状态转移集合
     */
    public Set<UmlTransition> getTransitionFromStateMachine(
            UmlStateMachine umlStateMachine) {
        return this.umlTransitionsForRegion.getOrDefault(
                this.getRegionForStateMachine(umlStateMachine), new HashSet<>()
        );
    }
}
