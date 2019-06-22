package com.oocourse.uml2.interact.format;

import com.oocourse.uml2.interact.exceptions.user.StateDuplicatedException;
import com.oocourse.uml2.interact.exceptions.user.StateMachineDuplicatedException;
import com.oocourse.uml2.interact.exceptions.user.StateMachineNotFoundException;
import com.oocourse.uml2.interact.exceptions.user.StateNotFoundException;

/**
 * UML状态图交互
 */
public interface UmlStateChartInteraction {
    /**
     * 获取状态机的状态数
     *
     * @param stateMachineName 状态机名称
     * @return 状态数
     * @throws StateMachineNotFoundException   状态机未找到
     * @throws StateMachineDuplicatedException 状态机存在重名
     */
    int getStateCount(String stateMachineName)
            throws StateMachineNotFoundException, StateMachineDuplicatedException;

    /**
     * 获取状态机转移数
     *
     * @param stateMachineName 状态机名称
     * @return 转移数
     * @throws StateMachineNotFoundException   状态机未找到
     * @throws StateMachineDuplicatedException 状态机存在重名
     */
    int getTransitionCount(String stateMachineName)
            throws StateMachineNotFoundException, StateMachineDuplicatedException;

    /**
     * 获取后继状态数
     *
     * @param stateMachineName 状态机名称
     * @param stateName        状态名称
     * @return 后继状态数
     * @throws StateMachineNotFoundException   状态机未找到
     * @throws StateMachineDuplicatedException 状态机存在重名
     * @throws StateNotFoundException          状态未找到
     * @throws StateDuplicatedException        状态存在重名
     */
    int getSubsequentStateCount(String stateMachineName, String stateName)
            throws StateMachineNotFoundException, StateMachineDuplicatedException,
            StateNotFoundException, StateDuplicatedException;
}
