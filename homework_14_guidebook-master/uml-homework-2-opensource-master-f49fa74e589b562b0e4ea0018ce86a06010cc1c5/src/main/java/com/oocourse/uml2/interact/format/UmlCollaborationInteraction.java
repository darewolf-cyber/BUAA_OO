package com.oocourse.uml2.interact.format;

import com.oocourse.uml2.interact.exceptions.user.InteractionDuplicatedException;
import com.oocourse.uml2.interact.exceptions.user.InteractionNotFoundException;
import com.oocourse.uml2.interact.exceptions.user.LifelineDuplicatedException;
import com.oocourse.uml2.interact.exceptions.user.LifelineNotFoundException;

/**
 * UML顺序图交互
 */
public interface UmlCollaborationInteraction {
    /**
     * 获取参与对象数
     *
     * @param interactionName 交互名称
     * @return 参与对象数
     * @throws InteractionNotFoundException   交互未找到
     * @throws InteractionDuplicatedException 交互重名
     */
    int getParticipantCount(String interactionName)
            throws InteractionNotFoundException, InteractionDuplicatedException;

    /**
     * 获取消息数
     *
     * @param interactionName 交互名称
     * @return 消息数
     * @throws InteractionNotFoundException   交互未找到
     * @throws InteractionDuplicatedException 交互重名
     */
    int getMessageCount(String interactionName)
            throws InteractionNotFoundException, InteractionDuplicatedException;

    /**
     * 获取对象的进入消息数
     *
     * @param interactionName 交互名称
     * @param lifelineName    消息名称
     * @return 进入消息数
     * @throws InteractionNotFoundException   交互未找到
     * @throws InteractionDuplicatedException 交互重名
     * @throws LifelineNotFoundException      生命线未找到
     * @throws LifelineDuplicatedException    生命线重名
     */
    int getIncomingMessageCount(String interactionName, String lifelineName)
            throws InteractionNotFoundException, InteractionDuplicatedException,
            LifelineNotFoundException, LifelineDuplicatedException;
}
