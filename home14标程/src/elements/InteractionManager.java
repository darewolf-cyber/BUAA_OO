package elements;

import com.oocourse.uml2.interact.exceptions.user.InteractionDuplicatedException;
import com.oocourse.uml2.interact.exceptions.user.InteractionNotFoundException;
import com.oocourse.uml2.interact.exceptions.user.LifelineDuplicatedException;
import com.oocourse.uml2.interact.exceptions.user.LifelineNotFoundException;
import com.oocourse.uml2.models.elements.UmlElement;
import com.oocourse.uml2.models.elements.UmlInteraction;
import com.oocourse.uml2.models.elements.UmlLifeline;
import com.oocourse.uml2.models.elements.UmlMessage;
import com.oocourse.uml2.utils.common.GenericPair;

import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

/**
 * 交互元素管理器
 * 注意：
 * 1、官方接口没有为UmlLifeline和UmlEndPoint统一抽象
 * 2、基于上述原因，此处的存储均以UmlElement的形式进行
 */
@SuppressWarnings({"WeakerAccess", "FieldCanBeLocal"})
public class InteractionManager {
    private final ElementPool<UmlElement> elementPool;
    private final Set<UmlInteraction> umlInteractions;
    private final Map<String, List<UmlInteraction>> umlInteractionNameGroups;

    private final Set<UmlLifeline> umlLifelines;
    private final Map<UmlInteraction, Set<UmlLifeline>>
            umlInteractionsWithLifeline;
    private final Map<GenericPair<UmlInteraction, String>, List<UmlLifeline>>
            umlInteractionsWithLifelineAndName;

    private final Set<UmlMessage> umlMessages;
    private final Map<UmlInteraction, Set<UmlMessage>>
            umlInteractionsWithMessage;
    private final Map<UmlMessage, UmlElement> umlMessageSources;
    private final Map<UmlElement, Set<UmlMessage>> umlOutgoingMessages;
    private final Map<UmlMessage, UmlElement> umlMessageTargets;
    private final Map<UmlElement, Set<UmlMessage>> umlIncomingMessages;

    /**
     * 构造函数
     *
     * @param elementPool 元素池
     */
    public InteractionManager(ElementPool<UmlElement> elementPool) {
        this.elementPool = elementPool;
        this.umlInteractions = this.elementPool
                .getElementsWithType(UmlInteraction.class);
        this.umlInteractionNameGroups = this.umlInteractions.stream()
                .collect(Collectors.groupingBy(
                        UmlInteraction::getName
                ));

        this.umlLifelines = this.elementPool
                .getElementsWithType(UmlLifeline.class);
        this.umlInteractionsWithLifeline = this.umlLifelines.stream()
                .collect(Collectors.groupingBy(umlLifeline -> this.elementPool
                                .getElementById(umlLifeline.getParentId(),
                                        UmlInteraction.class),
                        Collectors.toSet()
                ));
        this.umlInteractionsWithLifelineAndName = this.umlLifelines.stream()
                .collect(Collectors.groupingBy(umlLifeline -> new GenericPair<>(
                        this.elementPool
                                .getElementById(umlLifeline.getParentId(),
                                        UmlInteraction.class),
                        umlLifeline.getName()
                )));

        this.umlMessages = this.elementPool
                .getElementsWithType(UmlMessage.class);
        this.umlInteractionsWithMessage = this.umlMessages.stream()
                .collect(Collectors.groupingBy(umlMessage -> this.elementPool
                                .getElementById(umlMessage.getParentId(),
                                        UmlInteraction.class),
                        Collectors.toSet()
                ));
        this.umlMessageSources = this.umlMessages.stream()
                .collect(Collectors.toMap(umlMessage ->
                        umlMessage, umlMessage ->
                        this.elementPool.getElementById(umlMessage.getSource())
                ));
        this.umlOutgoingMessages = this.umlMessageSources.entrySet().stream()
                .collect(Collectors.groupingBy(
                        Map.Entry::getValue,
                        Collectors.mapping(
                                Map.Entry::getKey,
                                Collectors.toSet()
                        )
                ));
        this.umlMessageTargets = this.umlMessages.stream()
                .collect(Collectors.toMap(umlMessage ->
                        umlMessage, umlMessage ->
                        this.elementPool.getElementById(umlMessage.getTarget())
                ));
        this.umlIncomingMessages = this.umlMessageTargets.entrySet().stream()
                .collect(Collectors.groupingBy(
                        Map.Entry::getValue,
                        Collectors.mapping(
                                Map.Entry::getKey,
                                Collectors.toSet()
                        )
                ));
    }

    /**
     * 判断是否包含交互元素
     *
     * @param umlInteraction 交互元素
     * @return 是否包含交互元素
     */
    public boolean containsUmlInteraction(UmlInteraction umlInteraction) {
        return this.umlInteractions.contains(umlInteraction);
    }

    /**
     * 根据名称获取交互对象
     *
     * @param interactionName 交互名称
     * @return 交互对象
     * @throws InteractionNotFoundException   交互未找到异常
     * @throws InteractionDuplicatedException 交互重名异常
     */
    public UmlInteraction getUmlInteractionByName(String interactionName)
            throws InteractionNotFoundException,
            InteractionDuplicatedException {
        if (this.umlInteractionNameGroups.containsKey(interactionName)) {
            List<UmlInteraction> interactions =
                    this.umlInteractionNameGroups.get(interactionName);
            if (interactions.size() > 1) {
                throw new InteractionDuplicatedException(interactionName);
            } else if (interactions.isEmpty()) {
                throw new InteractionNotFoundException(interactionName);
            } else {
                return interactions.get(0);
            }
        } else {
            throw new InteractionNotFoundException(interactionName);
        }
    }

    /**
     * 在指定交互元素下获取生命线集合
     *
     * @param umlInteraction 交互元素
     * @return 生命线集合
     */
    public Set<UmlLifeline> getUmlLifelines(UmlInteraction umlInteraction) {
        return this.umlInteractionsWithLifeline
                .getOrDefault(umlInteraction, new HashSet<>());
    }

    /**
     * 在指定交互元素下根据生命线名称获取生命线对象
     *
     * @param umlInteraction 交互元素
     * @param lifelineName   生命线名称
     * @return 生命线对象
     * @throws LifelineNotFoundException   生命线未找到异常
     * @throws LifelineDuplicatedException 生命线重名异常
     */
    public UmlLifeline getUmlLifelineByName(
            UmlInteraction umlInteraction, String lifelineName)
            throws LifelineNotFoundException, LifelineDuplicatedException {
        GenericPair<UmlInteraction, String> queryKey =
                new GenericPair<>(umlInteraction, lifelineName);
        if (this.umlInteractionsWithLifelineAndName.containsKey(queryKey)) {
            List<UmlLifeline> lifelines =
                    this.umlInteractionsWithLifelineAndName.get(queryKey);
            if (lifelines.size() > 1) {
                throw new LifelineDuplicatedException(
                        umlInteraction.getName(), lifelineName);
            } else if (lifelines.isEmpty()) {
                throw new LifelineNotFoundException(
                        umlInteraction.getName(), lifelineName);
            } else {
                return lifelines.get(0);
            }
        } else {
            throw new LifelineNotFoundException(
                    umlInteraction.getName(), lifelineName);
        }
    }

    /**
     * 获取指定交互元素下的消息集合
     *
     * @param umlInteraction 交互元素
     * @return 消息集合
     */
    public Set<UmlMessage> getUmlMessages(UmlInteraction umlInteraction) {
        return this.umlInteractionsWithMessage
                .getOrDefault(umlInteraction, new HashSet<>());
    }

    /**
     * 获取指定元素的进入消息集合
     *
     * @param umlElement 元素
     * @return 进入消息集合
     */
    public Set<UmlMessage> getIncomingMessages(UmlElement umlElement) {
        return this.umlIncomingMessages
                .getOrDefault(umlElement, new HashSet<>());
    }

    /**
     * 获取指定元素的对外消息集合
     *
     * @param umlElement 元素
     * @return 对外消息集合
     */
    public Set<UmlMessage> getOutgoingMessages(UmlElement umlElement) {
        return this.umlOutgoingMessages
                .getOrDefault(umlElement, new HashSet<>());
    }
}
