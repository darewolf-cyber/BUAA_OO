package elements;

import com.oocourse.uml2.interact.common.AttributeClassInformation;
import com.oocourse.uml2.interact.common.AttributeQueryType;
import com.oocourse.uml2.interact.common.OperationQueryType;
import com.oocourse.uml2.interact.exceptions.user.AttributeDuplicatedException;
import com.oocourse.uml2.interact.exceptions.user.AttributeNotFoundException;
import com.oocourse.uml2.interact.exceptions.user.ClassDuplicatedException;
import com.oocourse.uml2.interact.exceptions.user.ClassNotFoundException;
import com.oocourse.uml2.interact.exceptions.user.InteractionDuplicatedException;
import com.oocourse.uml2.interact.exceptions.user.InteractionNotFoundException;
import com.oocourse.uml2.interact.exceptions.user.LifelineDuplicatedException;
import com.oocourse.uml2.interact.exceptions.user.LifelineNotFoundException;
import com.oocourse.uml2.interact.exceptions.user.StateDuplicatedException;
import com.oocourse.uml2.interact.exceptions.user.StateMachineDuplicatedException;
import com.oocourse.uml2.interact.exceptions.user.StateMachineNotFoundException;
import com.oocourse.uml2.interact.exceptions.user.StateNotFoundException;
import com.oocourse.uml2.interact.exceptions.user.UmlRule002Exception;
import com.oocourse.uml2.interact.exceptions.user.UmlRule008Exception;
import com.oocourse.uml2.interact.exceptions.user.UmlRule009Exception;
import com.oocourse.uml2.interact.format.UmlGeneralInteraction;
import com.oocourse.uml2.models.common.Visibility;
import com.oocourse.uml2.models.elements.UmlAssociationEnd;
import com.oocourse.uml2.models.elements.UmlAttribute;
import com.oocourse.uml2.models.elements.UmlClass;
import com.oocourse.uml2.models.elements.UmlClassOrInterface;
import com.oocourse.uml2.models.elements.UmlElement;
import com.oocourse.uml2.models.elements.UmlInteraction;
import com.oocourse.uml2.models.elements.UmlInterface;
import com.oocourse.uml2.models.elements.UmlLifeline;
import com.oocourse.uml2.models.elements.UmlOperation;
import com.oocourse.uml2.models.elements.UmlState;
import com.oocourse.uml2.models.elements.UmlStateMachine;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Queue;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.Stream;

/**
 * 交互类
 * 里面方法都知道啥意思，就不写注释了
 */
@SuppressWarnings("FieldCanBeLocal")
public class MyGeneralInteraction implements UmlGeneralInteraction {
    private final ElementPool<UmlElement> elementPool;
    private final ClassManager classManager;
    private final ClassAttributeManager classAttributeManager;
    private final InterfaceManager interfaceManager;
    private final ClassOperationManager classOperationManager;
    private final AssociationManager associationManager;
    private final InteractionManager interactionManager;
    private final StateMachineManager stateMachineManager;

    public MyGeneralInteraction(UmlElement... elements) {
        this.elementPool = new ElementPool<>(elements);
        this.classManager = new ClassManager(elementPool);
        this.classAttributeManager =
                new ClassAttributeManager(elementPool, classManager);
        this.interfaceManager = new InterfaceManager(elementPool, classManager);
        this.classOperationManager = new ClassOperationManager(elementPool);
        this.associationManager = new AssociationManager(elementPool);
        this.interactionManager = new InteractionManager(elementPool);
        this.stateMachineManager = new StateMachineManager(elementPool);
    }

    @Override
    public int getClassCount() {
        return this.classManager.size();
    }

    @Override
    public int getClassOperationCount(String className,
                                      OperationQueryType operationQueryType)
            throws ClassNotFoundException, ClassDuplicatedException {
        UmlClass umlClass = this.classManager.getUmlClassByName(className);
        Set<UmlOperation> operations = this.classOperationManager
                .getUmlOperations(umlClass);
        return (int) operations.stream()
                .filter(umlOperation -> this.classOperationManager
                        .isType(umlOperation, operationQueryType))
                .count();
    }

    @Override
    public int getClassAttributeCount(String className,
                                      AttributeQueryType attributeQueryType)
            throws ClassNotFoundException, ClassDuplicatedException {
        UmlClass umlClass = this.classManager.getUmlClassByName(className);
        int totalCount = 0;
        while (true) {
            totalCount += this.classAttributeManager
                    .getAttributesForClass(umlClass).size();
            UmlClass parentClass = this.classManager.getParentClass(umlClass);
            if (parentClass != null && attributeQueryType
                    == AttributeQueryType.ALL) {
                umlClass = parentClass;
            } else {
                break;
            }
        }
        return totalCount;
    }

    @Override
    public int getClassAssociationCount(String className)
            throws ClassNotFoundException, ClassDuplicatedException {
        UmlClass umlClass = this.classManager.getUmlClassByName(className);
        Set<UmlAssociationEnd> associationEnds = new HashSet<>();
        while (umlClass != null) {
            associationEnds.addAll(this.associationManager
                    .getUmlAssociationOppositeEnds(umlClass));
            umlClass = this.classManager.getParentClass(umlClass);
        }
        return associationEnds.size();
    }

    @Override
    public List<String> getClassAssociatedClassList(String className)
            throws ClassNotFoundException, ClassDuplicatedException {
        UmlClass umlClass = this.classManager.getUmlClassByName(className);
        Stream<UmlElement> elementStream = this.associationManager
                .getUmlAssociatedElements(umlClass).stream();
        while (umlClass != null) {
            umlClass = this.classManager.getParentClass(umlClass);
            if (umlClass != null) {
                elementStream = Stream.concat(elementStream,
                        this.associationManager
                                .getUmlAssociatedElements(umlClass).stream());
            }
        }
        return elementStream.collect(Collectors.toSet()).stream()
                .filter(umlElement -> umlElement instanceof UmlClass)
                .map(UmlElement::getName)
                .collect(Collectors.toList());
    }

    @Override
    public Map<Visibility, Integer> getClassOperationVisibility(
            String className, String operationName)
            throws ClassNotFoundException, ClassDuplicatedException {
        UmlClass umlClass = this.classManager.getUmlClassByName(className);
        Set<UmlOperation> operations = this.classOperationManager
                .getUmlOperations(umlClass);
        return operations.stream()
                .filter(umlOperation -> Objects
                        .equals(umlOperation.getName(), operationName))
                .collect(Collectors.groupingBy(
                        UmlOperation::getVisibility,
                        Collectors.collectingAndThen(
                                Collectors.counting(),
                                Long::intValue
                        )
                ));
    }

    @Override
    public Visibility getClassAttributeVisibility(
            String className, String attributeName)
            throws ClassNotFoundException, ClassDuplicatedException,
            AttributeNotFoundException, AttributeDuplicatedException {
        UmlClass umlClass = this.classManager.getUmlClassByName(className);
        UmlAttribute umlAttribute = this.classAttributeManager
                .getUmlAttributeInAllClasses(umlClass, attributeName);
        return umlAttribute.getVisibility();
    }

    @Override
    public String getTopParentClass(String className)
            throws ClassNotFoundException, ClassDuplicatedException {
        UmlClass umlClass = this.classManager.getUmlClassByName(className);
        while (this.classManager.getParentClass(umlClass) != null) {
            umlClass = this.classManager.getParentClass(umlClass);
        }
        return umlClass.getName();
    }

    @Override
    public List<String> getImplementInterfaceList(String className)
            throws ClassNotFoundException, ClassDuplicatedException {
        UmlClass umlClass = this.classManager.getUmlClassByName(className);
        Set<UmlInterface> interfaces = this.interfaceManager
                .getImplementInterfacesByClass(umlClass);
        return interfaces.stream()
                .map(UmlInterface::getName)
                .collect(Collectors.toList());
    }

    @Override
    public List<AttributeClassInformation> getInformationNotHidden(
            String className)
            throws ClassNotFoundException, ClassDuplicatedException {
        UmlClass currentClass = this.classManager.getUmlClassByName(className);
        List<AttributeClassInformation> result = new ArrayList<>();
        while (currentClass != null) {
            Set<UmlAttribute> unhiddenAttributes = this.classAttributeManager
                    .getAttributesForClass(currentClass).stream()
                    .filter(umlAttribute -> umlAttribute
                            .getVisibility() != Visibility.PRIVATE)
                    .collect(Collectors.toSet());
            for (UmlAttribute attribute : unhiddenAttributes) {
                UmlClass attributeClass = this.classAttributeManager
                        .getUmlClassForAttribute(attribute);
                result.add(new AttributeClassInformation(
                        attribute.getName(), attributeClass.getName()));
            }
            currentClass = this.classManager.getParentClass(currentClass);
        }
        return result;
    }

    @Override
    public int getParticipantCount(String interactionName)
            throws InteractionNotFoundException,
            InteractionDuplicatedException {
        UmlInteraction umlInteraction = this.interactionManager
                .getUmlInteractionByName(interactionName);
        return this.interactionManager.getUmlLifelines(umlInteraction).size();
    }

    @Override
    public int getMessageCount(String interactionName)
            throws InteractionNotFoundException,
            InteractionDuplicatedException {
        UmlInteraction umlInteraction = this.interactionManager
                .getUmlInteractionByName(interactionName);
        return this.interactionManager.getUmlMessages(umlInteraction).size();
    }

    @Override
    public int getIncomingMessageCount(
            String interactionName, String lifelineName)
            throws InteractionNotFoundException,
            InteractionDuplicatedException,
            LifelineNotFoundException, LifelineDuplicatedException {
        UmlInteraction umlInteraction = this.interactionManager
                .getUmlInteractionByName(interactionName);
        UmlLifeline umlLifeline = this.interactionManager
                .getUmlLifelineByName(umlInteraction, lifelineName);
        return this.interactionManager.getIncomingMessages(umlLifeline).size();
    }

    @Override
    public void checkForUml002() throws UmlRule002Exception {
        Set<AttributeClassInformation> result = new HashSet<>();
        for (UmlClass umlClass : this.classManager) {
            Set<UmlAttribute> attributes = this.classAttributeManager
                    .getAttributesForClass(umlClass);
            Set<UmlAssociationEnd> associationEnds = this.associationManager
                    .getUmlAssociationOppositeEnds(umlClass);
            Set<String> duplicatedNames = Stream.concat(
                    attributes.stream(),
                    associationEnds.stream()
            )
                    .filter(umlElement -> umlElement.getName() != null)
                    .collect(Collectors.groupingBy(
                            UmlElement::getName,
                            Collectors.collectingAndThen(
                                    Collectors.counting(),
                                    Long::intValue
                            )
                    )).entrySet().stream()
                    .filter(entry -> entry.getValue() > 1)
                    .map(Map.Entry::getKey)
                    .collect(Collectors.toSet());
            for (String elementName : duplicatedNames) {
                result.add(new AttributeClassInformation(
                        elementName,
                        umlClass.getName()
                ));
            }
        }
        if (!result.isEmpty()) {
            throw new UmlRule002Exception(result);
        }
    }

    @Override
    public void checkForUml008() throws UmlRule008Exception {
        HashSet<UmlClassOrInterface> result = new HashSet<>();
        for (UmlClass umlClass : this.classManager) {
            Queue<UmlClass> queue = new LinkedList<>();
            Set<UmlClass> visitedClasses = new HashSet<>();
            queue.offer(umlClass);
            visitedClasses.add(umlClass);
            boolean hasCircle = false;
            while (!queue.isEmpty()) {
                UmlClass head = queue.poll();
                UmlClass parentClass = this.classManager.getParentClass(head);
                if (parentClass != null) {
                    if (Objects.equals(parentClass, umlClass)) {
                        hasCircle = true;
                        break;
                    }
                    if (!visitedClasses.contains(parentClass)) {
                        visitedClasses.add(parentClass);
                        queue.offer(parentClass);
                    }
                }
            }
            if (hasCircle) {
                result.add(umlClass);
            }
        }

        for (UmlInterface umlInterface : this.interfaceManager) {
            Queue<UmlInterface> queue = new LinkedList<>();
            Set<UmlInterface> visitedInterfaces = new HashSet<>();
            queue.offer(umlInterface);
            visitedInterfaces.add(umlInterface);
            boolean hasCircle = false;
            while (!queue.isEmpty()) {
                UmlInterface head = queue.poll();
                for (UmlInterface item : this.interfaceManager
                        .getDirectlyExtendInterfacesByInterface(head)) {
                    if (Objects.equals(item, umlInterface)) {
                        hasCircle = true;
                        break;
                    }
                    if (!visitedInterfaces.contains(item)) {
                        visitedInterfaces.add(item);
                        queue.offer(item);
                    }
                }
            }
            if (hasCircle) {
                result.add(umlInterface);
            }
        }

        if (!result.isEmpty()) {
            throw new UmlRule008Exception(result);
        }
    }

    @Override
    public void checkForUml009() throws UmlRule009Exception {
        Set<UmlClassOrInterface> umlClassOrInterfaces = Stream.concat(
                this.classManager.stream(),
                this.interfaceManager.stream()
        ).collect(Collectors.toSet());
        Set<UmlClassOrInterface> result = new HashSet<>();
        for (UmlClassOrInterface classOrInterface : umlClassOrInterfaces) {
            Set<UmlClassOrInterface> visited = new HashSet<>();
            Queue<UmlClassOrInterface> queue = new LinkedList<>();
            visited.add(classOrInterface);
            queue.offer(classOrInterface);
            boolean hasDuplicated = false;
            while (!queue.isEmpty()) {
                UmlClassOrInterface head = queue.poll();
                List<UmlInterface> interfaces = new ArrayList<>();
                if (head instanceof UmlClass) {
                    UmlClass umlClass = (UmlClass) head;
                    UmlClass parentClass = this.classManager
                            .getParentClass(umlClass);
                    if (parentClass != null) {
                        if (!visited.contains(parentClass)) {
                            visited.add(parentClass);
                            queue.offer(parentClass);
                        } else {
                            hasDuplicated = true;
                            break;
                        }
                    }
                    interfaces = this.interfaceManager
                            .getDirectlyImplementInterfaceListByClass(umlClass);
                } else if (head instanceof UmlInterface) {
                    UmlInterface umlInterface = (UmlInterface) head;
                    interfaces = this.interfaceManager
                            .getDirectlyExtendInterfaceListByInterface(
                                    umlInterface);
                }
                for (UmlInterface umlInterface : interfaces) {
                    if (!visited.contains(umlInterface)) {
                        visited.add(umlInterface);
                        queue.offer(umlInterface);
                    } else {
                        hasDuplicated = true;
                        break;
                    }
                }
            }

            if (hasDuplicated) {
                result.add(classOrInterface);
            }
        }
        if (!result.isEmpty()) {
            throw new UmlRule009Exception(result);
        }
    }

    @Override
    public int getStateCount(String stateMachineName)
            throws StateMachineNotFoundException,
            StateMachineDuplicatedException {
        UmlStateMachine umlStateMachine = this.stateMachineManager
                .getUmlStateMachineByName(stateMachineName);
        return this.stateMachineManager
                .getStatesFromStateMachine(umlStateMachine).size();
    }

    @Override
    public int getTransitionCount(String stateMachineName)
            throws StateMachineNotFoundException,
            StateMachineDuplicatedException {
        UmlStateMachine umlStateMachine = this.stateMachineManager
                .getUmlStateMachineByName(stateMachineName);
        return this.stateMachineManager
                .getTransitionFromStateMachine(umlStateMachine).size();
    }

    @Override
    public int getSubsequentStateCount(
            String stateMachineName, String stateName)
            throws StateMachineNotFoundException,
            StateMachineDuplicatedException,
            StateNotFoundException, StateDuplicatedException {
        UmlStateMachine umlStateMachine = this.stateMachineManager
                .getUmlStateMachineByName(stateMachineName);
        UmlState umlState = this.stateMachineManager
                .getStateByName(umlStateMachine, stateName);

        Set<UmlElement> visited = new HashSet<>();
        Set<UmlElement> result = new HashSet<>();
        Queue<UmlElement> queue = new LinkedList<>();
        visited.add(umlState);
        queue.offer(umlState);
        while (!queue.isEmpty()) {
            UmlElement head = queue.poll();
            for (UmlElement next :
                    this.stateMachineManager.getTargetStates(head)) {
                if (!visited.contains(next)) {
                    visited.add(next);
                    queue.offer(next);
                }
                result.add(next);
            }
        }
        return result.size();
    }
}
