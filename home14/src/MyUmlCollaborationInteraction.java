import com.oocourse.uml2.interact.exceptions.user.InteractionDuplicatedException;
import com.oocourse.uml2.interact.exceptions.user.InteractionNotFoundException;
import com.oocourse.uml2.interact.exceptions.user.LifelineDuplicatedException;
import com.oocourse.uml2.interact.exceptions.user.LifelineNotFoundException;
import com.oocourse.uml2.interact.format.UmlCollaborationInteraction;
import com.oocourse.uml2.models.elements.UmlElement;
import com.oocourse.uml2.models.elements.UmlMessage;

import java.util.ArrayList;
import java.util.HashMap;

public class MyUmlCollaborationInteraction implements
        UmlCollaborationInteraction {
    //InteractionName->List<InteractionID>
    private HashMap<String,ArrayList<String>> name2id = new HashMap<>();
    //InteractionID->lifelineName->List<lifelineID>
    private HashMap<String,HashMap<String,ArrayList<String>>>
            lifeLineList = new HashMap<>();
    //InteractionID->cnt
    private HashMap<String,Integer> messageCount = new HashMap<>();
    //InteractionID->cnt
    private HashMap<String,Integer> lifelineCount = new HashMap<>();
    //lifelineId->cnt
    private HashMap<String,Integer> incomingCount = new HashMap<>();

    MyUmlCollaborationInteraction(UmlElement... elements) {
        ArrayList<UmlElement> level1list = new ArrayList<>();
        for (UmlElement e : elements) {
            switch (e.getElementType()) {
                case UML_INTERACTION:
                    if (!name2id.containsKey(e.getName())) {
                        name2id.put(e.getName(), new ArrayList<>());
                    }
                    name2id.get(e.getName()).add(e.getId());
                    if (!messageCount.containsKey(e.getId())) {
                        messageCount.put(e.getId(), 0);
                    }
                    if (!lifelineCount.containsKey(e.getId())) {
                        lifelineCount.put(e.getId(), 0);
                    }
                    if (!lifeLineList.containsKey(e.getId())) {
                        lifeLineList.put(e.getId(), new HashMap<>());
                    }
                    break;
                case UML_LIFELINE:
                    if (!incomingCount.containsKey(e.getId())) {
                        incomingCount.put(e.getId(),0);
                    }
                    level1list.add(e);
                    break;
                case UML_MESSAGE:
                    level1list.add(e);
                    break;
                default:
                    break;
            }
        }
        for (UmlElement e : level1list) {
            String pid = e.getParentId();
            switch (e.getElementType()) {
                case UML_LIFELINE:
                    if (!lifeLineList.containsKey(pid)) {
                        lifeLineList.put(pid,new HashMap<>());
                    }
                    if (!lifeLineList.get(pid).containsKey(e.getName())) {
                        lifeLineList.get(pid).put(e.getName(),
                                new ArrayList<>());
                    }
                    lifeLineList.get(pid).get(e.getName()).add(e.getId());
                    if (!lifelineCount.containsKey(pid)) {
                        lifelineCount.put(pid,0);
                    }
                    lifelineCount.put(pid, lifelineCount.get(pid) + 1);
                    break;
                case UML_MESSAGE:
                    if (!messageCount.containsKey(pid)) {
                        messageCount.put(pid,0);
                    }
                    messageCount.put(pid, messageCount.get(pid) + 1);
                    String target = ((UmlMessage)e).getTarget();
                    if (!incomingCount.containsKey(target)) {
                        incomingCount.put(target,0);
                    }
                    incomingCount.put(target,incomingCount.get(target) + 1);
                    break;
                default:
                    break;
            }
        }
    }

    @Override
    public int getParticipantCount(String interactionName)
            throws InteractionNotFoundException,
            InteractionDuplicatedException {
        if (!name2id.containsKey(interactionName)) {
            throw new InteractionNotFoundException(interactionName);
        } else {
            if (name2id.get(interactionName).size() > 1) {
                throw new InteractionDuplicatedException(interactionName);
            } else {
                String id = name2id.get(interactionName).get(0);
                return lifelineCount.get(id);
            }
        }
    }

    @Override
    public int getMessageCount(String interactionName)
            throws InteractionNotFoundException,
            InteractionDuplicatedException {
        if (!name2id.containsKey(interactionName)) {
            throw new InteractionNotFoundException(interactionName);
        } else {
            if (name2id.get(interactionName).size() > 1) {
                throw new InteractionDuplicatedException(interactionName);
            } else {
                String id = name2id.get(interactionName).get(0);
                return messageCount.get(id);
            }
        }
    }

    @Override
    public int getIncomingMessageCount(String interactionName,
                                       String lifelineName)
            throws InteractionNotFoundException,
            InteractionDuplicatedException, LifelineNotFoundException,
            LifelineDuplicatedException {
        if (!name2id.containsKey(interactionName)) {
            throw new InteractionNotFoundException(interactionName);
        } else {
            if (name2id.get(interactionName).size() > 1) {
                throw new InteractionDuplicatedException(interactionName);
            } else {
                String id = name2id.get(interactionName).get(0);
                if (!lifeLineList.containsKey(id)) {
                    System.err.println("????");
                    return 0;
                }
                if (!lifeLineList.get(id).containsKey(lifelineName)) {
                    throw new LifelineNotFoundException(interactionName,
                            lifelineName);
                } else {
                    if (lifeLineList.get(id).get(lifelineName).size() > 1) {
                        throw new LifelineDuplicatedException(
                                interactionName,lifelineName);
                    } else {
                        String lifelineId = lifeLineList.get(id).
                                get(lifelineName).get(0);
                        return incomingCount.get(lifelineId);
                    }
                }
            }
        }
    }
}
