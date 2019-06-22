import com.oocourse.uml2.interact.exceptions.user.StateDuplicatedException;
import com.oocourse.uml2.interact.exceptions.user.StateMachineDuplicatedException;
import com.oocourse.uml2.interact.exceptions.user.StateMachineNotFoundException;
import com.oocourse.uml2.interact.exceptions.user.StateNotFoundException;
import com.oocourse.uml2.interact.format.UmlStateChartInteraction;
import com.oocourse.uml2.models.elements.UmlElement;
import com.oocourse.uml2.models.elements.UmlTransition;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;

public class MyUmlStateChartInteraction implements UmlStateChartInteraction {
    //StateMachineID->transCnt
    private HashMap<String,Integer> transCount = new HashMap<>();
    //StateMachineName->List<StateMachineID>
    private HashMap<String,ArrayList<String>> name2id = new HashMap<>();
    //StateMachineID->stateName->List<stateID>
    private HashMap<String,HashMap<String,ArrayList<String>>>
            stateList = new HashMap<>();
    //StateMachineID->List<stateID>
    private HashMap<String,HashSet<String>> states = new HashMap<>();
    //stateID->nextStateID
    private HashMap<String,HashSet<String>> nextState = new HashMap<>();

    MyUmlStateChartInteraction(UmlElement... elements) {
        HashMap<String,String> parent = new HashMap<>();
        ArrayList<UmlElement> level1list = new ArrayList<>();
        for (UmlElement e : elements) {
            parent.put(e.getId(),e.getParentId());
            switch (e.getElementType()) {
                case UML_STATE_MACHINE:
                    if (!name2id.containsKey(e.getName())) {
                        name2id.put(e.getName(), new ArrayList<>());
                    }
                    name2id.get(e.getName()).add(e.getId());
                    if (!transCount.containsKey(e.getId())) {
                        transCount.put(e.getId(), 0);
                    }
                    if (!states.containsKey(e.getId())) {
                        states.put(e.getId(), new HashSet<>());
                    }
                    if (!stateList.containsKey(e.getId())) {
                        stateList.put(e.getId(), new HashMap<>());
                    }
                    break;
                case UML_STATE:
                case UML_PSEUDOSTATE:
                case UML_FINAL_STATE:
                case UML_TRANSITION:
                    level1list.add(e);
                    break;
                default:
                    break;
            }
        }
        for (UmlElement e : level1list) {
            String machineId = parent.get(e.getParentId());
            switch (e.getElementType()) {
                case UML_STATE:
                case UML_PSEUDOSTATE:
                case UML_FINAL_STATE:
                    if (!stateList.containsKey(machineId)) {
                        stateList.put(machineId,new HashMap<>());
                    }
                    if (!stateList.get(machineId).containsKey(e.getName())) {
                        stateList.get(machineId).put(e.getName(),
                                new ArrayList<>());
                    }
                    stateList.get(machineId).get(e.getName()).add(e.getId());
                    if (!states.containsKey(machineId)) {
                        states.put(machineId,new HashSet<>());
                    }
                    states.get(machineId).add(e.getId());
                    break;
                case UML_TRANSITION:
                    if (!transCount.containsKey(machineId)) {
                        transCount.put(machineId,0);
                    }
                    transCount.put(machineId,transCount.get(machineId) + 1);
                    String sourceG = ((UmlTransition)e).getSource();
                    String targetG = ((UmlTransition)e).getTarget();
                    if (!nextState.containsKey(sourceG)) {
                        nextState.put(sourceG, new HashSet<>());
                    }
                    nextState.get(sourceG).add(targetG);
                    break;
                default:
                    break;
            }
        }
    }

    @Override
    public int getStateCount(String stateMachineName)
            throws StateMachineNotFoundException,
            StateMachineDuplicatedException {
        if (!name2id.containsKey(stateMachineName)) {
            throw new StateMachineNotFoundException(stateMachineName);
        } else {
            if (name2id.get(stateMachineName).size() > 1) {
                throw new StateMachineDuplicatedException(stateMachineName);
            } else {
                String id = name2id.get(stateMachineName).get(0);
                return states.get(id).size();
            }
        }
    }

    @Override
    public int getTransitionCount(String stateMachineName)
            throws StateMachineNotFoundException,
            StateMachineDuplicatedException {
        if (!name2id.containsKey(stateMachineName)) {
            throw new StateMachineNotFoundException(stateMachineName);
        } else {
            if (name2id.get(stateMachineName).size() > 1) {
                throw new StateMachineDuplicatedException(stateMachineName);
            } else {
                String id = name2id.get(stateMachineName).get(0);
                return transCount.get(id);
            }
        }
    }

    @Override
    public int getSubsequentStateCount(String stateMachineName,
                                       String stateName)
            throws StateMachineNotFoundException,
            StateMachineDuplicatedException,
            StateNotFoundException, StateDuplicatedException {
        if (!name2id.containsKey(stateMachineName)) {
            throw new StateMachineNotFoundException(stateMachineName);
        } else {
            if (name2id.get(stateMachineName).size() > 1) {
                throw new StateMachineDuplicatedException(stateMachineName);
            } else {
                String id = name2id.get(stateMachineName).get(0);
                if (!stateList.containsKey(id)) {
                    System.err.println("!!!!");
                    return 0;
                }
                if (!stateList.get(id).containsKey(stateName)) {
                    throw new StateNotFoundException(
                            stateMachineName,stateName);
                } else {
                    if (stateList.get(id).get(stateName).size() > 1) {
                        throw new StateDuplicatedException(
                                stateMachineName,stateName);
                    } else {
                        String stateId = stateList.get(id).
                                get(stateName).get(0);
                        HashSet<String> vis = new HashSet<>(states.get(id));
                        LinkedList<String> queue = new LinkedList<>();
                        queue.addLast(stateId);
                        //vis.remove(stateId);
                        int cnt = 0;
                        while (!queue.isEmpty()) {
                            String tmp = queue.removeFirst();
                            if (nextState.containsKey(tmp)) {
                                for (String t : nextState.get(tmp)) {
                                    if (vis.contains(t)) {
                                        vis.remove(t);
                                        queue.addLast(t);
                                        cnt++;
                                    }
                                }
                            }
                        }
                        return cnt;
                    }
                }
            }
        }
    }
}
