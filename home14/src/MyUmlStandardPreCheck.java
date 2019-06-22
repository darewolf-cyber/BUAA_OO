import com.oocourse.uml2.interact.common.AttributeClassInformation;
import com.oocourse.uml2.interact.exceptions.user.UmlRule002Exception;
import com.oocourse.uml2.interact.exceptions.user.UmlRule008Exception;
import com.oocourse.uml2.interact.exceptions.user.UmlRule009Exception;
import com.oocourse.uml2.interact.format.UmlStandardPreCheck;
import com.oocourse.uml2.models.common.ElementType;
import com.oocourse.uml2.models.elements.UmlAssociation;
import com.oocourse.uml2.models.elements.UmlAssociationEnd;
import com.oocourse.uml2.models.elements.UmlClass;
import com.oocourse.uml2.models.elements.UmlClassOrInterface;
import com.oocourse.uml2.models.elements.UmlElement;
import com.oocourse.uml2.models.elements.UmlGeneralization;
import com.oocourse.uml2.models.elements.UmlInterface;
import com.oocourse.uml2.models.elements.UmlInterfaceRealization;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;

public class MyUmlStandardPreCheck implements UmlStandardPreCheck {
    private HashSet<String> interfaceSet = new HashSet<>();
    private HashSet<String> wrongInterfaceSet = new HashSet<>();
    private HashSet<String> classSet = new HashSet<>();
    private HashSet<AttributeClassInformation> set002 = new HashSet<>();
    private HashSet<UmlClassOrInterface> set008 = new HashSet<>();
    private HashSet<UmlClassOrInterface> set009 = new HashSet<>();
    private HashMap<String,UmlClass> idToClass = new HashMap<>();
    private HashMap<String,UmlInterface> idToInterface = new HashMap<>();
    private HashMap<String,ArrayList<String>> extendsWho = new HashMap<>();
    private HashMap<String,ArrayList<String>> implementsWho = new HashMap<>();

    MyUmlStandardPreCheck(UmlElement... elements) {
        HashMap<String,String> id2ref = new HashMap<>();
        HashMap<String,String> end2end = new HashMap<>();
        ArrayList<UmlElement> level1list = new ArrayList<>();
        HashMap<String, HashMap<String, Integer>> attrCnt = new HashMap<>();
        HashMap<String,String> id2name = new HashMap<>();
        for (UmlElement e : elements) {
            id2name.put(e.getId(),e.getName());
            switch (e.getElementType()) {
                case UML_CLASS:
                    attrCnt.put(e.getId(),new HashMap<>());
                    classSet.add(e.getId());
                    idToClass.put(e.getId(),(UmlClass)e);
                    break;
                case UML_INTERFACE:
                    interfaceSet.add(e.getId());
                    idToInterface.put(e.getId(),(UmlInterface)e);
                    break;
                default:
                    level1list.add(e);
                    break;
            }
        }
        ArrayList<UmlElement> level2list = new ArrayList<>();
        for (UmlElement e : level1list) {
            switch (e.getElementType()) {
                case UML_OPERATION:
                    break;
                case UML_ATTRIBUTE:
                    if (interfaceSet.contains(e.getParentId())) { break; }
                    if (e.getName() != null) {
                        if (!attrCnt.containsKey(e.getParentId())) {
                            attrCnt.put(e.getParentId(), new HashMap<>());
                        }
                        if (!attrCnt.get(e.getParentId()).containsKey(
                                e.getName())) {
                            attrCnt.get(e.getParentId()).put(e.getName(), 1);
                        } else {
                            attrCnt.get(e.getParentId()).put(e.getName(),
                                    attrCnt.get(e.getParentId()).
                                            get(e.getName()) + 1);
                            set002.add(new AttributeClassInformation(
                                    e.getName(), id2name.get(e.getParentId())));
                        }
                    }
                    break;
                case UML_PARAMETER:
                    break;
                case UML_GENERALIZATION:
                    String sourceG = ((UmlGeneralization)e).getSource();
                    String targetG = ((UmlGeneralization)e).getTarget();
                    if (!extendsWho.containsKey(sourceG)) {
                        extendsWho.put(sourceG,new ArrayList<>());
                    }
                    extendsWho.get(sourceG).add(targetG);
                    break;
                case UML_INTERFACE_REALIZATION:
                    String source = ((UmlInterfaceRealization)e).getSource();
                    String target = ((UmlInterfaceRealization)e).getTarget();
                    if (!implementsWho.containsKey(source)) {
                        implementsWho.put(source,new ArrayList<>());
                    }
                    implementsWho.get(source).add(target);
                    break;
                case UML_ASSOCIATION:
                    String end1 = ((UmlAssociation)e).getEnd1();
                    String end2 = ((UmlAssociation)e).getEnd2();
                    end2end.put(end1,end2);
                    end2end.put(end2,end1);
                    break;
                default:
                    level2list.add(e);
                    break;
            }
        }
        for (UmlElement e : level2list) {
            if (e.getElementType() == ElementType.UML_ASSOCIATION_END) {
                String ref = ((UmlAssociationEnd) e).getReference();
                id2ref.put(e.getId(), ref);
                if (end2end.containsKey(e.getId())) {
                    String to = end2end.get(e.getId());
                    if (id2ref.containsKey(to)) {
                        String ref2 = id2ref.get(to);
                        String name2 = id2name.get(to);
                        if (name2 != null) {
                            if (!attrCnt.containsKey(ref)) {
                                attrCnt.put(ref, new HashMap<>());
                            }
                            if (!attrCnt.get(ref).containsKey(name2)) {
                                attrCnt.get(ref).put(name2, 1);
                            } else {
                                attrCnt.get(ref).put(name2,
                                        attrCnt.get(ref).get(name2) + 1);
                                set002.add(new AttributeClassInformation(
                                        name2, id2name.get(ref)));
                            }
                        }
                        if (e.getName() != null) {
                            if (!attrCnt.containsKey(ref2)) {
                                attrCnt.put(ref2, new HashMap<>());
                            }
                            if (!attrCnt.get(ref2).containsKey(e.getName())) {
                                attrCnt.get(ref2).put(e.getName(), 1);
                            } else {
                                attrCnt.get(ref2).put(e.getName(),
                                        attrCnt.get(ref2).get(e.getName()) + 1);
                                set002.add(new AttributeClassInformation(
                                        e.getName(), id2name.get(ref2)));
                            }
                        }
                    }
                }
            }
        }
    }

    @Override
    public void checkForUml002() throws UmlRule002Exception {
        if (!set002.isEmpty()) {
            throw new UmlRule002Exception(set002);
        }
    }

    private HashSet<String> vis;
    private String start;

    private void dfs(String id) {
        vis.remove(id);
        if (extendsWho.containsKey(id)) {
            for (String s : extendsWho.get(id)) {
                if (vis.contains(s)) {
                    dfs(s);
                } else {
                    if (s.equals(start)) {
                        if (idToInterface.containsKey(start)) {
                            set008.add(idToInterface.get(start));
                        }
                        else if (idToClass.containsKey(start)) {
                            set008.add(idToClass.get(start));
                        }
                    }
                }
            }
        }
    }

    @Override
    public void checkForUml008() throws UmlRule008Exception {
        for (String id : classSet) {
            //朴素的dfs 每次只判断id自己能否回来 只加自己 不加整个环
            vis = new HashSet<>(classSet);
            start = id;
            dfs(id);
        }
        for (String id : interfaceSet) {
            //朴素的dfs 每次只判断id自己能否回来 只加自己 不加整个环
            vis = new HashSet<>(interfaceSet);
            start = id;
            dfs(id);
        }
        if (!set008.isEmpty()) {
            throw new UmlRule008Exception(set008);
        }
    }

    private boolean interfaceDuplicated(String id) {
        HashSet<String> set = new HashSet<>();
        LinkedList<String> queue = new LinkedList<>();
        queue.addLast(id);
        while (!queue.isEmpty()) {
            String tmp = queue.removeFirst();
            if (extendsWho.containsKey(tmp)) {
                for (String t : extendsWho.get(tmp)) { //t是父接口id
                    if (wrongInterfaceSet.contains(t)) {
                        return false;
                    }
                    queue.addLast(t);
                    if (set.contains(t)) {
                        return false;
                    } else {
                        set.add(t);
                    }
                }
            }
        }
        return true;
    }

    private boolean classDuplicated(HashSet<String> set,String id) {
        if (implementsWho.containsKey(id)) { //类直接实现的接口
            for (String s : implementsWho.get(id)) { //s是接口id
                if (wrongInterfaceSet.contains(s)) {
                    return false; //实现了重复接口
                }
                //s是正常接口（继承都是一次） 装入set
                LinkedList<String> queue = new LinkedList<>();
                queue.addLast(s);
                while (!queue.isEmpty()) {
                    String tmp = queue.removeFirst();
                    if (set.contains(tmp)) {
                        return false;
                    } else {
                        set.add(tmp);
                    }
                    if (extendsWho.containsKey(tmp)) {
                        for (String t : extendsWho.get(tmp)) {
                            queue.addLast(t);
                        }
                    }
                }
            }
        }
        return true;
    }

    @Override
    public void checkForUml009() throws UmlRule009Exception {
        for (String id : interfaceSet) {
            boolean ans = interfaceDuplicated(id);
            if (!ans) {
                set009.add(idToInterface.get(id));
                wrongInterfaceSet.add(id); //有问题的接口
            }
        }
        String pid;
        for (String id : classSet) { //遍历class
            HashSet<String> set = new HashSet<>();
            boolean ans = classDuplicated(set,id);
            if (!ans) {
                set009.add(idToClass.get(id));
                continue;
            }
            pid = id;
            while (extendsWho.containsKey(pid)) { //求父类的接口
                pid = extendsWho.get(pid).get(0); //父类id
                ans = classDuplicated(set,pid);
                if (!ans) {
                    set009.add(idToClass.get(id)); //子类
                    break;
                }
            }
        }
        if (!set009.isEmpty()) {
            throw new UmlRule009Exception(set009);
        }
    }
}
