import com.oocourse.uml2.interact.common.AttributeClassInformation;
import com.oocourse.uml2.interact.common.AttributeQueryType;
import com.oocourse.uml2.interact.common.OperationQueryType;
import com.oocourse.uml2.interact.exceptions.user.AttributeDuplicatedException;
import com.oocourse.uml2.interact.exceptions.user.AttributeNotFoundException;
import com.oocourse.uml2.interact.exceptions.user.ClassDuplicatedException;
import com.oocourse.uml2.interact.exceptions.user.ClassNotFoundException;
import com.oocourse.uml2.interact.format.UmlClassModelInteraction;
import com.oocourse.uml2.models.common.ElementType;
import com.oocourse.uml2.models.common.Visibility;
import com.oocourse.uml2.models.elements.UmlAssociation;
import com.oocourse.uml2.models.elements.UmlAssociationEnd;
import com.oocourse.uml2.models.elements.UmlAttribute;
import com.oocourse.uml2.models.elements.UmlElement;
import com.oocourse.uml2.models.elements.UmlGeneralization;
import com.oocourse.uml2.models.elements.UmlInterfaceRealization;
import com.oocourse.uml2.models.elements.UmlOperation;
import com.oocourse.uml2.models.elements.UmlParameter;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

public class MyUmlClassModelInteraction implements UmlClassModelInteraction {
    private int classCount = 0;
    private HashMap<String, HashMap<String, ArrayList<UmlOperation>>>
            opt = new HashMap<>();
    private HashMap<String,Integer> optCnt = new HashMap<>();
    private HashMap<String,HashMap<String,UmlAttribute>> attr = new HashMap<>();
    private HashMap<String,ArrayList<String>> noPriAttr = new HashMap<>();
    private HashMap<String,HashSet<String>> optParamCnt = new HashMap<>();
    private HashMap<String,Integer> optReturnCnt = new HashMap<>();
    private HashMap<String,String> id2name = new HashMap<>();
    private HashMap<String,ArrayList<String>> name2id = new HashMap<>();
    private HashMap<String,ArrayList<String>> extendsWho = new HashMap<>();
    private HashMap<String,ArrayList<String>> implementsWho = new HashMap<>();
    private HashMap<String,ArrayList<String>> associateWho = new HashMap<>();
    private HashSet<String> interfaceSet = new HashSet<>();

    MyUmlClassModelInteraction(UmlElement... elements) {
        HashMap<String,String> parent = new HashMap<>();
        HashMap<String,String> id2ref = new HashMap<>();
        HashMap<String,String> end2end = new HashMap<>();
        ArrayList<UmlElement> level1list = new ArrayList<>();
        for (UmlElement e : elements) {
            parent.put(e.getId(),e.getParentId());
            id2name.put(e.getId(),e.getName());
            switch (e.getElementType()) {
                case UML_CLASS:
                    classCount++;
                    opt.put(e.getId(),new HashMap<>());
                    attr.put(e.getId(),new HashMap<>());
                    noPriAttr.put(e.getId(),new ArrayList<>());
                    optParamCnt.put(e.getId(),new HashSet<>());
                    optReturnCnt.put(e.getId(),0);
                    optCnt.put(e.getId(),0);
                    if (!name2id.containsKey(e.getName())) {
                        name2id.put(e.getName(),new ArrayList<>());
                    }
                    name2id.get(e.getName()).add(e.getId());
                    break;
                case UML_INTERFACE:
                    interfaceSet.add(e.getId());
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
                    if (interfaceSet.contains(e.getParentId())) { break; }
                    if (!opt.containsKey(e.getParentId())) {
                        opt.put(e.getParentId(),new HashMap<>());
                    }
                    if (!opt.get(e.getParentId()).containsKey(e.getName())) {
                        opt.get(e.getParentId()).put(e.getName(),
                                new ArrayList<>());
                    }
                    opt.get(e.getParentId()).get(e.getName()).
                            add((UmlOperation)e);
                    if (!optCnt.containsKey(e.getParentId())) {
                        optCnt.put(e.getParentId(),0);
                    }
                    optCnt.put(e.getParentId(),optCnt.get(e.getParentId()) + 1);
                    break;
                case UML_ATTRIBUTE:
                    if (interfaceSet.contains(e.getParentId())) { break; }
                    if (!attr.containsKey(e.getParentId())) {
                        attr.put(e.getParentId(),new HashMap<>());
                    }
                    attr.get(e.getParentId()).put(e.getName(),(UmlAttribute) e);
                    if (((UmlAttribute)e).getVisibility() !=
                            Visibility.PRIVATE) {
                        if (!noPriAttr.containsKey(e.getParentId())) {
                            noPriAttr.put(e.getParentId(),new ArrayList<>());
                        }
                        noPriAttr.get(e.getParentId()).add(e.getName());
                    }
                    break;
                case UML_PARAMETER:
                    String classId = parent.get(e.getParentId());
                    if (interfaceSet.contains(classId)) { break; }
                    if (!optParamCnt.containsKey(classId)) {
                        optParamCnt.put(classId,new HashSet<>());
                    }
                    if (!optReturnCnt.containsKey(classId)) {
                        optReturnCnt.put(classId,0);
                    }
                    switch (((UmlParameter)e).getDirection()) {
                        case RETURN:
                            optReturnCnt.put(classId,
                                    optReturnCnt.get(classId) + 1);
                            break;
                        case IN:
                            optParamCnt.get(classId).add(e.getParentId());
                            break;
                        default: break;
                    }
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
                        if (!associateWho.containsKey(ref)) {
                            associateWho.put(ref, new ArrayList<>());
                        }
                        associateWho.get(ref).add(ref2);
                        if (!associateWho.containsKey(ref2)) {
                            associateWho.put(ref2, new ArrayList<>());
                        }
                        associateWho.get(ref2).add(ref);
                    }
                }
            }
        }
    }

    @Override
    public int getClassCount() { return classCount; }

    @Override
    public int getClassOperationCount(String className, OperationQueryType
            operationQueryType)
            throws ClassNotFoundException, ClassDuplicatedException {
        if (!name2id.containsKey(className)) {
            throw new ClassNotFoundException(className);
        } else {
            if (name2id.get(className).size() > 1) {
                throw new ClassDuplicatedException(className);
            } else {
                String id = name2id.get(className).get(0); //size==1
                switch (operationQueryType) {
                    case RETURN:  return optReturnCnt.get(id);
                    case NON_RETURN:
                        return optCnt.get(id) - optReturnCnt.get(id);
                    case PARAM:  return optParamCnt.get(id).size();
                    case NON_PARAM:
                        return optCnt.get(id) - optParamCnt.get(id).size();
                    case ALL:  return optCnt.get(id);
                    default:  return 0;
                }
            }
        }
    }

    @Override
    public int getClassAttributeCount(String className,
                                      AttributeQueryType attributeQueryType)
            throws ClassNotFoundException, ClassDuplicatedException {
        if (!name2id.containsKey(className)) {
            throw new ClassNotFoundException(className);
        } else {
            if (name2id.get(className).size() > 1) {
                throw new ClassDuplicatedException(className);
            } else {
                String id = name2id.get(className).get(0); //size==1
                int cnt = 0;
                if (attr.containsKey(id)) {
                    cnt += attr.get(id).size();
                }
                if (attributeQueryType == AttributeQueryType.ALL) {
                    while (extendsWho.containsKey(id)) { //类的父类不会多继承
                        id = extendsWho.get(id).get(0); //就直接找第一个
                        if (attr.containsKey(id)) {
                            cnt += attr.get(id).size();
                        }
                    }
                }
                return cnt;
            }
        }
    }

    @Override
    public int getClassAssociationCount(String className)
            throws ClassNotFoundException, ClassDuplicatedException {
        if (!name2id.containsKey(className)) {
            throw new ClassNotFoundException(className);
        } else {
            if (name2id.get(className).size() > 1) {
                throw new ClassDuplicatedException(className);
            } else {
                String id = name2id.get(className).get(0); //size==1
                int cnt = 0;
                if (associateWho.containsKey(id)) {
                    cnt += associateWho.get(id).size();
                }
                while (extendsWho.containsKey(id)) {
                    id = extendsWho.get(id).get(0);
                    if (associateWho.containsKey(id)) {
                        cnt += associateWho.get(id).size();
                    }
                }
                return cnt;
            }
        }
    }

    @Override
    public List<String> getClassAssociatedClassList(String className)
            throws ClassNotFoundException, ClassDuplicatedException {
        if (!name2id.containsKey(className)) {
            throw new ClassNotFoundException(className);
        } else {
            if (name2id.get(className).size() > 1) {
                throw new ClassDuplicatedException(className);
            } else {
                String id = name2id.get(className).get(0); //size==1
                HashSet<String> set = new HashSet<>();
                if (associateWho.containsKey(id)) {
                    for (String s : associateWho.get(id)) {
                        if (!interfaceSet.contains(s)) { set.add(s); }
                    }
                }
                while (extendsWho.containsKey(id)) {
                    id = extendsWho.get(id).get(0);
                    if (associateWho.containsKey(id)) {
                        for (String s : associateWho.get(id)) {
                            if (!interfaceSet.contains(s)) { set.add(s); }
                        }
                    }
                }
                ArrayList<String> l = new ArrayList<>();
                for (String s : set) { l.add(id2name.get(s)); }
                return l;
            }
        }
    }

    @Override
    public Map<Visibility, Integer> getClassOperationVisibility(
            String className, String operationName)
            throws ClassNotFoundException, ClassDuplicatedException {
        if (!name2id.containsKey(className)) {
            throw new ClassNotFoundException(className);
        } else {
            if (name2id.get(className).size() > 1) {
                throw new ClassDuplicatedException(className);
            } else {
                String id = name2id.get(className).get(0); //size==1
                Map<Visibility,Integer> m = new HashMap<>();
                HashMap<String,ArrayList<UmlOperation>> ml = opt.get(id);
                if (ml.containsKey(operationName)) {
                    for (UmlOperation op : ml.get(operationName)) {
                        if (m.containsKey(op.getVisibility())) {
                            m.put(op.getVisibility(),
                                    m.get(op.getVisibility()) + 1);
                        } else { m.put(op.getVisibility(),1); }
                    }
                }
                return m;
            }
        }
    }

    @Override
    public Visibility getClassAttributeVisibility(
            String className, String attributeName)
            throws ClassNotFoundException, ClassDuplicatedException,
            AttributeNotFoundException, AttributeDuplicatedException {
        if (!name2id.containsKey(className)) {
            throw new ClassNotFoundException(className);
        } else {
            if (name2id.get(className).size() > 1) {
                throw new ClassDuplicatedException(className);
            } else {
                Visibility v = null;
                int cnt = 0;
                String id = name2id.get(className).get(0); //size==1
                HashMap<String,UmlAttribute> m;
                if (attr.containsKey(id)) {
                    m = attr.get(id);
                    if (m.containsKey(attributeName)) {
                        cnt++;
                        v = m.get(attributeName).getVisibility();
                    }
                }
                while (extendsWho.containsKey(id)) {
                    id = extendsWho.get(id).get(0);
                    if (attr.containsKey(id)) {
                        m = attr.get(id);
                        if (m.containsKey(attributeName)) {
                            cnt++;
                            v = m.get(attributeName).getVisibility();
                        }
                    }
                }
                if (cnt == 0) {
                    throw new AttributeNotFoundException(
                            className,attributeName);
                } else if (cnt > 1) {
                    throw new AttributeDuplicatedException(
                            className,attributeName);
                } else { return v; }
            }
        }
    }

    @Override
    public String getTopParentClass(String className)
            throws ClassNotFoundException, ClassDuplicatedException {
        if (!name2id.containsKey(className)) {
            throw new ClassNotFoundException(className);
        } else {
            if (name2id.get(className).size() > 1) {
                throw new ClassDuplicatedException(className);
            } else {
                String id = name2id.get(className).get(0); //size==1
                while (extendsWho.containsKey(id)) {
                    id = extendsWho.get(id).get(0);
                }
                return id2name.get(id);
            }
        }
    }

    private void interfaceList(HashSet<String> set,String id) {
        if (implementsWho.containsKey(id)) { //直接实现的接口
            for (String s : implementsWho.get(id)) { //s是接口id
                LinkedList<String> queue = new LinkedList<>();
                queue.addLast(s); //根节点入队
                while (!queue.isEmpty()) {
                    String tmp = queue.removeFirst();
                    set.add(tmp);
                    if (extendsWho.containsKey(tmp)) {
                        for (String t : extendsWho.get(tmp)) {
                            queue.addLast(t);
                        }
                    }
                }
            }
        }
    }

    @Override
    public List<String> getImplementInterfaceList(String className)
            throws ClassNotFoundException, ClassDuplicatedException {
        if (!name2id.containsKey(className)) {
            throw new ClassNotFoundException(className);
        } else {
            if (name2id.get(className).size() > 1) {
                throw new ClassDuplicatedException(className);
            } else {
                String id = name2id.get(className).get(0); //size==1
                HashSet<String> set = new HashSet<>();
                interfaceList(set,id);
                while (extendsWho.containsKey(id)) { //求父类的接口
                    id = extendsWho.get(id).get(0); //父类id
                    interfaceList(set,id);
                }
                ArrayList<String> l = new ArrayList<>();
                for (String s : set) { l.add(id2name.get(s)); }
                return l;
            }
        }
    }

    @Override
    public List<AttributeClassInformation> getInformationNotHidden(
            String className)
            throws ClassNotFoundException, ClassDuplicatedException {
        if (!name2id.containsKey(className)) {
            throw new ClassNotFoundException(className);
        } else {
            if (name2id.get(className).size() > 1) {
                throw new ClassDuplicatedException(className);
            } else {
                String id = name2id.get(className).get(0); //size==1
                List<AttributeClassInformation> l = new ArrayList<>();
                if (noPriAttr.containsKey(id)) {
                    for (String s : noPriAttr.get(id)) {
                        l.add(new AttributeClassInformation(s,id2name.get(id)));
                    }
                }
                while (extendsWho.containsKey(id)) {
                    id = extendsWho.get(id).get(0);
                    if (noPriAttr.containsKey(id)) {
                        for (String s : noPriAttr.get(id)) {
                            l.add(new AttributeClassInformation(s,
                                    id2name.get(id)));
                        }
                    }
                }
                return l;
            }
        }
    }
}
