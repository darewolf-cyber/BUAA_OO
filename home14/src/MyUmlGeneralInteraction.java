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
import com.oocourse.uml2.models.elements.UmlElement;

import java.util.List;
import java.util.Map;

public class MyUmlGeneralInteraction implements UmlGeneralInteraction {
    private MyUmlClassModelInteraction umlClassModel;
    private MyUmlStateChartInteraction umlStateChart;
    private MyUmlCollaborationInteraction umlCollaboration;
    private MyUmlStandardPreCheck umlStandardPreCheck;

    public MyUmlGeneralInteraction(UmlElement... elements) {
        umlClassModel = new MyUmlClassModelInteraction(elements);
        umlStateChart = new MyUmlStateChartInteraction(elements);
        umlCollaboration = new MyUmlCollaborationInteraction(elements);
        umlStandardPreCheck = new MyUmlStandardPreCheck(elements);
    }

    @Override
    public int getClassCount() {
        return umlClassModel.getClassCount();
    }

    @Override
    public int getClassOperationCount(String s, OperationQueryType opt)
            throws ClassNotFoundException, ClassDuplicatedException {
        return umlClassModel.getClassOperationCount(s,opt);
    }

    @Override
    public int getClassAttributeCount(String s, AttributeQueryType attrType)
            throws ClassNotFoundException, ClassDuplicatedException {
        return umlClassModel.getClassAttributeCount(s,attrType);
    }

    @Override
    public int getClassAssociationCount(String s)
            throws ClassNotFoundException, ClassDuplicatedException {
        return umlClassModel.getClassAssociationCount(s);
    }

    @Override
    public List<String> getClassAssociatedClassList(String s)
            throws ClassNotFoundException, ClassDuplicatedException {
        return umlClassModel.getClassAssociatedClassList(s);
    }

    @Override
    public Map<Visibility, Integer> getClassOperationVisibility(
            String className, String opName)
            throws ClassNotFoundException, ClassDuplicatedException {
        return umlClassModel.getClassOperationVisibility(className,opName);
    }

    @Override
    public Visibility getClassAttributeVisibility(
            String className, String opName)
            throws ClassNotFoundException, ClassDuplicatedException,
            AttributeNotFoundException, AttributeDuplicatedException {
        return umlClassModel.getClassAttributeVisibility(className,opName);
    }

    @Override
    public String getTopParentClass(String s)
            throws ClassNotFoundException, ClassDuplicatedException {
        return umlClassModel.getTopParentClass(s);
    }

    @Override
    public List<String> getImplementInterfaceList(String s)
            throws ClassNotFoundException, ClassDuplicatedException {
        return umlClassModel.getImplementInterfaceList(s);
    }

    @Override
    public List<AttributeClassInformation> getInformationNotHidden(
            String s) throws ClassNotFoundException, ClassDuplicatedException {
        return umlClassModel.getInformationNotHidden(s);
    }

    @Override
    public int getParticipantCount(String s)
            throws InteractionNotFoundException,InteractionDuplicatedException {
        return umlCollaboration.getParticipantCount(s);
    }

    @Override
    public int getMessageCount(String s)
            throws InteractionNotFoundException,InteractionDuplicatedException {
        return umlCollaboration.getMessageCount(s);
    }

    @Override
    public int getIncomingMessageCount(String s, String s1)
            throws InteractionNotFoundException,InteractionDuplicatedException,
            LifelineNotFoundException, LifelineDuplicatedException {
        return umlCollaboration.getIncomingMessageCount(s,s1);
    }

    @Override
    public void checkForUml002() throws UmlRule002Exception {
        umlStandardPreCheck.checkForUml002();
    }

    @Override
    public void checkForUml008() throws UmlRule008Exception {
        umlStandardPreCheck.checkForUml008();
    }

    @Override
    public void checkForUml009() throws UmlRule009Exception {
        umlStandardPreCheck.checkForUml009();
    }

    @Override
    public int getStateCount(String s) throws
            StateMachineNotFoundException, StateMachineDuplicatedException {
        return umlStateChart.getStateCount(s);
    }

    @Override
    public int getTransitionCount(String s)
            throws StateMachineNotFoundException,
            StateMachineDuplicatedException {
        return umlStateChart.getTransitionCount(s);
    }

    @Override
    public int getSubsequentStateCount(String s,String s1)
            throws StateMachineNotFoundException,
            StateMachineDuplicatedException,
            StateNotFoundException, StateDuplicatedException {
        return umlStateChart.getSubsequentStateCount(s,s1);
    }
}