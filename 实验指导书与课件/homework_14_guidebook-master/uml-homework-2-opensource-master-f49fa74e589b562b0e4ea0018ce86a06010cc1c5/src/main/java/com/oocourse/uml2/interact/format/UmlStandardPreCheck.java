package com.oocourse.uml2.interact.format;

import com.oocourse.uml2.interact.exceptions.user.PreCheckRuleException;
import com.oocourse.uml2.interact.exceptions.user.UmlRule002Exception;
import com.oocourse.uml2.interact.exceptions.user.UmlRule008Exception;
import com.oocourse.uml2.interact.exceptions.user.UmlRule009Exception;

/**
 * UML基本标准预检查
 */
public interface UmlStandardPreCheck {
    /**
     * 检查全部规则
     *
     * @throws PreCheckRuleException 预检查异常
     */
    default void checkForAllRules() throws PreCheckRuleException {
        checkForUml002();
        checkForUml008();
        checkForUml009();
    }

    /**
     * 检查UML002 规则
     *
     * @throws UmlRule002Exception 规则异常
     */
    void checkForUml002() throws UmlRule002Exception;

    /**
     * 检查UML008 规则
     *
     * @throws UmlRule008Exception 规则异常
     */
    void checkForUml008() throws UmlRule008Exception;

    /**
     * 检查UML009 规则
     *
     * @throws UmlRule009Exception 规则异常
     */
    void checkForUml009() throws UmlRule009Exception;
}
