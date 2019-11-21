package com.oocourse.uml2.interact.exceptions.user;

import com.oocourse.uml2.interact.common.AttributeClassInformation;

import java.util.Set;
import java.util.stream.Collectors;

/**
 * UML002 规则异常
 */
public class UmlRule002Exception extends PreCheckRuleException {
    private final Set<? extends AttributeClassInformation> pairs;

    /**
     * 构造函数
     *
     * @param pairs 异常对
     */
    public UmlRule002Exception(Set<? extends AttributeClassInformation> pairs) {
        super(String.format(
                "Failed when check R001, %s has duplicate name.",
                pairs.stream()
                        .sorted(AttributeClassInformation::compareTo)
                        .map(information -> String.format("\"%s\" in \"%s\"",
                                information.getAttributeName(), information.getClassName()))
                        .collect(Collectors.joining(", "))
        ));
        this.pairs = pairs;
    }

    /**
     * 获取异常对
     *
     * @return 异常对
     */
    public Set<? extends AttributeClassInformation> getPairs() {
        return pairs;
    }
}
