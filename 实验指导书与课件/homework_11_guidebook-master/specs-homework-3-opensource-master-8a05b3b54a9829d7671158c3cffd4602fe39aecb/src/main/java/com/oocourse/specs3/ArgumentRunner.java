package com.oocourse.specs3;

import java.util.List;

/**
 * 命令列表执行接口
 */
interface ArgumentRunner {
    /**
     * 执行方法
     *
     * @param type      指令类型
     * @param arguments 解析后的参数列表
     * @return 运行结果
     * @throws Exception 运行异常
     */
    RunnerResult run(InstructionType type, List<Object> arguments) throws Exception;
}