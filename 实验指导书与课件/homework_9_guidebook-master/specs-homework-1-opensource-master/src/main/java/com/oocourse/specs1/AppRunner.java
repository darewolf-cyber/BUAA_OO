package com.oocourse.specs1;

import com.oocourse.specs1.exceptions.AppRunnerFailedMessageException;
import com.oocourse.specs1.exceptions.AppRunnerInstantiationException;
import com.oocourse.specs1.exceptions.AppRunnerRunException;
import com.oocourse.specs1.exceptions.InputArgumentException;
import com.oocourse.specs1.models.Path;
import com.oocourse.specs1.models.PathContainer;
import com.oocourse.specs1.models.PathIdNotFoundException;
import com.oocourse.specs1.models.PathNotFoundException;

import java.io.InputStream;
import java.io.PrintStream;
import java.lang.reflect.Constructor;
import java.lang.reflect.InvocationTargetException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Scanner;

/**
 * App运行类
 * 说明：
 * 1、我知道你们想吐槽超过了500行
 * 2、但是，去了注释之后，其实没到500行2333
 * 3、此类封装了全部的基本运行逻辑
 * 4、实例化后，appRunner.run(args)即可自动运行
 */
@SuppressWarnings({"PrimitiveArrayArgumentToVarargsMethod", "unused", "WeakerAccess", "SameParameterValue", "FieldCanBeLocal"})
public class AppRunner {
    private static final PrintStream DEFAULT_ERROR_STREAM = System.err;
    private static final InputStream DEFAULT_INPUT_STREAM = System.in;
    private static final PrintStream DEFAULT_OUTPUT_STREAM = System.out;
    private static final InputArgumentParser NONE_PARAMETER_PARSER
            = InputArgumentParser.newInstance(InstructionType.class);
    private static final InputArgumentParser SINGLE_PARAMETER_PARSER
            = InputArgumentParser.newInstance(InstructionType.class, Integer.class);
    private static final InputArgumentParser DOUBLE_PARAMETER_PARSER
            = InputArgumentParser.newInstance(InstructionType.class, Integer.class, Integer.class);
    private static final InputArgumentParser MULTIPLE_PARAMETER_PARSER
            = InputArgumentParser.newInstance(new Class<?>[]{InstructionType.class}, Integer.class);
    private static final HashMap<InstructionType, InputArgumentParser> PARSER_HASH_MAP
            = new HashMap<InstructionType, InputArgumentParser>() {{
        put(InstructionType.PATH_ADD, MULTIPLE_PARAMETER_PARSER);
        put(InstructionType.PATH_REMOVE, MULTIPLE_PARAMETER_PARSER);
        put(InstructionType.PATH_REMOVE_BY_ID, SINGLE_PARAMETER_PARSER);
        put(InstructionType.PATH_GET_ID, MULTIPLE_PARAMETER_PARSER);
        put(InstructionType.PATH_GET_BY_ID, SINGLE_PARAMETER_PARSER);
        put(InstructionType.PATH_COUNT, NONE_PARAMETER_PARSER);
        put(InstructionType.PATH_SIZE, SINGLE_PARAMETER_PARSER);
        put(InstructionType.PATH_DISTINCT_NODE_COUNT, SINGLE_PARAMETER_PARSER);
        put(InstructionType.PATH_CONTAINS_NODE, DOUBLE_PARAMETER_PARSER);
        put(InstructionType.CONTAINS_PATH, MULTIPLE_PARAMETER_PARSER);
        put(InstructionType.CONTAINS_PATH_ID, SINGLE_PARAMETER_PARSER);
        put(InstructionType.DISTINCT_NODE_COUNT, NONE_PARAMETER_PARSER);
        put(InstructionType.COMPARE_PATHS, DOUBLE_PARAMETER_PARSER);
    }};
    private static final int MAX_PATH_LENGTH = 1000;
    private static final int MIN_PATH_LENGTH = 2;
    private static final InputArgumentParser GENERAL_PARSER
            = InputArgumentParser.newInstance(new Class<?>[]{InstructionType.class}, Anything.class);
    private final Class<? extends Path> pathClass;
    private final Class<? extends PathContainer> pathContainerClass;
    private final Constructor<? extends Path> pathConstructor;
    private final Constructor<? extends PathContainer> pathContainerConstructor;
    private final PathContainer pathContainer;
    private final InputStream inputStream;
    private final PrintStream outputStream;
    private final OfficialOutput officialOutput;
    private final PrintStream errorStream;
    private final HashMap<InstructionType, ArgumentRunner> RUNNER_HASH_MAP
            = new HashMap<InstructionType, ArgumentRunner>() {{
        put(InstructionType.PATH_ADD, AppRunner.this::runAsPathAdd);
        put(InstructionType.PATH_REMOVE, AppRunner.this::runAsPathRemove);
        put(InstructionType.PATH_REMOVE_BY_ID, AppRunner.this::runAsPathRemoveById);
        put(InstructionType.PATH_GET_ID, AppRunner.this::runAsPathGetId);
        put(InstructionType.PATH_GET_BY_ID, AppRunner.this::runAsPathGetById);
        put(InstructionType.PATH_COUNT, AppRunner.this::runAsPathCount);
        put(InstructionType.PATH_SIZE, AppRunner.this::runAsPathSize);
        put(InstructionType.PATH_DISTINCT_NODE_COUNT, AppRunner.this::runAsPathDistinctNodeCount);
        put(InstructionType.PATH_CONTAINS_NODE, AppRunner.this::runAsPathContainsNode);
        put(InstructionType.CONTAINS_PATH, AppRunner.this::runAsContainsPath);
        put(InstructionType.CONTAINS_PATH_ID, AppRunner.this::runAsContainsPathId);
        put(InstructionType.DISTINCT_NODE_COUNT, AppRunner.this::runAsDistinctNodeCount);
        put(InstructionType.COMPARE_PATHS, AppRunner.this::runAsComparePaths);
    }};

    /**
     * 构造函数
     *
     * @param pathClass          路径类型
     * @param pathContainerClass 路径容器类型
     * @param inputStream        输入流
     * @param outputStream       输出流
     * @param errorStream        异常流
     * @throws NoSuchMethodException     无方法异常
     * @throws InstantiationException    实例化异常
     * @throws IllegalAccessException    非法读写异常
     * @throws InvocationTargetException 方法调用内部异常
     */
    private AppRunner(
            Class<? extends Path> pathClass,
            Class<? extends PathContainer> pathContainerClass,
            InputStream inputStream, PrintStream outputStream, PrintStream errorStream)
            throws NoSuchMethodException, InstantiationException,
            IllegalAccessException, InvocationTargetException {
        this.pathClass = pathClass;
        this.pathContainerClass = pathContainerClass;
        this.inputStream = inputStream;
        this.outputStream = outputStream;
        this.errorStream = errorStream;
        this.officialOutput = new OfficialOutput(outputStream);

        // init & test path container constructor
        this.pathContainerConstructor = this.pathContainerClass.getConstructor();
        this.pathContainer = this.pathContainerConstructor.newInstance();

        // init & test path constructor
        this.pathConstructor = this.pathClass.getConstructor(int[].class);
        Path testPath = this.pathConstructor.newInstance(new int[]{1, 2, 3, 4});
    }

    /**
     * 实例化函数（输入输出异常均使用系统流）
     *
     * @param pathClass          路径类型
     * @param pathContainerClass 路径容器类型
     * @throws AppRunnerInstantiationException 运行类实例化异常
     */
    public static AppRunner newInstance(
            Class<? extends Path> pathClass,
            Class<? extends PathContainer> pathContainerClass)
            throws AppRunnerInstantiationException {
        return newInstance(pathClass, pathContainerClass,
                DEFAULT_INPUT_STREAM, DEFAULT_OUTPUT_STREAM, DEFAULT_ERROR_STREAM);
    }

    /**
     * 构造函数
     *
     * @param pathClass          路径类型
     * @param pathContainerClass 路径容器类型
     * @param inputStream        输入流
     * @param outputStream       输出流
     * @param errorStream        异常流
     * @throws AppRunnerInstantiationException 运行类实例化异常
     */
    private static AppRunner newInstance(
            Class<? extends Path> pathClass,
            Class<? extends PathContainer> pathContainerClass,
            InputStream inputStream, PrintStream outputStream, PrintStream errorStream)
            throws AppRunnerInstantiationException {
        try {
            return new AppRunner(pathClass, pathContainerClass,
                    inputStream, outputStream, errorStream);
        } catch (NoSuchMethodException | InvocationTargetException |
                InstantiationException | IllegalAccessException e) {
            throw new AppRunnerInstantiationException(e);
        }
    }

    /**
     * 参数对象列表转节点整型列表
     *
     * @param arguments 参数对象列表
     * @return 节点整型列表
     */
    private static int[] argumentsToNodeList(List<Object> arguments) {
        int[] nodeList = new int[arguments.size() - 1];
        int size = arguments.size();
        for (int i = 1; i < size; i++) {
            nodeList[i - 1] = (Integer) arguments.get(i);
        }
        return nodeList;
    }

    /**
     * 检查节点列表
     *
     * @param nodeList 节点列表
     * @throws AppRunnerFailedMessageException 异常消息信息
     */
    private static void checkValidNodeList(int[] nodeList) throws AppRunnerFailedMessageException {
        if (!(nodeList.length >= MIN_PATH_LENGTH && nodeList.length <= MAX_PATH_LENGTH)) {
            throw new AppRunnerFailedMessageException("Failed, invalid path.");
        }
    }

    /**
     * 获取路径类型
     *
     * @return 路径类型
     */
    public Class<? extends Path> getPathClass() {
        return pathClass;
    }

    /**
     * 获取路径容器类型
     *
     * @return 路径容器类型
     */
    public Class<? extends PathContainer> getPathContainerClass() {
        return pathContainerClass;
    }

    /**
     * 获取路径类构造函数
     *
     * @return 路径类构造函数
     */
    private Constructor<? extends Path> getPathConstructor() {
        return pathConstructor;
    }

    /**
     * 获取路径容器类构造函数
     *
     * @return 路径容器类构造函数
     */
    private Constructor<? extends PathContainer> getPathContainerConstructor() {
        return pathContainerConstructor;
    }

    /**
     * 获取路径容器
     *
     * @return 路径容器
     */
    private PathContainer getPathContainer() {
        return pathContainer;
    }

    /**
     * 生成新的路径对象
     *
     * @param nodeList 节点列表
     * @return 路径对象
     * @throws IllegalAccessException    非法访问异常
     * @throws InstantiationException    实例化异常
     * @throws InvocationTargetException 调用内部异常
     */
    private Path newPathInstance(int[] nodeList)
            throws IllegalAccessException,
            InstantiationException, InvocationTargetException {
        return this.getPathConstructor().newInstance(nodeList);
    }

    /**
     * 运行应用
     *
     * @param args 命令行参数列表
     */
    public void run(String[] args) {
        Scanner scanner = new Scanner(inputStream);
        while (scanner.hasNextLine()) {
            String line = scanner.nextLine();
            String[] arguments = line.trim().split("\\s+");
            List<Object> parsedArguments;
            try {
                parsedArguments = GENERAL_PARSER.parse(arguments);
            } catch (InputArgumentException exception) {
                printlnAsError("Error, invalid instruction type.");
                continue;
            }
            InstructionType type = (InstructionType) parsedArguments.get(0);
            try {
                runAsArguments(type, arguments);
            } catch (AppRunnerRunException e) {
                errorStream.println("Something wrong with your process.");
                Exception exception = e.getException();
                if (exception != null) {
                    exception.printStackTrace(errorStream);
                }
            }
        }
        scanner.close();
    }

    /**
     * 输出异常信息（附加数据为null）
     *
     * @param message 信息文本
     */
    private void printlnAsError(String message) {
        printlnAsError(message, null);
    }

    /**
     * 输出异常信息
     *
     * @param message 信息文本
     * @param data    附加数据
     */
    private void printlnAsError(String message, HashMap<String, Object> data) {
        officialOutput.println(message, true, false, data);
    }

    /**
     * 输出失败信息（附加数据为null）
     *
     * @param message 信息文本
     */
    private void printlnAsFailed(String message) {
        printlnAsFailed(message, null);
    }

    /**
     * 输出失败信息
     *
     * @param message 信息文本
     * @param data    附加数据
     */
    private void printlnAsFailed(String message, HashMap<String, Object> data) {
        officialOutput.println(message, false, false, data);
    }

    /**
     * 输出成功信息（附加数据为null）
     *
     * @param message 信息文本
     */
    private void printlnAsSuccess(String message) {
        printlnAsSuccess(message, null);
    }

    /**
     * 输出成功信息
     *
     * @param message 信息文本
     * @param data    信息附加数据
     */
    private void printlnAsSuccess(String message, HashMap<String, Object> data) {
        officialOutput.println(message, false, true, data);
    }

    /**
     * 按照参数列表形式执行程序
     *
     * @param type      指令类型
     * @param arguments 参数列表
     * @throws AppRunnerRunException 应用运行异常
     */
    private void runAsArguments(
            InstructionType type, String[] arguments)
            throws AppRunnerRunException {
        InputArgumentParser parser = PARSER_HASH_MAP.get(type);
        List<Object> parsedArguments;
        try {
            parsedArguments = parser.parse(arguments);
        } catch (InputArgumentException e) {
            printlnAsError("Error, invalid argument format.");
            return;
        }
        ArgumentRunner runner = RUNNER_HASH_MAP.get(type);
        try {
            RunnerResult result = runner.run(type, parsedArguments);
            printlnAsSuccess(result.getMessage(), result.getData());
        } catch (AppRunnerFailedMessageException e) {
            printlnAsFailed(e.getMessage());
        } catch (Exception e) {
            throw new AppRunnerRunException(e);
        }
    }

    /**
     * PATH_ADD指令
     *
     * @param type      指令类型
     * @param arguments 解析后的参数列表
     * @return 运行结果
     * @throws Exception 运行异常
     */
    private RunnerResult runAsPathAdd(InstructionType type, List<Object> arguments) throws Exception {
        int[] nodeList = argumentsToNodeList(arguments);
        checkValidNodeList(nodeList);
        Path path = newPathInstance(nodeList);

        int result = pathContainer.addPath(path);
        return new RunnerResult(
                String.format("Ok, path id is %s.", result),
                new HashMap<String, Object>() {{
                    put("path_id", result);
                }}
        );
    }

    /**
     * PATH_REMOVE指令
     *
     * @param type      指令类型
     * @param arguments 解析后的参数列表
     * @return 运行结果
     * @throws Exception 运行异常
     */
    private RunnerResult runAsPathRemove(InstructionType type, List<Object> arguments) throws Exception {
        int[] nodeList = argumentsToNodeList(arguments);
        checkValidNodeList(nodeList);
        Path path = newPathInstance(nodeList);

        try {
            int result = pathContainer.removePath(path);
            return new RunnerResult(
                    String.format("Ok, path id is %s.", result),
                    new HashMap<String, Object>() {{
                        put("path_id", result);
                    }}
            );
        } catch (PathNotFoundException e) {
            throw new AppRunnerFailedMessageException("Failed, path not exist.");
        }
    }

    /**
     * PATH_REMOVE_BY_ID指令
     *
     * @param type      指令类型
     * @param arguments 解析后的参数列表
     * @return 运行结果
     * @throws Exception 运行异常
     */
    private RunnerResult runAsPathRemoveById(InstructionType type, List<Object> arguments) throws Exception {
        int pathId = (Integer) arguments.get(1);

        try {
            pathContainer.removePathById(pathId);
            return new RunnerResult("Ok, path removed.");
        } catch (PathIdNotFoundException e) {
            throw new AppRunnerFailedMessageException("Failed, path id not exist.");
        }
    }

    /**
     * PATH_GET_ID指令
     *
     * @param type      指令类型
     * @param arguments 解析后的参数列表
     * @return 运行结果
     * @throws Exception 运行异常
     */
    private RunnerResult runAsPathGetId(InstructionType type, List<Object> arguments) throws Exception {
        int[] nodeList = argumentsToNodeList(arguments);
        checkValidNodeList(nodeList);
        Path path = newPathInstance(nodeList);

        try {
            int result = pathContainer.getPathId(path);
            return new RunnerResult(
                    String.format("Ok, path id is %s.", result),
                    new HashMap<String, Object>() {{
                        put("path_id", result);
                    }}
            );
        } catch (PathNotFoundException e) {
            throw new AppRunnerFailedMessageException("Failed, path not exist.");
        }
    }

    /**
     * PATH_GET_BY_ID指令
     *
     * @param type      指令类型
     * @param arguments 解析后的参数列表
     * @return 运行结果
     * @throws Exception 运行异常
     */
    private RunnerResult runAsPathGetById(InstructionType type, List<Object> arguments) throws Exception {
        int pathId = (Integer) arguments.get(1);

        try {
            Path path = pathContainer.getPathById(pathId);

            StringBuilder arrayContent = new StringBuilder();
            arrayContent.append("(");
            List<Integer> nodeList = new ArrayList<>();
            boolean first = true;
            for (Integer nodeId : path) {
                if (!first) {
                    arrayContent.append(", ");
                }
                arrayContent.append(nodeId);
                first = false;
                nodeList.add(nodeId);
            }
            arrayContent.append(")");
            return new RunnerResult(
                    String.format("Ok, path is %s.", arrayContent.toString()),
                    new HashMap<String, Object>() {{
                        put("nodes", nodeList);
                    }}
            );
        } catch (PathIdNotFoundException e) {
            throw new AppRunnerFailedMessageException("Failed, path id not exist.");
        }
    }

    /**
     * PATH_COUNT指令
     *
     * @param type      指令类型
     * @param arguments 解析后的参数列表
     * @return 运行结果
     */
    private RunnerResult runAsPathCount(InstructionType type, List<Object> arguments) {
        int count = pathContainer.size();
        return new RunnerResult(
                String.format("Total count is %s.", count),
                new HashMap<String, Object>() {{
                    put("count", count);
                }}
        );
    }

    /**
     * PATH_SIZE指令
     *
     * @param type      指令类型
     * @param arguments 解析后的参数列表
     * @return 运行结果
     * @throws Exception 运行异常
     */
    private RunnerResult runAsPathSize(InstructionType type, List<Object> arguments) throws Exception {
        int pathId = (Integer) arguments.get(1);

        try {
            Path path = pathContainer.getPathById(pathId);

            int size = path.size();
            return new RunnerResult(
                    String.format("Ok, path size is %s.", size),
                    new HashMap<String, Object>() {{
                        put("size", size);
                    }}
            );
        } catch (PathIdNotFoundException e) {
            throw new AppRunnerFailedMessageException("Failed, path id not exist.");
        }
    }

    /**
     * PATH_DISTINCT_NODE_COUNT指令
     *
     * @param type      指令类型
     * @param arguments 解析后的参数列表
     * @return 运行结果
     * @throws Exception 运行异常
     */
    private RunnerResult runAsPathDistinctNodeCount(InstructionType type, List<Object> arguments) throws Exception {
        int pathId = (Integer) arguments.get(1);

        try {
            Path path = pathContainer.getPathById(pathId);

            int count = path.getDistinctNodeCount();
            return new RunnerResult(
                    String.format("Ok, distinct node count of path is %s.", count),
                    new HashMap<String, Object>() {{
                        put("count", count);
                    }}
            );
        } catch (PathIdNotFoundException e) {
            throw new AppRunnerFailedMessageException("Failed, path id not exist.");
        }
    }

    /**
     * PATH_CONTAINS_NODE指令
     *
     * @param type      指令类型
     * @param arguments 解析后的参数列表
     * @return 运行结果
     * @throws Exception 运行异常
     */
    private RunnerResult runAsPathContainsNode(InstructionType type, List<Object> arguments) throws Exception {
        int pathId = (Integer) arguments.get(1);
        int nodeId = (Integer) arguments.get(2);
        try {
            Path path = pathContainer.getPathById(pathId);
            boolean contains = path.containsNode(nodeId);
            String message;
            if (contains) {
                message = "Yes.";
            } else {
                message = "No.";
            }
            return new RunnerResult(
                    message,
                    new HashMap<String, Object>() {{
                        put("contains", contains);
                    }}
            );
        } catch (PathIdNotFoundException e) {
            throw new AppRunnerFailedMessageException("Failed, path id not exist.");
        }
    }

    /**
     * CONTAINS_PATH指令
     *
     * @param type      指令类型
     * @param arguments 解析后的参数列表
     * @return 运行结果
     * @throws Exception 运行异常
     */
    private RunnerResult runAsContainsPath(InstructionType type, List<Object> arguments) throws Exception {
        int[] nodeList = argumentsToNodeList(arguments);
        checkValidNodeList(nodeList);
        Path path = newPathInstance(nodeList);

        boolean contains = pathContainer.containsPath(path);
        String message;
        if (contains) {
            message = "Yes.";
        } else {
            message = "No.";
        }
        return new RunnerResult(
                message,
                new HashMap<String, Object>() {{
                    put("contains", contains);
                }}
        );
    }

    /**
     * CONTAINS_PATH_ID指令
     *
     * @param type      指令类型
     * @param arguments 解析后的参数列表
     * @return 运行结果
     */
    private RunnerResult runAsContainsPathId(InstructionType type, List<Object> arguments) {
        int pathId = (Integer) arguments.get(1);

        boolean contains = pathContainer.containsPathId(pathId);
        String message;
        if (contains) {
            message = "Yes.";
        } else {
            message = "No.";
        }
        return new RunnerResult(
                message,
                new HashMap<String, Object>() {{
                    put("contains", contains);
                }}
        );
    }

    /**
     * DISTINCT_NODE_COUNT指令
     *
     * @param type      指令类型
     * @param arguments 解析后的参数列表
     * @return 运行结果
     */
    private RunnerResult runAsDistinctNodeCount(InstructionType type, List<Object> arguments) {
        int count = pathContainer.getDistinctNodeCount();
        return new RunnerResult(
                String.format("Ok, distinct node count is %s.", count),
                new HashMap<String, Object>() {{
                    put("count", count);
                }}
        );
    }

    /**
     * COMPARE_PATHS指令
     *
     * @param type      指令类型
     * @param arguments 解析后的参数列表
     * @return 运行结果
     * @throws Exception 运行异常
     */
    private RunnerResult runAsComparePaths(InstructionType type, List<Object> arguments) throws Exception {
        int xPathId = (Integer) arguments.get(1);
        int yPathId = (Integer) arguments.get(2);

        try {
            Path xPath = pathContainer.getPathById(xPathId);
            Path yPath = pathContainer.getPathById(yPathId);

            int compare = xPath.compareTo(yPath);
            String statusTest;
            if (compare < 0) {
                statusTest = "less than";
            } else if (compare > 0) {
                statusTest = "greater than";
            } else {
                statusTest = "equal to";
            }
            return new RunnerResult(
                    String.format("Ok, path %s is %s to %s.", xPathId, statusTest, yPathId),
                    new HashMap<String, Object>() {{
                        put("x_path_id", xPathId);
                        put("y_path_id", yPathId);
                        put("compare", compare);
                    }}
            );
        } catch (PathIdNotFoundException e) {
            throw new AppRunnerFailedMessageException("Failed, path id not exist.");
        }
    }

    /**
     * 命令列表执行接口
     */
    private interface ArgumentRunner {
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

    /**
     * 运行结果对象
     */
    private static class RunnerResult {
        private final String message;
        private final HashMap<String, Object> data;

        /**
         * 构造函数
         *
         * @param message 消息
         * @param data    附加数据
         */
        RunnerResult(String message, HashMap<String, Object> data) {
            this.message = message;
            this.data = data;
        }

        /**
         * 构造函数（附加数据位null）
         *
         * @param message 消息
         */
        RunnerResult(String message) {
            this(message, null);
        }

        /**
         * 获取消息
         *
         * @return 消息
         */
        public String getMessage() {
            return message;
        }

        /**
         * 获取附加数据
         *
         * @return 附加数据
         */
        public HashMap<String, Object> getData() {
            return data;
        }
    }
}
