# OO第三次博客作业 #

三次作业内容：JML相关，逐步进阶。`PathContainer`->`Graph`->`RailwaySystem`

## (1)梳理`JML`语言的理论基础、应用工具链情况 ##

### 理论基础 ###

JML是一种为 Java量身定做的**形式化的行为接口规范语言 ( BISL)**, 用来规范 Java程序模块 (如类和接口 )的行为及详细设计决策。它沿袭了 BISL良好定义的形式语义, 同时也继承了DBC语言较强的执行能力。使用 JML书写的形式化的接口规范可以推动程序的自动化测试, 减少单元测试的负担。

一般而言，JML有两种主要的用法：
（1）**开展规格化设计**。这样交给代码实现人员的将不是可能带有内在模糊性的自然语言描述，而是逻辑严格的规
格。
（2）**针对已有的代码实现，书写其对应的规格，从而提高代码的可维护性**。这在遗留代码的维护方面具有特别重要的意义。

### 应用工具链 ###

目前, 许多基于 JML的验证、调试和测试工具已经非常成熟, 例如运行时刻的断言检查器 (Runti me Assertion Checker)、JmlUnit、JMLAutoTest等等。利用这些支撑工具, JML 规范可以被翻译为可识别的程序代码, 并被动态断言检查器检验, 也可以进行测试框架、测试用例等的自动生成。

**Openjml**可以对生成的类文件进行JML规范检查。Openjml使用**SMT Solver**来对检查程序实现是否满足所设计的规格(specification)。目前Openjml封装了四个主流的solver，z3由Microsoft开发的，并已在[github](https://github.com/Z3Prover/z3)上开源，其正式[发布版](https://www.microsoft.com/en-us/download/details.aspx?id=52270)。cvc4由Standford开发，可以通过[下载](http://cvc4.cs.stanford.edu/downloads/)。 

**JMLUnitNG/JMLUnit**可以实现自动生成测试用例，可以实现对代码的自动化测试。

**JMLdoc**工具可在生成的HTML格式文档中包含JML规范。

## (2)部署`SMT Solver`，至少选择3个主要方法来尝试进行验证，报告结果 ##

尝试着测试了`MyPath.java` 源代码如下

```java
import com.oocourse.specs1.models.Path;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Set;

public class MyPath implements Path {
    //@ public instance model non_null int[] nodes;
    private ArrayList<Integer> path;
    private int disNum;

    public MyPath(int... nodeList) {
        path = new ArrayList<>();
        for (int i = 0;i < nodeList.length;i++) {
            path.add(nodeList[i]);
        }
        disNum = -1;
    }

	//@ also    
    //@ ensures \result == nodes.length;
    public /*@pure@*/int size() {
        return path.size();
    }

    /*@ also
	  @ requires index >= 0 && index < size();
      @ assignable \nothing;
      @ ensures \result == nodes[index];
      @*/
    public /*@pure@*/ int getNode(int index) {
        return path.get(index);
    }

	//@ also
    //@ ensures \result == (\exists int i; 0 <= i && i < nodes.length; nodes[i] == node);
    public /*@pure@*/ boolean containsNode(int node) {
        return path.contains(node);
    }

	/*@ also
      @ ensures \result == (\num_of int i, j; 0 <= i && i < j
                && j < nodes.length;nodes[i] != nodes[j]);
      @*/
    public /*pure*/ int getDistinctNodeCount() {
        if (disNum == -1) {
            Set<Integer> set = new HashSet<>();
            set.addAll(path);
            disNum = set.size();
        }
        return disNum;
    }

	//@ also
    //@ ensures \result == (nodes.length >= 2);
    public /*@pure@*/ boolean isValid() {
        return path.size() >= 2;
    }

    /*@ also
      @ public normal_behavior
      @ requires obj != null && obj instanceof Path;
      @ assignable \nothing;
      @ ensures \result == (((MyPath) obj).size() == nodes.length) && (\forall int i; 0 <= i && i < nodes.length; nodes[i] == ((MyPath) obj).getNode(i));
      @ also
      @ public normal_behavior
      @ requires obj == null || !(obj instanceof Path);
      @ assignable \nothing;
      @ ensures \result == false;
      @*/
    public boolean equals(Object obj) {
        if (obj == null || !(obj instanceof Path)) {
            return false;
        }
        else {
            if (path.size() != ((Path) obj).size()) {
                return false;
            }
            boolean flag = true;
            for (int i = 0;i < path.size(); i++) {
                if (path.get(i) != ((Path) obj).getNode(i)) {
                    flag = false;
                    break;
                }
            }
            return flag;
        }
    }

    public int compareTo(Path o) {
        for (int i = 0;i < Math.min(path.size(),o.size()); i++) {
            if (path.get(i) < o.getNode(i)) {
                return -1;
            }
            else if (path.get(i) > o.getNode(i)) {
                return 1;
            }
        }
        return path.size() - o.size();
    }

    public Iterator<Integer> iterator() {
        return path.iterator();
    }

    public int hashCode() {
        return path.hashCode();
    }
}
```

通过命令` java -jar openjml.jar -cp specs-homework-1-1.1-raw-jar-with-dependencies.jar -check MyPath.java`可以检验JML是否有语法错误。

经过调整，JML语法已经正确。

通过命令`java -jar openjml.jar -cp specs-homework-1-1.1-raw-jar-with-dependencies.jar -exec Solvers-windows/z3-4.7.1.exe -esc MyPath.java`进行程序代码静态检查：给出程序中可能出现的问题。

输出如下：

```java
MyPath.java:16: 警告: The prover cannot establish an assertion (PossiblyNegativeIndex) in method MyPath
            path.add(nodeList[i]);
                             ^
MyPath.java:9: 警告: The prover cannot establish an assertion (NullField) in method MyPath
    //@ public instance model non_null int[] nodes;
                                             ^
MyPath.java:100: 警告: The prover cannot establish an assertion (InvariantLeaveCaller: openjml.jar(specs/java/util/Collection.jml):71: 注: ) in method compareTo:  (Caller: MyPath.compareTo(com.oocourse.specs1.models.Path), Callee: java.util.ArrayList.size())
        return path.size() - o.size();
                        ^
openjml.jar(specs/java/util/Collection.jml):71: 警告: Associated declaration: MyPath.java:100: 注:
    //-RAC@ public invariant content.theSize >= 0;
                   ^
MyPath.java:93: 警告: The prover cannot establish an assertion (InvariantLeaveCaller: openjml.jar(specs/java/util/Collection.jml):71: 注: ) in method compareTo:  (Caller: MyPath.compareTo(com.oocourse.specs1.models.Path), Callee: java.util.ArrayList.get(int))
            if (path.get(i) < o.getNode(i)) {
                        ^
openjml.jar(specs/java/util/Collection.jml):71: 警告: Associated declaration: MyPath.java:93: 注:
    //-RAC@ public invariant content.theSize >= 0;
                   ^
MyPath.java:100: 警告: The prover cannot establish an assertion (ArithmeticOperationRange) in method compareTo:  overflow in int difference
        return path.size() - o.size();
                           ^
MyPath.java:96: 警告: The prover cannot establish an assertion (InvariantLeaveCaller: openjml.jar(specs/java/util/Collection.jml):71: 注: ) in method compareTo:  (Caller: MyPath.compareTo(com.oocourse.specs1.models.Path), Callee: java.util.ArrayList.get(int))
            else if (path.get(i) > o.getNode(i)) {
                             ^
openjml.jar(specs/java/util/Collection.jml):71: 警告: Associated declaration: MyPath.java:96: 注:
    //-RAC@ public invariant content.theSize >= 0;
                   ^
MyPath.java:96: 警告: The prover cannot establish an assertion (InvariantLeaveCaller: openjml.jar(specs/java/util/Collection.jml):70: 注: ) in method compareTo:  (Caller: MyPath.compareTo(com.oocourse.specs1.models.Path), Callee: java.util.ArrayList.get(int))
            else if (path.get(i) > o.getNode(i)) {
                             ^
openjml.jar(specs/java/util/Collection.jml):70: 警告: Associated declaration: MyPath.java:96: 注:
    //-RAC@ public invariant content.owner == this;
                   ^
MyPath.java:100: 警告: The prover cannot establish an assertion (InvariantLeaveCaller: openjml.jar(specs/java/util/Collection.jml):70: 注: ) in method compareTo:  (Caller: MyPath.compareTo(com.oocourse.specs1.models.Path), Callee: java.util.ArrayList.size())
        return path.size() - o.size();
                        ^
openjml.jar(specs/java/util/Collection.jml):70: 警告: Associated declaration: MyPath.java:100: 注:
    //-RAC@ public invariant content.owner == this;
                   ^
MyPath.java:93: 警告: The prover cannot establish an assertion (InvariantLeaveCaller: openjml.jar(specs/java/util/Collection.jml):70: 注: ) in method compareTo:  (Caller: MyPath.compareTo(com.oocourse.specs1.models.Path), Callee: java.util.ArrayList.get(int))
            if (path.get(i) < o.getNode(i)) {
                        ^
openjml.jar(specs/java/util/Collection.jml):70: 警告: Associated declaration: MyPath.java:93: 注:
    //-RAC@ public invariant content.owner == this;
                   ^
openjml.jar(specs/java/util/Collection.jml):70: 警告: The prover cannot establish an assertion (Invariant) in method compareTo
    //-RAC@ public invariant content.owner == this;
                   ^
openjml.jar(specs/java/util/Collection.jml):71: 警告: The prover cannot establish an assertion (Invariant) in method compareTo
    //-RAC@ public invariant content.theSize >= 0;
                   ^
MyPath.java:39: 警告: The prover cannot establish an assertion (Postcondition: MyPath.java:37: 注: ) in method containsNode
        return path.contains(node);
        ^
MyPath.java:37: 警告: Associated declaration: MyPath.java:39: 注:
    //@ ensures \result == (\exists int i; 0 <= i && i < nodes.length; nodes[i] == node);
        ^
MyPath.java:77: 警告: The prover cannot establish an assertion (Assignable: MyPath.java:62: 注: ) in method equals:  \everything
            if (path.size() != ((Path) obj).size()) {
                                                ^
MyPath.java:62: 警告: Associated declaration: MyPath.java:77: 注:
      @ public normal_behavior
               ^
MyPath.java:81: 警告: The prover cannot establish an assertion (InvariantLeaveCaller: openjml.jar(specs/java/util/Collection.jml):71: 注: ) in method equals:  (Caller: MyPath.equals(java.lang.Object), Callee: java.util.ArrayList.size())
            for (int i = 0;i < path.size(); i++) {
                                        ^
openjml.jar(specs/java/util/Collection.jml):71: 警告: Associated declaration: MyPath.java:81: 注:
    //-RAC@ public invariant content.theSize >= 0;
                   ^
MyPath.java:81: 警告: The prover cannot establish an assertion (InvariantLeaveCaller: openjml.jar(specs/java/util/Collection.jml):70: 注: ) in method equals:  (Caller: MyPath.equals(java.lang.Object), Callee: java.util.ArrayList.size())
            for (int i = 0;i < path.size(); i++) {
                                        ^
openjml.jar(specs/java/util/Collection.jml):70: 警告: Associated declaration: MyPath.java:81: 注:
    //-RAC@ public invariant content.owner == this;
                   ^
MyPath.java:77: 警告: The prover cannot establish an assertion (ExceptionalPostcondition: MyPath.java:62: 注: ) in method equals
            if (path.size() != ((Path) obj).size()) {
                                                ^
MyPath.java:62: 警告: Associated declaration: MyPath.java:77: 注:
      @ public normal_behavior
               ^
MyPath.java:77: 警告: The prover cannot establish an assertion (ExceptionalPostcondition: openjml.jar(specs/java/lang/Object.jml):76: 注: ) in method equals
            if (path.size() != ((Path) obj).size()) {
                                                ^
openjml.jar(specs/java/lang/Object.jml):76: 警告: Associated declaration: MyPath.java:77: 注:
      @   public normal_behavior
                 ^
MyPath.java:82: 警告: The prover cannot establish an assertion (Assignable: MyPath.java:62: 注: ) in method equals:  \everything
                if (path.get(i) != ((Path) obj).getNode(i)) {
                                                       ^
MyPath.java:62: 警告: Associated declaration: MyPath.java:82: 注:
      @ public normal_behavior
               ^
openjml.jar(specs/java/util/Collection.jml):70: 警告: The prover cannot establish an assertion (Invariant) in method equals
    //-RAC@ public invariant content.owner == this;
                   ^
openjml.jar(specs/java/util/Collection.jml):71: 警告: The prover cannot establish an assertion (Invariant) in method equals
    //-RAC@ public invariant content.theSize >= 0;
                   ^
MyPath.java:65: 警告: The prover cannot establish an assertion (UndefinedBadCast) in method equals:  a java.lang.Object cannot be proved to be a MyPath
      @ ensures \result == (((MyPath) obj).size() == nodes.length) && (\forall int i; 0 <= i && i < nodes.length; nodes[i] == ((MyPath) obj).getNode(i));
                             ^
MyPath.java:87: 警告: Associated method exit
            return flag;
            ^
MyPath.java:87: 警告: The prover cannot establish an assertion (Postcondition: MyPath.java:65: 注: ) in method equals
            return flag;
            ^
MyPath.java:65: 警告: Associated declaration: MyPath.java:87: 注:
      @ ensures \result == (((MyPath) obj).size() == nodes.length) && (\forall int i; 0 <= i && i < nodes.length; nodes[i] == ((MyPath) obj).getNode(i));
        ^
MyPath.java:87: 警告: The prover cannot establish an assertion (Postcondition: openjml.jar(specs/java/lang/Object.jml):78: 注: ) in method equals
            return flag;
            ^
openjml.jar(specs/java/lang/Object.jml):78: 警告: Associated declaration: MyPath.java:87: 注:
      @     ensures \result;
            ^
MyPath.java:43: 警告: NOT IMPLEMENTED: Not yet supported feature in converting BasicPrograms to SMTLIB: JML Quantified expression using \num_of
      @ ensures \result == (\num_of int i, j; 0 <= i && i < j
                            ^
MyPath.java:49: 警告: The prover cannot establish an assertion (Precondition: openjml.jar(specs/java/util/Set.jml):81: 注: ) in method getDistinctNodeCount
            set.addAll(path);
                      ^
openjml.jar(specs/java/util/Set.jml):81: 警告: Associated declaration: MyPath.java:49: 注:
    boolean addAll(/*@non_null*/ Collection<? extends E> c) throws NullPointerException;
            ^
openjml.jar(specs/java/util/Collection.jml):268: 警告: Precondition conjunct is false: !\key("RAC") ==> (!containsNull ==> !c.containsNull)
      @   requires !\key("RAC") ==> !containsNull ==> !c.containsNull;
                                ^
openjml.jar(specs/java/util/Collection.jml):277: 警告: Precondition conjunct is false: c == null
      @  requires c == null;
                    ^
MyPath.java:52: 警告: The prover cannot establish an assertion (Postcondition: MyPath.java:43: 注: ) in method getDistinctNodeCount
        return disNum;
        ^
MyPath.java:43: 警告: Associated declaration: MyPath.java:52: 注:
      @ ensures \result == (\num_of int i, j; 0 <= i && i < j
        ^
MyPath.java:33: 警告: The prover cannot establish an assertion (Postcondition: MyPath.java:30: 注: ) in method getNode
        return path.get(index);
        ^
MyPath.java:30: 警告: Associated declaration: MyPath.java:33: 注:
      @ ensures \result == nodes[index];
        ^
MyPath.java:108: 警告: The prover cannot establish an assertion (Postcondition: openjml.jar(specs/java/lang/Object.jml):63: 注: ) in method hashCode
        return path.hashCode();
        ^
openjml.jar(specs/java/lang/Object.jml):63: 警告: Associated declaration: MyPath.java:108: 注:
    //-RAC@ ensures \result == theHashCode;
            ^
MyPath.java:58: 警告: The prover cannot establish an assertion (Postcondition: MyPath.java:56: 注: ) in method isValid
        return path.size() >= 2;
        ^
MyPath.java:56: 警告: Associated declaration: MyPath.java:58: 注:
    //@ ensures \result == (nodes.length >= 2);
        ^
MyPath.java:24: 警告: The prover cannot establish an assertion (Postcondition: MyPath.java:22: 注: ) in method size
        return path.size();
        ^
MyPath.java:22: 警告: Associated declaration: MyPath.java:24: 注:
    //@ ensures \result == nodes.length;
        ^
54 个警告
```

通过命令 `java -jar openjml.jar -cp specs-homework-1-1.1-raw-jar-with-dependencies.jar -rac MyPath.java`进行运行时检查，结果如下：

```java
MyPath.java:43: 注: Runtime assertion checking is not implemented for this type or number of declarations in a quantified expression
      @ ensures \result == (\num_of int i, j; 0 <= i && i < j
                            ^
MyPath.java:9: 警告: JML model field is not implemented: nodes
    //@ public instance model non_null int[] nodes;
                                             ^
1 个警告
```

## (3)部署`JMLUnitNG/JMLUnit`，针对`Graph`接口的实现自动生成测试用例，并结合规格对生成的测试用例和数据进行简要分析 ##

先使用简单的`Demo.java`进行了实验。（来自讨论区大佬的教程）

源码如下：

```java
public class Demo {
    /*@ public normal_behaviour
      @ ensures \result == lhs - rhs;
    */
    public static int compare(int lhs, int rhs) {
        return lhs - rhs;
    }

    public static void main(String[] args) {
        compare(114514,1919810);
    }
}
```

通过指令`java -jar jmlunitng.jar Demo.java`生成了一系列文件。

```bash
├── Demo_InstanceStrategy.java
├── Demo_JML_Data
│   ├── ClassStrategy_int.java
│   ├── ClassStrategy_java_lang_String1DArray.java
│   ├── ClassStrategy_java_lang_String.java
│   ├── compare__int_lhs__int_rhs__0__lhs.java
│   ├── compare__int_lhs__int_rhs__0__rhs.java
│   └── main__String1DArray_args__10__args.java
├── Demo_JML_Test.java
├── PackageStrategy_int.java
├── PackageStrategy_java_lang_String1DArray.java
└── PackageStrategy_java_lang_String.java
```

之后编译` javac -cp jmlunitng.jar *.java`生成了一些`.class`文件

之后运行`java -cp jmlunitng.jar Demo_JML_Test` 结果如下：

```java
[TestNG] Running:
  Command line suite

Failed: racEnabled()
Passed: constructor Demo()
Passed: static compare(-2147483648, -2147483648)
Passed: static compare(0, -2147483648)
Passed: static compare(2147483647, -2147483648)
Passed: static compare(-2147483648, 0)
Passed: static compare(0, 0)
Passed: static compare(2147483647, 0)
Passed: static compare(-2147483648, 2147483647)
Passed: static compare(0, 2147483647)
Passed: static compare(2147483647, 2147483647)
Passed: static main(null)
Passed: static main({})

===============================================
Command line suite
Total tests run: 13, Failures: 1, Skips: 0
===============================================
```

我选择了对`MyPath.java`做测试

命令`java -jar jmlunitng.jar -cp specs-homework-1-1.1-raw-jar-with-dependencies.jar MyPath.java`

命令`javac -cp "specs-homework-1-1.1-raw-jar-with-dependencies.jar;jmlunitng.jar" *.java`

命令`java -cp "specs-homework-1-1.1-raw-jar-with-dependencies.jar;jmlunitng.jar" MyPath_JML_Test`

测试结果：

```java
[TestNG] Running:
  Command line suite

Failed: racEnabled()
Failed: constructor MyPath(null)
Passed: constructor MyPath({})
Failed: <<MyPath@1>>.compareTo(null)
Passed: <<MyPath@1>>.containsNode(-2147483648)
Passed: <<MyPath@1>>.containsNode(0)
Passed: <<MyPath@1>>.containsNode(2147483647)
Passed: <<MyPath@1>>.equals(null)
Passed: <<MyPath@1>>.equals(java.lang.Object@60215eee)
Passed: <<MyPath@1>>.getDistinctNodeCount()
Failed: <<MyPath@1>>.getNode(-2147483648)
Failed: <<MyPath@1>>.getNode(0)
Failed: <<MyPath@1>>.getNode(2147483647)
Passed: <<MyPath@1>>.hashCode()
Passed: <<MyPath@1>>.isValid()
Passed: <<MyPath@1>>.iterator()
Passed: <<MyPath@1>>.size()

===============================================
Command line suites
Total tests run: 17, Failures: 6, Skips: 0
===============================================

```

可以看到它测试了边界的数据，比如对于`getNode()`测试了下标是负数和0的情况，导致了失败`Failed`。对于`compareTo()`测试了输入为`null`的情形，这是我没有考虑到的地方。以及构造函数输入为`null`的情形。但是`getNode()`方法的规格有`@ requires index >= 0 && index < size();`这个前置条件的。

测试代码：`MyPath_JML_Test.java`

```java
/*
 * Test Oracle Class for MyPath
 * For Use With OpenJML RAC
 *
 * Generated by JMLUnitNG 1.4 (116/OpenJML-20131218-REV3178), 2019-05-21 16:36 +0800.
 * (do not modify this comment, it is used by JMLUnitNG clean-up routines)
 */

import java.io.PrintWriter;
import java.util.ArrayList;

import org.jmlspecs.jmlunitng.iterator.IteratorWrapper;
import org.jmlspecs.jmlunitng.iterator.ParameterArrayIterator;
import org.jmlspecs.jmlunitng.testng.BasicTestListener;
import org.jmlspecs.jmlunitng.testng.PreconditionSkipException;
import org.testng.Assert;
import org.testng.TestException;
import org.testng.TestNG;
import org.testng.annotations.DataProvider;
import org.testng.annotations.Test;
import org.testng.xml.XmlSuite;

import org.jmlspecs.utils.JmlAssertionError;
import org.jmlspecs.utils.Utils; 

/**
 * Test oracles generated by JMLUnitNG for OpenJML RAC of class
 * MyPath.
 * 
 * @author JMLUnitNG 1.4 (116/OpenJML-20131218-REV3178)
 * @version 2019-05-21 16:36 +0800
 */

public /*@ nullable_by_default */ class MyPath_JML_Test {
  /**
   * The main method. Allows the tests to be run without a testng.xml or
   * the use of the TestNG executable/plugin.
   *
   * @param the_args Command line arguments, ignored.
   */
  public static void main(String[] the_args) {
    final TestNG testng_runner = new TestNG();
    final Class<?>[] classes = {MyPath_JML_Test.class};
    final BasicTestListener listener =
      new BasicTestListener(new PrintWriter(System.out));
    testng_runner.setUseDefaultListeners(false);
    testng_runner.setXmlSuites(new ArrayList<XmlSuite>());
    testng_runner.setTestClasses(classes);
    testng_runner.addListener(listener);
    testng_runner.run();
  }

  /** 
   * A test to ensure that RAC is enabled before running other tests;
   * this also turns on RAC exceptions if they were not already turned on.
   */
  @Test
  public void test_racEnabled() {
    Utils.useExceptions = true;
    Assert.assertFalse
    (Utils.isRACCompiled(MyPath_JML_Test.class),
     "JMLUnitNG tests must not be RAC-compiled when using OpenJML RAC.");
    Assert.assertTrue
    (Utils.isRACCompiled(MyPath.class),
     "JMLUnitNG tests can only run on RAC-compiled code.");
  } 

  /**
   * A test for method containsNode.
   *
   * @param the_test_object The MyPath to call the test method on.
   * @param node The int to be passed.
   */
  @Test(dependsOnMethods = { "test_racEnabled" }, 
        dataProvider = "p_containsNode__int_node__0")
  public void test_containsNode__int_node__0
  (final MyPath the_test_object, 
   final int node) {
      if (the_test_object == null) {
        throw new PreconditionSkipException
        ("could not construct an object to test");
      }
    try {
      the_test_object.containsNode(node);
    }
    catch (final JmlAssertionError $e) {
      if ($e.jmlAssertionType.equals("Precondition") &&
          $e.getStackTrace().length >= 4 &&
          "test_containsNode__int_node__0".equals($e.getStackTrace()[3].getMethodName())) {
        // meaningless test because precondition failed
        throw new PreconditionSkipException($e.getMessage());
      } else {
        // test failure because something else failed
        throw new TestException($e.getMessage());
      }
    } catch (final Throwable $e) {
      // test failure for some reason other than assertion violation
      throw new TestException($e.getMessage());
    }
  }

  /**
   * A test for method hashCode.
   *
   * @param the_test_object The MyPath to call the test method on.
   */
  @Test(dependsOnMethods = { "test_racEnabled" }, 
        dataProvider = "p_instance_only")
  public void test_hashCode__0
  (final MyPath the_test_object ) {
      if (the_test_object == null) {
        throw new PreconditionSkipException
        ("could not construct an object to test");
      }
    try {
      the_test_object.hashCode();
    }
    catch (final JmlAssertionError $e) {
      if ($e.jmlAssertionType.equals("Precondition") &&
          $e.getStackTrace().length >= 4 &&
          "test_hashCode__0".equals($e.getStackTrace()[3].getMethodName())) {
        // meaningless test because precondition failed
        throw new PreconditionSkipException($e.getMessage());
      } else {
        // test failure because something else failed
        throw new TestException($e.getMessage());
      }
    } catch (final Throwable $e) {
      // test failure for some reason other than assertion violation
      throw new TestException($e.getMessage());
    }
  }

  /**
   * A test for method equals.
   *
   * @param the_test_object The MyPath to call the test method on.
   * @param obj The Object to be passed.
   */
  @Test(dependsOnMethods = { "test_racEnabled" }, 
        dataProvider = "p_equals__Object_obj__10")
  public void test_equals__Object_obj__10
  (final MyPath the_test_object, 
   final java.lang.Object obj) {
      if (the_test_object == null) {
        throw new PreconditionSkipException
        ("could not construct an object to test");
      }
    try {
      the_test_object.equals(obj);
    }
    catch (final JmlAssertionError $e) {
      if ($e.jmlAssertionType.equals("Precondition") &&
          $e.getStackTrace().length >= 4 &&
          "test_equals__Object_obj__10".equals($e.getStackTrace()[3].getMethodName())) {
        // meaningless test because precondition failed
        throw new PreconditionSkipException($e.getMessage());
      } else {
        // test failure because something else failed
        throw new TestException($e.getMessage());
      }
    } catch (final Throwable $e) {
      // test failure for some reason other than assertion violation
      throw new TestException($e.getMessage());
    }
  }

  /**
   * A test for method isValid.
   *
   * @param the_test_object The MyPath to call the test method on.
   */
  @Test(dependsOnMethods = { "test_racEnabled" }, 
        dataProvider = "p_instance_only")
  public void test_isValid__0
  (final MyPath the_test_object ) {
      if (the_test_object == null) {
        throw new PreconditionSkipException
        ("could not construct an object to test");
      }
    try {
      the_test_object.isValid();
    }
    catch (final JmlAssertionError $e) {
      if ($e.jmlAssertionType.equals("Precondition") &&
          $e.getStackTrace().length >= 4 &&
          "test_isValid__0".equals($e.getStackTrace()[3].getMethodName())) {
        // meaningless test because precondition failed
        throw new PreconditionSkipException($e.getMessage());
      } else {
        // test failure because something else failed
        throw new TestException($e.getMessage());
      }
    } catch (final Throwable $e) {
      // test failure for some reason other than assertion violation
      throw new TestException($e.getMessage());
    }
  }

  /**
   * A test for method size.
   *
   * @param the_test_object The MyPath to call the test method on.
   */
  @Test(dependsOnMethods = { "test_racEnabled" }, 
        dataProvider = "p_instance_only")
  public void test_size__0
  (final MyPath the_test_object ) {
      if (the_test_object == null) {
        throw new PreconditionSkipException
        ("could not construct an object to test");
      }
    try {
      the_test_object.size();
    }
    catch (final JmlAssertionError $e) {
      if ($e.jmlAssertionType.equals("Precondition") &&
          $e.getStackTrace().length >= 4 &&
          "test_size__0".equals($e.getStackTrace()[3].getMethodName())) {
        // meaningless test because precondition failed
        throw new PreconditionSkipException($e.getMessage());
      } else {
        // test failure because something else failed
        throw new TestException($e.getMessage());
      }
    } catch (final Throwable $e) {
      // test failure for some reason other than assertion violation
      throw new TestException($e.getMessage());
    }
  }

  /**
   * A test for method getDistinctNodeCount.
   *
   * @param the_test_object The MyPath to call the test method on.
   */
  @Test(dependsOnMethods = { "test_racEnabled" }, 
        dataProvider = "p_instance_only")
  public void test_getDistinctNodeCount__0
  (final MyPath the_test_object ) {
      if (the_test_object == null) {
        throw new PreconditionSkipException
        ("could not construct an object to test");
      }
    try {
      the_test_object.getDistinctNodeCount();
    }
    catch (final JmlAssertionError $e) {
      if ($e.jmlAssertionType.equals("Precondition") &&
          $e.getStackTrace().length >= 4 &&
          "test_getDistinctNodeCount__0".equals($e.getStackTrace()[3].getMethodName())) {
        // meaningless test because precondition failed
        throw new PreconditionSkipException($e.getMessage());
      } else {
        // test failure because something else failed
        throw new TestException($e.getMessage());
      }
    } catch (final Throwable $e) {
      // test failure for some reason other than assertion violation
      throw new TestException($e.getMessage());
    }
  }

  /**
   * A test for method getNode.
   *
   * @param the_test_object The MyPath to call the test method on.
   * @param index The int to be passed.
   */
  @Test(dependsOnMethods = { "test_racEnabled" }, 
        dataProvider = "p_getNode__int_index__0")
  public void test_getNode__int_index__0
  (final MyPath the_test_object, 
   final int index) {
      if (the_test_object == null) {
        throw new PreconditionSkipException
        ("could not construct an object to test");
      }
    try {
      the_test_object.getNode(index);
    }
    catch (final JmlAssertionError $e) {
      if ($e.jmlAssertionType.equals("Precondition") &&
          $e.getStackTrace().length >= 4 &&
          "test_getNode__int_index__0".equals($e.getStackTrace()[3].getMethodName())) {
        // meaningless test because precondition failed
        throw new PreconditionSkipException($e.getMessage());
      } else {
        // test failure because something else failed
        throw new TestException($e.getMessage());
      }
    } catch (final Throwable $e) {
      // test failure for some reason other than assertion violation
      throw new TestException($e.getMessage());
    }
  }

  /**
   * A test for method iterator.
   *
   * @param the_test_object The MyPath to call the test method on.
   */
  @Test(dependsOnMethods = { "test_racEnabled" }, 
        dataProvider = "p_instance_only")
  public void test_iterator__0
  (final MyPath the_test_object ) {
      if (the_test_object == null) {
        throw new PreconditionSkipException
        ("could not construct an object to test");
      }
    try {
      the_test_object.iterator();
    }
    catch (final JmlAssertionError $e) {
      if ($e.jmlAssertionType.equals("Precondition") &&
          $e.getStackTrace().length >= 4 &&
          "test_iterator__0".equals($e.getStackTrace()[3].getMethodName())) {
        // meaningless test because precondition failed
        throw new PreconditionSkipException($e.getMessage());
      } else {
        // test failure because something else failed
        throw new TestException($e.getMessage());
      }
    } catch (final Throwable $e) {
      // test failure for some reason other than assertion violation
      throw new TestException($e.getMessage());
    }
  }

  /**
   * A test for a constructor.
   *
   * @param nodeList The int[] to be passed.
   */
  @Test(dependsOnMethods = { "test_racEnabled" }, 
        dataProvider = "p_MyPath__int1DArray_nodeList__0")
  public void test_MyPath__int1DArray_nodeList__0
  (final int[] nodeList) {
    try {
      new MyPath(nodeList);
    }
    catch (final JmlAssertionError $e) {
      if ($e.jmlAssertionType.equals("Precondition") &&
          $e.getStackTrace().length >= 4 &&
          "test_MyPath__int1DArray_nodeList__0".equals($e.getStackTrace()[3].getMethodName())) {
        // meaningless test because precondition failed
        throw new PreconditionSkipException($e.getMessage());
      } else {
        // test failure because something else failed
        throw new TestException($e.getMessage());
      }
    } catch (final Throwable $e) {
      // test failure for some reason other than assertion violation
      throw new TestException($e.getMessage());
    }
  }

  /**
   * A test for method compareTo.
   *
   * @param the_test_object The MyPath to call the test method on.
   * @param o The Path to be passed.
   */
  @Test(dependsOnMethods = { "test_racEnabled" }, 
        dataProvider = "p_compareTo__Path_o__27")
  public void test_compareTo__Path_o__27
  (final MyPath the_test_object, 
   final com.oocourse.specs1.models.Path o) {
      if (the_test_object == null) {
        throw new PreconditionSkipException
        ("could not construct an object to test");
      }
    try {
      the_test_object.compareTo(o);
    }
    catch (final JmlAssertionError $e) {
      if ($e.jmlAssertionType.equals("Precondition") &&
          $e.getStackTrace().length >= 4 &&
          "test_compareTo__Path_o__27".equals($e.getStackTrace()[3].getMethodName())) {
        // meaningless test because precondition failed
        throw new PreconditionSkipException($e.getMessage());
      } else {
        // test failure because something else failed
        throw new TestException($e.getMessage());
      }
    } catch (final Throwable $e) {
      // test failure for some reason other than assertion violation
      throw new TestException($e.getMessage());
    }
  }

  /**
   * Data provider for method boolean containsNode(int).
   * @return An iterator over strategies to use for parameter generation.
   */
  @SuppressWarnings({"unchecked"})
  @DataProvider(name = "p_containsNode__int_node__0", 
                parallel = false)
  public static IteratorWrapper<Object[]> p_containsNode__int_node__0() {
    return new IteratorWrapper<Object[]>
    (new ParameterArrayIterator
         (MyPath_InstanceStrategy.class,
          MyPath_containsNode__int_node__0__node.class));
  }



  /**
   * Data provider for method boolean equals(Object).
   * @return An iterator over strategies to use for parameter generation.
   */
  @SuppressWarnings({"unchecked"})
  @DataProvider(name = "p_equals__Object_obj__10", 
                parallel = false)
  public static IteratorWrapper<Object[]> p_equals__Object_obj__10() {
    return new IteratorWrapper<Object[]>
    (new ParameterArrayIterator
         (MyPath_InstanceStrategy.class,
          MyPath_equals__Object_obj__10__obj.class));
  }





  /**
   * Data provider for method int getNode(int).
   * @return An iterator over strategies to use for parameter generation.
   */
  @SuppressWarnings({"unchecked"})
  @DataProvider(name = "p_getNode__int_index__0", 
                parallel = false)
  public static IteratorWrapper<Object[]> p_getNode__int_index__0() {
    return new IteratorWrapper<Object[]>
    (new ParameterArrayIterator
         (MyPath_InstanceStrategy.class,
          MyPath_getNode__int_index__0__index.class));
  }



  /**
   * Data provider for constructor MyPath(int[]).
   * @return An iterator over strategies to use for parameter generation.
   */
  @SuppressWarnings({"unchecked"})
  @DataProvider(name = "p_MyPath__int1DArray_nodeList__0", 
                parallel = false)
  public static IteratorWrapper<Object[]> p_MyPath__int1DArray_nodeList__0() {
    return new IteratorWrapper<Object[]>
    (new ParameterArrayIterator
         (MyPath_MyPath__int1DArray_nodeList__0__nodeList.class));
  }


  /**
   * Data provider for method int compareTo(Path).
   * @return An iterator over strategies to use for parameter generation.
   */
  @SuppressWarnings({"unchecked"})
  @DataProvider(name = "p_compareTo__Path_o__27", 
                parallel = false)
  public static IteratorWrapper<Object[]> p_compareTo__Path_o__27() {
    return new IteratorWrapper<Object[]>
    (new ParameterArrayIterator
         (MyPath_InstanceStrategy.class,
          MyPath_compareTo__Path_o__27__o.class));
  }


  /**
   * Data provider for methods with no parameters.
   * @return An iterator over the main class strategy.
   */
  @SuppressWarnings({"unchecked"})
  @DataProvider(name = "p_instance_only", 
                parallel = false)
  public static IteratorWrapper<Object[]> p_instance_only() {
    return new IteratorWrapper<Object[]>
    (new ParameterArrayIterator(MyPath_InstanceStrategy.class));
  }
}
```

## (4)按照作业梳理自己的架构设计，并特别分析迭代中对架构的重构 ##

#### 第9次作业

需要完成的任务为实现两个容器器类 `Path` 和 `PathContainer `

在`PathContainer`中主要的数据结构如下

```java
public class MyPathContainer implements PathContainer {
    private HashMap<Path, Integer> map;
    private HashMap<Integer, Path> idmap;
    private HashMap<Integer,Integer> dismap; //记录每个节点出现的次数
}
```

本次作业为了加快查找的效率，采用了双`HashMap`的方式，映射边和序号的关系。

同时考虑到查询不同节点个数的指令条数很多，需要采用一个均摊的策略，把这个复杂度给均摊到出现次数较少的增删指令上，采用`dismap`这个`HashMap`同于记录每个节点出现的次数，这样在查询不同节点数目的时候只需要返回`dismap.size()`就可以了。

类图：

![h9_2](E:\OO\OO第三次博客作业\h9_2.GIF)

![h9_3](E:\OO\OO第三次博客作业\h9_3.GIF)

复杂度分析：

![h9_1](E:\OO\OO第三次博客作业\h9_1.GIF)

#### 第10次作业

需要完成的任务为实现容器类 `Path` 和数据结构类 `Graph`

接口`Graph`继承自`PathContainer`。

在`Graph`中主要的数据结构如下

```java
public class MyGraph implements Graph {
    private HashMap<Path, Integer> map;
    private HashMap<Integer, Path> idmap;
    private HashMap<Integer,Integer> dismap; //记录每个节点出现的次数
    //邻接表存储的图 from-><to,num> 记录边(from->to) 重边数目为num
    private HashMap<Integer, HashMap<Integer,Integer>> lgraph;
    //用于记录两点之间的最短距离 from-><to,dist>
    private HashMap<Integer, HashMap<Integer,Integer>> dist;
}
```

本次作业构成了图的结构，需求增加了判断连通性和求最短路，所以需要加入一个邻接表用于记录这个图的结构`HashMap<Integer, HashMap<Integer,Integer>> lgraph`，并且考虑到时间的效率，用一个数据结构对计算结果进行缓存`HashMap<Integer, HashMap<Integer,Integer>> dist`，当查询计算过的结果的时候可以直接返回结果，不需要重复计算，这样可以避免过多的重复计算，缩减CPU时间。其他结构则继承自上次的代码结构。

类图：

![h10_2](E:\OO\OO第三次博客作业\h10_2.GIF)

![h10_1](E:\OO\OO第三次博客作业\h10_1.GIF)

复杂度分析：

![h10_3](E:\OO\OO第三次博客作业\h10_3.GIF)

![h10_4](E:\OO\OO第三次博客作业\h10_4.GIF)

#### 第11次作业

需要完成的任务为实现容器类 `Path` ，地铁系统类 `RailwaySystem `

三个接口`RailwaySystem`继承自`Graph`，

在`RailwaySystem`中主要的数据结构如下

```java
public class MyRailwaySystem implements RailwaySystem {
    private HashMap<Path, Integer> map;
    private HashMap<Integer, Path> idmap;
    private HashMap<Integer,Integer> dismap; //记录每个节点出现的次数
    //邻接表存储的图 from-><to,num> 记录边(from->to) 重边数目为num
    private HashMap<Integer, HashMap<Integer,Integer>> lgraph;
    //用于记录两点之间的最短距离 from-><to,dist>
    private HashMap<Integer, HashMap<Integer,Integer>> dist;
    //邻接表存储的图 记录起点和与他邻接点的对应关系 这个图是进行过拆点之后的图
    private HashMap<Pair<Integer,Integer>,HashSet<Pair<Integer,Integer>>> graph;
    //用于记录两个结点之间的最少换乘次数
    private HashMap<Integer,HashMap<Integer,Integer>> traDist;
    //用于记录两个结点之间的最低票价
    private HashMap<Integer,HashMap<Integer,Integer>> priDist;
    //用于记录两个结点之间的最少不满意度
    private HashMap<Integer,HashMap<Integer,Integer>> pleDist;
    //用于计算连通块个数时bfs的标志
    private HashMap<Integer,Integer> vis;
}
```

第11次作业，则在图结构的基础上，增加了最少换乘次数，最低票价，最少不满意度，连通块个数的需求，连通块个数可以直接采用`bfs`进行染色的方法进行计算，而对于三个“最少”的请求，其实实际上他们的方法是相通的，采用拆点的方式，记录了一个新的图`HashMap<Pair<Integer,Integer>,HashSet<Pair<Integer,Integer>>> graph`，在这个图的基础上，其实这三个需求都是**基于权重的最短路**，都可以采用`dijkstra`算法贪心求解。并且同样类似于前一次作业，采用了缓存的方式记录了结果，这里使用了三个`HashMap`分别缓存三种需求的计算结果`(traDist,priDist,pleDist)`避免了重复计算。注意`dijkstra`算法需要**堆优化**。否则O(N^2)复杂度必然超时。其他部分结构继承自前一次作业。

**拆点做法**：

对于每一个点，设立起点和终点，每个点i到终点有一条单向边，权重为0，起点到每一个点i也有一个单向边，权重为0，而终点到起点也有一条单向边，权重则是换乘的代价（换乘次数=1，最少票价=2，不满意度=32）。其他的边都是正常处理即可。这样的图就是一个拆点图了，在此基础之上，进行计算即可。

类图：

![h11_3](E:\OO\OO第三次博客作业\h11_3.GIF)

![h11_4](E:\OO\OO第三次博客作业\h11_4.GIF)

![h11_5](E:\OO\OO第三次博客作业\h11_5.GIF)

复杂度分析：

![h11_1](E:\OO\OO第三次博客作业\h11_1.GIF)

![h11_2](E:\OO\OO第三次博客作业\h11_2.GIF)

三个接口`RailwaySystem`继承自`Graph`，`Graph`继承自`PathContainer`。依次迭代过程中，每次的数据结构都继承自上次的数据结构，并根据需求的增加，增加相应的数据结构完成需求即可。

## (5)按照作业分析代码实现的bug和修复情况

这次的三次作业的强测和互测都没有出现bug

## (6)阐述对规格撰写和理解上的心得体会 ##

本单元的主题是JML规格，首先由于自然语言描述具有二义性，容易产生理解上的偏差，例如在实际工程中，测试人员与程序开发者对于相同问题和需求的理解差异就会造成测试结果的误差。而采用规格化的设计，通过严谨的规格设计，可以避免这样的二义性的出现，也更方便程序员编写精确的高质量代码。**形式化方法是保证软件正确性和质量的一种重要方法。**针对已有的代码实现，书写对应的规格，可以提高代码的可维护性。通过规格设计，我们更容易获得简洁和职责单一的设计和实现。大多数情况下设计和撰写规格要比编写代码难，比如第三次作业的那些“最少换乘次数”、“最少票价”等等的规格描述实际上是很困难的，但是可以确定的是一旦规格确定了，实现代码就变成了一个相对简单的事情了。规格的撰写，我觉得是比较麻烦的一件事，相比于编写代码而言。为了避免二义性，采用了比较规范的类似“数学语言”的描述，而且撰写规格不是撰写代码，规格是比较抽象的。比如对于第三次作业的最少换乘次数，最低票价，最少不满意度，这些规格太过于繁琐了，很难想象自己去撰写这样规模的规格需要花费多久，而且可能还描述的不够完善。

> 由于JML 是一种精确的形式规范描述语言，它能准确表达方法的功能需求，也可以利用自身开发的工具进行高效率的测试。JML 可精确地表达功能模块的行为规范，避免了使用自然语言产生的需求不精确、可能产生歧义的问题，使用 JML 书写的形式化接口规范可以推动程序的自动化测试。

JML有自己的测试工具，有自己的语法规范，相比于采用普通的文本进行程序的规范书写，JML有着独有的优势，它不涉及到具体的代码实现，是代码与需求之间的沟通桥梁。JML语言有前置条件和后置条件，他们是彼此独立的，前置条件出现问题那么说明是用户的输入有问题，后置条件出现问题则说明是程序方法的设计有问题。这样的描述使得程序的可读性更好，设计起来也更加容易，读者的理解也更加容易，可以很清晰的了解一段代码的作用。JML 的形式规范是抽象的，只要阅读某个函数（方法）的形式规范，就能明白这个方法的功能，而不需要阅读这个方法里面用到的其他方法的规格，这样的实现是规模化，模块化的，规格中使用到的其他方法都应该是`pure`的，这样的方法不会修改变量，不会对程序产生影响。JML语言作为一种注释的形式出现在java代码中，不影响正常的程序运行，而且可以通过JML的工具（比如Openjml）进行静态的检查，检查 JML 形式规范是否正确等。如果你的代码没有实现规格中要求的功能，就会给你报错，这是检验一个代码正确性的好办法。基于JML可以进行程序的自动化测试。

总之，通过这个单元的学习，了解了规格的相关内容，学习了JML这个规格描述语言，对于面向对象程序的测试是很有帮助的，希望在未来可以多多使用规格描述，掌握这种契约式的编程方式。