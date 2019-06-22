# 第三次规格作业接口使用说明

本次我们继续像是之前一样，提供封装好的jar包给大家。

这次的话，**我们已经将全部的主干业务逻辑进行了封装，只需要同学们实现两个核心类即可**。

前排提醒注意：**本次作业使用的接口，所处的包为`com.oocourse.specs3`，和上次有所不同，请各位注意一定不要用混了**。

## 实现类

### Path

学生需要实现一个自己的Path类，这个**类必须继承接口`com.oocourse.specs3.models.Path`**。

```java
import com.oocourse.specs3.models.Path;

public class MyPath implements Path {
    // TODO : IMPLEMENT
}
```

接口源码设定：

```java
package com.oocourse.specs3.models;

public interface Path extends Iterable<Integer>, Comparable<Path> {
    int size();

    int getNode(int index);

    boolean containsNode(int nodeId);

    int getDistinctNodeCount();

    boolean equals(Object obj);

    boolean isValid();

    int getUnpleasantValue(int nodeId);
}
```

注意：

* 本接口继承了`Iterable<Integer>`迭代器接口，所以**还需要实现迭代器方法`Iterator<Integer> iterator()`**。
* 本接口继承了`Comparable<Path>`偏序比较接口，所以**还需要实现偏序比较方法`int compareTo(Path o)`**。
* 关于迭代器接口、偏序比较接口相关的内容，后文有介绍

### RailwaySystem

学生需要实现一个自己的`RailwaySystem`类，用于管理`Path`对象，这个类必须继承`RailwaySystem`接口

```java
import com.oocourse.specs3.models.RailwaySystem;

public class MyRailwaySystem implements RailwaySystem {
    // TODO : IMPLEMENT
}
```

RailwaySystem接口继承了上次的Graph接口。

其中RailwaySystem接口源码设定：

```java
package com.oocourse.specs3.models;

public interface RailwaySystem extends Graph {
    int getLeastTicketPrice(int fromNodeId, int toNodeId) throws NodeIdNotFoundException, NodeNotConnectedException;

    int getLeastTransferCount(int fromNodeId, int toNodeId) throws NodeIdNotFoundException, NodeNotConnectedException;

    int getUnpleasantValue(Path path, int fromIndex, int toIndex);

    int getLeastUnpleasantValue(int fromNodeId, int toNodeId) throws NodeIdNotFoundException, NodeNotConnectedException;

    int getConnectedBlockCount();
}

```

Graph接口源码设定（与上次相比无变化）：

```java
package com.oocourse.specs3.models;

public interface Graph extends PathContainer {
    boolean containsNode(int nodeId);

    boolean containsEdge(int fromNodeId, int toNodeId);

    boolean isConnected(int fromNodeId, int toNodeId) throws NodeIdNotFoundException;

    int getShortestPathLength(int fromNodeId, int toNodeId) throws NodeIdNotFoundException, NodeNotConnectedException;
}
```

PathContainer接口设定（与上次相比无变化）：

```java
package com.oocourse.specs3.models;

public interface PathContainer {
    int size();

    boolean containsPath(Path path);

    boolean containsPathId(int pathId);

    Path getPathById(int pathId) throws PathIdNotFoundException;

    int getPathId(Path path) throws PathNotFoundException;

    int addPath(Path path);

    int removePath(Path path) throws PathNotFoundException;

    boolean removePathById(int pathId) throws PathIdNotFoundException;

    int getDistinctNodeCount();
}
```

## 开始使用

使用方法非常简单

```java
import com.oocourse.specs3.AppRunner;

public class Main {
    public static void main(String[] args) throws Exception {
        AppRunner runner = AppRunner.newInstance(MyPath.class, MyRailwaySystem.class);
        runner.run(args);
    }
}
```

**将自己实现的Path类和RailwaySystem类作为参数传入**，构造AppRunner对象，并执行run方法即可。

值得注意的是：

* 自己实现的Path类必须继承接口`com.oocourse.specs3.models.Path`，否则将无法传入。
* 自己实现的RailwaySystem类必须继承接口`com.oocourse.specs3.models.RailwaySystem`，否则将无法传入。
* **`Path`类必须实现构造函数`public Path(int[] nodeList)`**（或者`public Path(int... nodeList)`，实际上等价，后文会对此进行介绍），否则会出现报错。
* **`RailwaySystem`类必须实现构造函数`public RailwaySystem()`**，否则会出现报错。

## 科普介绍

### 迭代器的使用简介

容器类型通过继承迭代器，可以实现快速的遍历。

一个超级简单的例子：

文件`TestList.java`

```java
import java.util.ArrayList;
import java.util.Iterator;

class TestList implements Iterable<Integer> {
    private final ArrayList<Integer> list;

    public TestList(ArrayList<Integer> list) {
        this.list = list;
    }

    @Override
    public Iterator<Integer> iterator() {
        return list.iterator();
    }
}
```

文件`TestMain.java`

```java
import java.util.ArrayList;

public class TestMain {
    public static void main(String[] args) throws Exception {
        ArrayList<Integer> originalList = new ArrayList<Integer>() {{
            add(2);
            add(3);
            add(5);
            add(7);
            add(19260817);
        }};
        TestList testList = new TestList(originalList);
        for (Integer integer : testList) {
            System.out.println(integer);
        }
    }
}
```

运行结果：

```
2
3
5
7
19260817
```

简而言之，**通过实现一个iterator方法，即可使你自己定义的类也可以用foreach语法快速遍历**。

关于迭代器的更多用法，可以自己进行百度。搜索关键词：`Java Iterable`。

实际上，如果感兴趣的话，你们依然可以选择读一下`Iterable`接口源码后，逐个实现这个接口的方法。不过本次作业中，方便起见，不建议自己造轮子，还是使用现有容器的iterator接口即可。

### 偏序比较接口使用简介

偏序比较接口，其作用是定义一个类实例的偏序关系。

一个超级简单的例子：

`TestInteger.java`

```java
public class TestInteger implements Comparable<TestInteger> {
    private final int value;

    TestInteger(int value) {
        this.value = value;
    }

    public int getValue() {
        return value;
    }

    @Override
    public int compareTo(TestInteger o) {
        // when this.value < o.value, return < 0
        // when this.value == o.value, return == 0
        // when this.value > o.value, return > 0
        return Integer.compare(this.value, o.value);
    }
}
```

`TestMain.java`

```java
import java.util.ArrayList;
import java.util.Collections;

public class TestMain {
    public static void main(String[] args) throws Exception {
        TestInteger testInteger1 = new TestInteger(1);
        TestInteger testInteger2 = new TestInteger(2);
        TestInteger testInteger3 = new TestInteger(3);
        System.out.println(String.format("#1 vs #2 : %s", testInteger1.compareTo(testInteger2)));
        System.out.println(String.format("#1 vs #1 : %s", testInteger1.compareTo(testInteger1)));
        System.out.println(String.format("#3 vs #2 : %s", testInteger3.compareTo(testInteger2)));

        ArrayList<TestInteger> testIntegers = new ArrayList<TestInteger>() {{
            add(new TestInteger(3));
            add(new TestInteger(7));
            add(new TestInteger(2));
            add(new TestInteger(5));
        }};
        Collections.sort(testIntegers);
        for (TestInteger testInteger : testIntegers) {
            System.out.println(testInteger.getValue());
        }
    }
}
```

输出结果：

```
#1 vs #2 : -1
#1 vs #1 : 0
#3 vs #2 : 1
2
3
5
7
```

偏序接口最厉害的地方在于，你可以自定义对象的偏序关系。

简单来说，**你可以通过实现`int compareTo`方法（返回值小于0表示小于，等于0表示等于，大于0表示大于），自由决定两个对象之间的大小关系**。

比如，只要在上述例子中：

* 将`Integer.compare`的返回结果取反，即可实现反序排序效果
* 将`Integer.compare`的比较对象改为两个数各自的绝对值，即可实现按照绝对值从小到大排序

想要了解更多的的话，可以自行百度探索，搜索关键词：`Java Comparable`。

## 其他

* 本次作业接口下载地址：[下载地址](https://oo-public-1258540306.cos.ap-beijing.myqcloud.com/homeworks/specs_3/specs-homework-3-1.3-raw-jar-with-dependencies.jar)
* 本次作业中，开源代码展示的接口，有**部分仅作为简化jml描述用，实际上无须进行实现，不作为本次作业的强制要求**。此类方法均已经在注释上进行了标注，还请大家注意。（当然，实际上为了方便大家本地使用jml工具进行规格检查，以及使代码层次化更加清晰，还是**建议大家在条件允许的情况下，将这些方法实现出来，以提高程序的可测试性**）。
* 本次作业依然在输出层面上分为加密版和非加密版
  * 非加密版完全公开
  * 加密版只在评测机上使用且闭源，会对输出进行一定程度的加密处理
    * <del>所以，请不要试图伪造输出，还请使用我们的接口</del>
    * 不仅如此，加密版本次编译时加入了源码混淆选项，所有非public的字段、方法、类以及方法实现都会被混淆。
    * <del>所以，请不要试图通过反射来破解接口</del>。互测时发现此类情况，也可以直接举报。
* 特别提醒注意：**本次作业使用的接口，所处的包为`com.oocourse.specs3`，和上次有所不同，请各位注意一定不要用混了**。