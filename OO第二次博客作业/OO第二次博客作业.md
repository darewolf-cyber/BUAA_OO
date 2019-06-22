# OO第二次博客作业 #

三次作业内容：多线程电梯（傻瓜调度，ALS捎带策略调度，多电梯）

## (1)从多线程的协同和同步控制方面，分析和总结自己三次作业的设计策略 ##

### 生产者消费者模型 ###

实现方式一：利用Java库中的阻塞队列`BlockingQueue`，生产者消费者两个线程分别持有同一个`BlockingQueue`的对象，利用`put()和`take()`方法实现向队列中的存取。

实现方式二：利用普通的容器类，自行构造一个类，保证其存储和访问的线程安全性即可。

实现方式三：利用`wait()`和`notify()`实现线程之间的通信。

**作业5** 初识多线程，首先想到的是利用`BlockingQueue`，这样的话实现简单，遂笔者首先尝试了它，但是面对电梯作业，发现固然可以非常容易实现基本功能（只需要照搬生产者消费者模型即可），但是`put()`和`take()`方法都是阻塞的，也就是说如果Input输入线程没有输入了，~~（那时由于不会使用`wait()`和`notify()`笔者采用的是暴力轮询）~~就会在`put()`处阻塞住，这就导致了无法在输入`ctrl+D`的时候控制线程退出。发现这个问题后，笔者弃之，开始转向使用自行构造的请求队列类。于是

```java
public class RequestQueue {
    private ArrayList<PersonRequest> bq;
    public synchronized void add(PersonRequest pr) {}
    public synchronized PersonRequest getFirst() {}
    public synchronized boolean isEmpty() {}
    .....
}
```

构造了这个请求队列类，基于`ArrayList`，并采用`synchronized`保证读写安全。

所以，第5次作业实现了2个线程，生产者线程——`Input`负责读取输入请求加入请求队列，消费者线程——`Elevator`负责读出请求队列的请求并进行处理。采用生产者消费者模型，托盘就是请求队列类`RequestQueue`，采用`synchronized`保证读写安全,线程的`run()`方法采用暴力轮询。

关于如何使得输入`ctrl+D`控制线程退出，我在`RequestQueue`类中添加了一个控制信号，初值`false`，并且对这个控制信号的访问也是线程安全的。

```java
public synchronized boolean getStop() {
    return stop;
}
public synchronized void setStop(boolean in) {
    stop = in;
}
```

所以这里也构成一个生产者与消费者的关系，`Input`和`Elevator`共享这个控制信号，`Input`线程读到`ctrl+D`的时候，会把控制信号置为`true`，这是`Input`线程会自动退出,而`Elevator`线程则在控制信号为`true`且请求队列为空的时候退出。注意需要锁住请求队列的对象`queue`。

电梯类退出条件：

```java
while (true) {
	synchronized (queue) {
    	if (queue.isEmpty() && queue.getStop()) {
        	break;
    	}
	}
    .....
}
```

![](E:\OO\OO第二次博客作业\h5.GIF)

**作业6** 在作业5的基础上，由于禁止暴力轮询了，遂笔者开始学习利用`wait()`和`notify()`实现线程之间的通信。同时为了给作业7多电梯做准备，增加一个调度器线程`Schedule`，他持有`Elevator`类的一个对象，本次的基本模型还是生产者消费者模型，区别在于：(1)`Input`线程和`Schedule`线程是一对，`Input`作为生产者向缓冲区加入请求，`Schedule`作为消费者从缓冲区取出请求并分发给电梯，可以预见的是由于只有一部电梯，所以本次作业中`Schedule`的作用只是把请求原样取出，再原样传给电梯，~~（看起来有点蠢，但是这个操作确实让我的第7次作业的扩展容易许多）~~；(2)`Schedule`和`Elevator`又是另一对，`Schedule`作为生产者向电梯的任务队列中加入需要电梯处理的请求，`Elevator`作为消费者从任务队列中取出请求并执行。也就是两对生产者和消费者。

另一点不同之处，作业5的电梯只需要取出请求，依次执行，但是这次需要实现捎带，所以我维护了一个基于`ConcurrentHashMap`的请求队列：

```java
public class FloorQueue {
    private ConcurrentHashMap<Integer,
    			CopyOnWriteArrayList<PersonRequest>> queue;
}        
```

这个队列的作用如下：`key`是楼层号，`value`是这个楼层的人的一个队列。基于这个楼层队列可以实现2个功能：（1）记录电梯外边有哪些人想要进入电梯，也就是`Schedule`和`Elevator`共享的那个缓冲区，`key`代表想上电梯的人所在的楼层。（2）记录电梯里边有哪些人想要下电梯，也就是电梯内部的内队列，`key`代表想下电梯的目标楼层。这样就可以记录每一层的上下人员了，基于`ConcurrentHashMap`的实现比较容易管理，为了保证线程安全性，所以采用的是`ConcurrentHashMap`，人员队列采用的是`CopyOnWriteArrayList`。

（踩坑记录:本来使用的是`ArrayList`，但是对于电梯的内队列由于会涉及到人员想要下电梯，即从队列中删除，和外边的人上电梯，即加入队列，这是在遍历的时候就会出问题，报异常，遂采用`CopyOnWriteArrayList` ）

基于`FloorQueue`可以再每一层都判断下是否有人上下电梯，这样可以实现捎带策略。但是也有一个缺点，由于这样的存储结构没有办法知道请求到达的队列顺序，所以我在`Schedule`和`Elevator`之间还共享了另一个对象`RequestQueue`他可以按照顺序的记录请求的达到，同时在控制`Elevator`线程退出的时候也有作用。

关于如何使得输入`ctrl+D`控制线程退出，`Input`和`Schedule`两个线程跟作业5类似，直接共享了`Requestqueue`对象中的`stop`信号即可控制`Schedule`线程退出，为了控制`Elevator`线程退出，`Schedule`在退出之前，会把他和`Elevator`共享的`RequestQueue`的`stop`信号置为`true`，所以电梯退出的条件就是控制信号为`true`且请求队列为空（没有新请求了）且内队列为空（已有的请求全部处理完成）。

电梯类退出条件：

```java
while (true) {
    synchronized (queue) {
        if (queue.isEmpty() && queue.getStop() && inEle.isEmpty()) {
            break;
        }
    }
}
```

![](E:\OO\OO第二次博客作业\h6.GIF)

**作业7** 在作业6的基础上，要求实现3部电梯，基于作业6的结构，只需要在`Schedule`线程中让他持有三个电梯的对象即可。仍旧是生产者消费者模型，`Input`线程和`Schedule`线程是一对，`Input`作为生产者向缓冲区加入请求，`Schedule`作为消费者从缓冲区取出请求并分发给电梯，采用一定的分配策略，`Schedule`和每一个`Elevator`都一对，`Schedule`作为生产者向电梯的任务队列中加入需要电梯处理的请求，`Elevator`作为消费者从任务队列中取出请求并执行。每一个`Elevator`线程都有自己的内外队列，即需要处理的请求队列和电梯内部人员队列。

```java
public class Schedule implements Runnable {
    private Elevator eleA;   //电梯A
    private Elevator eleB;   //电梯B
    private Elevator eleC;   //电梯C
    private static FloorQueue<Request> outEleA;  //电梯A外的请求
    private static FloorQueue<Request> outEleB;  //电梯B外的请求
    private static FloorQueue<Request> outEleC;  //电梯C外的请求
    private static int numOfTranA = 0;   //以A为换乘电梯的请求数
    private static int numOfTranB = 0;   //以B为换乘电梯的请求数
    private static int numOfTranC = 0;   //以C为换乘电梯的请求数
    private static RequestQueue<Request> queueA; //A全部请求 按顺序的
    private static RequestQueue<Request> queueB; //B全部请求 按顺序的
    private static RequestQueue<Request> queueC; //C全部请求 按顺序的
    private RequestQueue<PersonRequest> queue;  //和Input共享的请求队列
}
```

与作业6一点很大的不同就是，本次的请求可能需要“换乘”，所以，当一个人从一个电梯出来的时候，他可能还需要进入另一部电梯换乘，因此就需要一部电梯可以把请求加入到另一部电梯的待处理请求队列的队列中，我采用的方式是这3个电梯的请求队列都放置在`Schedule`类中，把引用传给`Elevator`这样二者之间的生产者消费者模式容易实现，同时更重要的是，当电梯A请求将一条请求加入电梯B的队列时（即这个人需要从A换乘到B），可以调用`Schedule`类的一个静态方法，直接将请求加入到B的请求队列，实现人员的换乘，一定程度上A与B共享了这个B的待处理请求的队列。

换乘代码：

```java
if (pr.getTranFloor() != pr.getToFloor()) {
    Request req = new Request(pr.getTranFloor(),pr.getToFloor(),
            pr.getToFloor(),pr.getPersonId(), pr.getSecEle(),pr.getSecEle());
    Schedule.addOutFloor(req,pr.getSecEle());
    Schedule.addQueue(req,pr.getSecEle());
    Schedule.subNumofTran(pr.getSecEle());
}
```

```java
public static synchronized void addQueue(Request req, char ch) {
    switch (ch) {
        case 'A':
            synchronized (queueA) {
                queueA.add(req);
                queueA.notifyAll();
            }
            break;
        case 'B':
            ....
        case 'C':
            ....
        default:
    }
}
```

关于如何使得输入`ctrl+D`控制线程退出，`Input`和`Schedule`两个线程跟作业5类似，直接共享了`Requestqueue`对象中的`stop`信号即可控制`Schedule`线程退出，为了控制`Elevator`线程退出，`Schedule`在退出之前，会把他和`Elevator`共享的`RequestQueue`的`stop`信号置为`true`，电梯退出的条件在作业6的基础上，增加了一个换乘数为0的条件，因为如果只是把任务处理完就退出的话，因为换乘的存在，例如A处理了所有任务，想要退出，但是B中下来一个人请求换乘到A，这就需要启动A，所以A不能直接处理完任务就退出。由于笔者的设计中在任务的分配的同时就确定了一个请求的换乘电梯是哪一部电梯，因此在这个同时可以统一计数以每一部电梯作为换乘电梯的请求数量，之后每处理一条换乘请求则数量减1，直到处理完所有的换乘请求，才可以退出，这个量保存在`Schedule`中，在分配任务的时候增加，在电梯执行任务后减1，可以通过静态方法实现，也就是这个量也是`Schedule`和`Elevator`之间共享的。

电梯类退出条件：

```java
while (true) {
    synchronized (queue) {
        if (queue.isEmpty() && queue.getStop() && inEle.isEmpty()
                && Schedule.getNumOfTran(id) == 0) {
            break;
        }
    }
}
```

![](E:\OO\OO第二次博客作业\h7.GIF)

## (2)基于度量来分析自己的程序结构 ##

•度量类的属性个数、方法个数、每个方法规模、每个方法的控制分支数目、类总代码规模

•计算经典的OO度量

•画出自己作业的类图，并自我点评优点和缺点，要结合类图做分析

•通过UML的协作图(sequence diagram)来展示线程之间的协作关系（别忘记主线程）

•从设计原则检查角度，检查自己的设计，并按照SOLID列出所存在的问题

### 作业分析

#### 第5次作业

任务为基于傻瓜调度的多线程电梯。

**解决方案**：主要方案已经在上边给出。就是基于生消模型，但是采用了暴力轮询。共使用了5个类。

**类图**：

![home5_2](E:\OO\OO第二次博客作业\home5_2.GIF)

![home5_3](E:\OO\OO第二次博客作业\home5_3.GIF)

![home5_4](E:\OO\OO第二次博客作业\home5_4.GIF)

**代码复杂度**分析如下

![](E:\OO\OO第二次博客作业\home5_1.GIF)

**优点**：初步了解多线程，写出了多线程程序，这次代码的复杂度分析比前3次作业明显偏低。

**缺点**：采用了暴力轮询的方式，占用CPU。

**修改**：可以改用`wait()`和`notify()`来实现线程的通信。

**UML协作图**：

![](E:\OO\OO第二次博客作业\home5.GIF)

**SOLID (单一功能、开闭原则、里氏替换、接口隔离以及依赖反转)**

**[S] Single Responsibility Principle (单一功能原则)**

`Input`用于读取输入，`Elevator`用于执行请求，`RequestQueue`既保存了请求队列，也保存了共享变量`stop`，用于控制线程退出，`stop`可以另起一个类。

**[o] Open Close Principle （开闭原则）**

满足开闭原则

**[L] Liskov Substitution Principle（里氏替换原则）**

没有使用到继承

**[I] Interface Segregation Principle（接口隔离原则）**

没有使用接口

**[D] Dependency Inversion Principle（依赖反转原则）**

没有使用到抽象类和接口等。不满足依赖反转原则。

#### 第6次作业

**解决方案**：主要方案已经在上边给出。使用`wait()`和`notify()`实现通信，共6个类，电梯调度策略：ALS，所以采用一层一层爬楼梯的方式，每爬一层楼都要检验一下是否有人上下电梯，值得注意的是，由于开关门是有时间的，所以需要在关门之前再次判断一下是否有人要上电梯，因为此时可能这条请求刚刚才达到电梯。

```java
sleep(200);
if (outEle.containsKey(curFloor)) {
    scanOutEle(flag);
}
close();
```

关于ALS的主请求：如果电梯内部为空，就在队列中按照先后顺序取出最先到达的那个；如果电梯内部不为空，就在电梯内部选择主请求，除了在系统刚开始的时候选择一次主请求外，每次选择主请求的时机是在主请求下电梯之后。

```java
public void selectMainReq() {
    if (mainreq == null) {
        if (inEle.isEmpty()) {
            ....在请求队列中选......
            synchronized (queue) {
                while (queue.isEmpty()) {
                    try {
                        queue.wait();
                    } catch (Exception e) {
                        e.printStackTrace();
                    }
                }
                mainreq = queue.first();
                .....
            }
        }
        else {
           ....在电梯内部选......
        }
    }
}
```

关于捎带：跟电梯运动方向一致的请求均可捎带，对于主请求如果他跟我的方向一致则捎带，不一致如果电梯为空则捎带，否则就需要重新在电梯内部选择一个请求做主请求，这个主请求等下次路过再行判断。

```java
if ((pr.getToFloor() > curFloor && direction == 1) ||
        (pr.getToFloor() < curFloor && direction == -1) ||
        pr.equals(mainreq) && inEle.isEmpty() || mainreq == null) {
   ....进入电梯.....
}
else if (pr.equals(mainreq) && !inEle.isEmpty()) {
    .....重选主请求.....
    mainreq = null;
    selectMainReq();
}
```

**类图**：

![home6_2](E:\OO\OO第二次博客作业\home6_2.GIF)

​                      ![home6_3](E:\OO\OO第二次博客作业\home6_3.GIF)

![](E:\OO\OO第二次博客作业\home6_1.GIF)

**代码复杂度**分析如下

![](E:\OO\OO第二次博客作业\home6_4.GIF)

![home6_5](E:\OO\OO第二次博客作业\home6_5.GIF)

**优点**：（1）改用`wait()`和`notify()`来实现线程的通信，节约CPU时间；

（2）使用`ConcurrentHashMap<Integer,CopyOnWriteArrayList<PersonRequest>> queue`这样的队列形式，即可以根据出发楼层存储电梯外的人，也可以目标楼层存储电梯内的人，可以比较容易的实现捎带。

**缺点**：（1）效率不高，这次的性能分偏低，强测分数是历次最低分~~（大佬们优化的比ALS强很多，且测试数据不是随机的，这样对于普适性的算法提升并没好处，因为总有些特殊的测试点会卡你）~~。（2）`Schedule`和`Elevator`之间共享了`FloorQueue`和`RequestQueue`两个队列，浪费内存。（3）电梯类的主要方法，比如`selectMainReq`复杂度太高，没能解耦合

**修改**：（1）可以改用更高效的调度策略，比如look算法，scan算法等。（2）重构一些函数，解耦合。

**UML协作图**：

![](E:\OO\OO第二次博客作业\home6.GIF)

**SOLID (单一功能、开闭原则、里氏替换、接口隔离以及依赖反转)**

**[S] Single Responsibility Principle (单一功能原则)**

`Input`用于读取输入，`Elevator`用于执行请求，`RequestQueue`既保存了请求队列，也保存了共享变量`stop`，用于控制线程退出，`stop`可以另起一个类。

**[o] Open Close Principle （开闭原则）**

满足开闭原则

**[L] Liskov Substitution Principle（里氏替换原则）**

没有使用到继承

**[I] Interface Segregation Principle（接口隔离原则）**

没有使用接口

**[D] Dependency Inversion Principle（依赖反转原则）**

没有使用到抽象类和接口等。不满足依赖反转原则。

#### 第7次作业

**解决方案**：主要方案已经在上边给出。使用`wait()`和`notify()`实现通信，共7个类。

**换乘**的策略：对比作业6，由于需要换乘，我采取的策略是：对一条请求，从`from`到`to`，根据三部电梯的可到达楼层，可以比较容易的验证任意的请求都可以由最多2部电梯完成目标，所以我将`from->to`的过程划分为两段`from->tran`,`tran->to`。而对于可以用一部电梯完成的策略，`tran=to`。所以，在`Schedule`类中，每读到一个请求，都会分配电梯，在这个过程中所做的就是对电梯的选择，暂且不论选择的策略，但是选择之后都会有一个结果，这个结果记录着`from->tran`,`tran->to`这样的一条路径，我使用`Request`类来记录。这样在第一段走完之后，人下电梯，只需要判断`tran`和`to`是否相等就可以知道是否需要换乘，换乘则调用`Schedule`类的方法把他加入到换乘电梯的请求队列即可（前边已经介绍过）

```java
public class Request {
    private int fromFloor;
    private int tranFloor;
    private int toFloor;
    private int personId;
    private char firEle; //第一乘电梯id
    private char secEle; //第二乘电梯id
}
```

换乘：

```java
if (pr.getTranFloor() != pr.getToFloor()) {
    Request req = new Request(pr.getTranFloor(),pr.getToFloor(),
            pr.getToFloor(),pr.getPersonId(), pr.getSecEle(),pr.getSecEle());
    Schedule.addOutFloor(req,pr.getSecEle());
    Schedule.addQueue(req,pr.getSecEle());
    Schedule.subNumofTran(pr.getSecEle());
}
```

**分配**的策略：

（1）对于一部电梯可以送达的请求均一步到位。若A,B,C三部电梯有不止一部可以送达请求，则需要做出选择，选择的策略是主要选择可以捎带的电梯，其次需要考虑已经分配给电梯的请求数是否太多和电梯是否已经满容量，如果均可以捎带，则选择路程较近的，相同条件下还要优先选择运行时间快的。

判断捎带：

```java
public boolean carry(Elevator ele,PersonRequest pr) {
    if ((ele.getCurFloor() < pr.getFromFloor() && ele.getDirection() == 1) ||                  (ele.getCurFloor() > pr.getFromFloor() && ele.getDirection() == -1) ||
            ele.getDirection() == 0 || ele.getCurFloor() == pr.getFromFloor()) {
        return true;
    }
    return false;
}
```

选择电梯的函数：

```java
public void selectTwo(Elevator ele1,Elevator ele2,PersonRequest pr) {
    boolean t1;
    boolean t2;
    t1 = carry(ele1,pr);  //判断捎带
    t2 = carry(ele2,pr);  //判断捎带
    if (t1 && t2) {
        if (!ele1.isFull() && ele2.isFull()) {
            addStright(pr,ele1.getId());
        } else if (!ele2.isFull() && ele1.isFull()) {
            addStright(pr,ele2.getId());
        } else if (!ele1.isFull() && !ele2.isFull()) {  //选距离近的
            if (Math.abs(ele1.getCurFloor() - pr.getFromFloor()) >
                    Math.abs(ele2.getCurFloor() - pr.getFromFloor())) {
                addStright(pr,ele2.getId());
            } else {
                addStright(pr,ele1.getId());
            }
        } else {
            addStright(pr,ele1.getId());
        }
    } else if (t1 && !t2) {
        ......
    } else if (!t1 && t2) {
        ......
    } else {
        ......
    }
}
```

（2）对于一部电梯无法送达的请求，可以验证两部电梯必然可以送达，固分两步，而不分更多了。而如果这里仍面临多种换乘的策略的话，则优先选择速度较快的电梯。换乘点`tran`的选择：优先选择`from`和`to`之间的点做换乘点，如果不能实现，则选择`from`和`to`之外的，注意距离从近到远的选择。

换乘点`tran`的选择：

```java
public int solveOutUp(int i,int j,int id) {}
public int solveOutDown(int i,int j,int id) {}
public int solveInUp(int i,int j,int id) {}
public int solveInDown(int i,int j,int id) {}
```

**类图**：

![](E:\OO\OO第二次博客作业\home7_1.GIF)

![home7_6](E:\OO\OO第二次博客作业\home7_6.GIF)

![home7_7](E:\OO\OO第二次博客作业\home7_7.GIF)

![home7_8](E:\OO\OO第二次博客作业\home7_8.GIF)

**代码复杂度**分析如下

![](E:\OO\OO第二次博客作业\home7_2.GIF)

![home7_3](E:\OO\OO第二次博客作业\home7_3.GIF)

**优点**：基于作业6的架构只需要丰富一下`Schedule`函数的分配策略就可以实现作业7。分配策略简明，写法简单。

**缺点**：（1）除了上次的`Elevator`类的方法之外，本次作业补充的`Schedule`函数的复杂度也是过高，硬编码较多，耦合度过高。（2）效率问题，本次的性能比上一次要好，我想这跟强测数据的随机性有关，但是整体的效率还有很大的提升空间。

**修改**：降低耦合度，主要还是修改分配策略的实现函数，甚至于对于架构的改革。但目前没有太好的想法改革架构。主要应该还是考虑下分配策略，目前只是简单的“**哪部电梯可以运，就给那部电梯运**”。

**UML协作图**：

![](E:\OO\OO第二次博客作业\home7.GIF)

**SOLID (单一功能、开闭原则、里氏替换、接口隔离以及依赖反转)**

**[S] Single Responsibility Principle (单一功能原则)**

`Input`用于读取输入，`Elevator`用于执行请求，`RequestQueue`既保存了请求队列，也保存了共享变量`stop`，用于控制线程退出，`stop`可以另起一个类。

**[o] Open Close Principle （开闭原则）**

满足开闭原则

**[L] Liskov Substitution Principle（里氏替换原则）**

没有使用到继承，本来可以`Request`类继承`PersonRequest`，但是我写的时候输入接口的构造方法还是`private`，于是就自己构造的一个`Request`类。

**[I] Interface Segregation Principle（接口隔离原则）**

没有使用接口

**[D] Dependency Inversion Principle（依赖反转原则）**

没有使用到抽象类和接口等。不满足依赖反转原则。

## (3)分析自己程序的bug  ##

这3次作业出现的bug只有**作业7的互测**被找到了一个bug。主要原因是，由于这次的电梯有了容量限制，所以当电梯满员之后任何请求都无法进入电梯，但是基于作业6的架构，我的主请求如果无法进入电梯，就说明此时主请求已经跟电梯**方向不一致**而且**电梯里边有人**，这时候我不让主请求进入电梯，而是采用重新选取电梯内部请求作为主请求的策略，但是这次的写法之中，我在判断电梯满员之后直接跳出了循环而没有去判断这层楼是否隐藏着主请求，但是此时主请求也没法进入电梯了，因为电梯满了，所以需要修改一个主请求，而我没有修改因此电梯没了方向，就停下不动了。

原代码：

```java
for (Request pr : outEle.get(curFloor)) {
    if (curNum == maxNum) {  //满员直接break
        break;
    }
    if ((pr.getTranFloor() > curFloor && direction == 1) ||
            (pr.getTranFloor() < curFloor && direction == -1) ||
            pr.equals(mainreq) && inEle.isEmpty() || mainreq == null) {
       .....进入电梯.....
    }
    else if (pr.equals(mainreq) && !inEle.isEmpty()) {
        //由于主请求没进来，需要重新选一个主请求
        mainreq = null;
        selectMainReq();
    }
}
```

修改方案：

````java
for (Request pr : outEle.get(curFloor)) {
    if (curNum == maxNum) {  //满员
        if (outEle.get(curFloor).contains(mainreq)) { //看一下当前楼层有没有主请求 有的话重选一个 因为他进不去了
              mainreq = null;
              selectMainReq();
        }
        break;
    }
    if ((pr.getTranFloor() > curFloor && direction == 1) ||
            (pr.getTranFloor() < curFloor && direction == -1) ||
            pr.equals(mainreq) && inEle.isEmpty() || mainreq == null) {
       .....进入电梯.....
    }
    else if (pr.equals(mainreq) && !inEle.isEmpty()) {
        //由于主请求没进来，需要重新选一个主请求
        mainreq = null;
        selectMainReq();
    }
}
````

其实关键的问题就是**主请求是否上电梯**这样的一个问题，本来最初的设计（作业6）我采用的是主请求都能上电梯，但是这样就可能导致因为捎带而进入的人没有到达目的地电梯剧转向了。所以我加入一个规则使得主请求可能进不来，而作业7其实又加了一个规则**电梯满员了主请求也进不来**，对于进不来的情况**均需要更换请求**。

这次的Bug不是很容易发现，因为一组数据能够恰好使得**电梯满员而且主请求之后才随之到来恰好没能进入电梯**，很难找到，自行测试了几十组50请求量级的数据也没能发现。

## (4)分析自己发现别人程序bug所采用的策略 ##

**测试策略**：

作业5：由于不会如何做到定时投放，所以只能在某个时刻做输入，但是由于策略采用的是傻瓜调度，所以也比较容易，大家的程序基本也都没有bug。

作业6和作业7：在作业6结束之前，何岱岚同学在讨论区发了可以实现定时投放的jar包，所以在之后的两次作业中都可以实现定时投放，所以只需要自己实现一个随机函数生成测试数据和一个运行测试结果是否正确的函数即可实现一个半自动化的测试了。

所以，做的都是**随机化的测试，没有结合被测程序的代码设计结构来设计测试用例**。

**生成数据函数**：

```java
class A{
    String str;
    double data;
    public A(String str, double data) {
        this.str = str;
        this.data = data;
    }
    @Override
    public String toString() {
        return str;
    }
}
public class RandData {
    public static void main(String[] args) throws Exception{
        FileOutputStream out = new FileOutputStream(new File("E:\\data.txt"));
        Random r = new Random(System.currentTimeMillis());
        ArrayList<A> queue = new ArrayList<>();
        for (int i = 0;i < 50;i++){
            StringBuilder sb = new StringBuilder("");
            sb.append("[");
            double time = r.nextFloat()*40.0;
            String s = String.format("%.1f", time);
            sb.append(s);
            sb.append("]");
            sb.append(i+"-FROM-");
            int n1 = r.nextInt(24)-3;
            while (n1 == 0) {
                n1 = r.nextInt(24)-3;
            }
            sb.append(n1);
            sb.append("-TO-");
            int n2 = r.nextInt(24)-3;
            while (n2 == 0 || n2 == n1) {
                n2 = r.nextInt(24)-3;
            }
            sb.append(n2);
            sb.append("\n");
            queue.add(new A(sb.toString(),Double.parseDouble(s)));
        }
        queue.sort(new Comparator<A>() {
            @Override
            public int compare(A o1, A o2) {
                if(o1.data > o2.data){
                    return 1;
                }
                else{
                    return -1;
                }
            }
        });
        for(A a : queue) {
            out.write(a.toString().getBytes());
            System.out.print(a);
        }
    }
}
```

**验证正确性的代码（部分）**:

```java
checkNum(list);//最大人数限制
checkOpenClose(listA,'A');//open与close一一对应 且时间间隔0.4以上 只能在可以停靠的楼层开关门
checkOpenClose(listB,'B');//open close之间不能arrive
checkOpenClose(listC,'C');//除了第一次 都得先arrive再open
checkArrive(listA,'A');//两个楼层之间的运行时间大于等于理论运行时间和楼层变化
checkArrive(listB,'B');//关门和arrive之间的时间 和楼层变化
checkArrive(listC,'C');
//判断每个请求是否到达目的地
while((str=bf1.readLine()) != null) {
    Matcher m1 = Pattern.compile(pattern1).matcher(str);
    if (m1.matches()) {
        String id = m1.group(1);
        String from = m1.group(2);
        String to = m1.group(3);
        boolean a = checkINOUT(id,from,to,listA,"A");
        boolean b = checkINOUT(id,from,to,listB,"B");
        boolean c = checkINOUT(id,from,to,listC,"C");
        if(a){
            System.out.println("Request:("+str+")solved by eleA");
        }else if(b){
            System.out.println("Request:("+str+")solved by eleB");
        }else if(c){
            System.out.println("Request:("+str+")solved by eleC");
        }else{
            boolean t1,t2;
            boolean f = false;
            for(int k=-3;k<=20;k++){
                if(k==0) continue;
                t1=checkINOUT(id,from,k+"",listA,"A");
                t2=checkINOUT(id,k+"",to,listB,"B");
                if(t1&&t2){
                    System.out.println("Request:("+str+")solved by eleA and eleB,tran floor is "+k);
                }
                t1=checkINOUT(id,from,k+"",listB,"B");
                t2=checkINOUT(id,k+"",to,listA,"A");
                if(t1&&t2){
                    System.out.println("Request:("+str+")solved by eleB and eleA,tran floor is "+k);
                }
                t1=checkINOUT(id,from,k+"",listB,"B");
                t2=checkINOUT(id,k+"",to,listC,"C");
                if(t1&&t2){
                    System.out.println("Request:("+str+")solved by eleB and eleC,tran floor is "+k);
                }
                t1=checkINOUT(id,from,k+"",listC,"C");
                t2=checkINOUT(id,k+"",to,listB,"B");
                if(t1&&t2){
                    System.out.println("Request:("+str+")solved by eleC and eleB,tran floor is "+k);
                }
                t1=checkINOUT(id,from,k+"",listA,"A");
                t2=checkINOUT(id,k+"",to,listC,"C");
                if(t1&&t2){
                    System.out.println("Request:("+str+")solved by eleA and eleC,tran floor is "+k);
                }
                t1=checkINOUT(id,from,k+"",listC,"C");
                t2=checkINOUT(id,k+"",to,listA,"A");
                if(t1&&t2){
                    System.out.println("Request:("+str+")solved by eleC and eleA,tran floor is "+k);
                }
            }
        }
    }
    else {
        System.err.println("wrong input format");
    }
}
```

**测试策略与第一单元测试策略的差异之处**：

第一单元的测试只需要生成数据之后运行即可，输出结果也是相对固定的（顶多是化简程度不同），但是多线程的程序就可能涉及到了不确定的因素了，而且电梯的要求比较多，所以用于验证结果是否正确的程序比较难写。但是主要的难点还是**如何实现定时投放**,我想前2次互测空刀比较多也是因为不知道如何定时投放所以难以测试，只能在同一个时刻同时输入很多组请求，测试效果比较差。

**发现线程安全相关的问题**：

只是通过**大量数据的随机化测试**，判断结果是否正确。比如1000+条指令定时投放判断正确性。

**利用文件输入**可以一定程度模拟测评机的输入~~（相比于手动输入）~~，如果有线程不安全的问题，或者比如控制线程结束时有误等，利用文件输入会比手动输入更容易发现问题，比如文件输入就可能会出现电梯没有处理完全部请求就停止工作了，一般手动输入就难以发现。

## (5) 心得体会 ##

从线程安全和设计原则两个方面来梳理自己在本单元三次作业中获得的心得体会

### (1)线程安全 ###

作业5第一次接触多线程的时候，写代码过程中出现2个关于线程安全的bug。

**1.电梯的`run()`函数**

错误版本：

```java
@Override
public void run() {
    while (true) {
        PersonRequest pr = queue.getFirst();
        .......
        if (queue.isEmpty() && queue.getStop()) {
            break;
        }
    }
}
```

正确版本：

````java
@Override
public void run() {
    while (true) {
        synchronized (queue) {
            if (queue.isEmpty() && queue.getStop() && inEle.isEmpty()) {
                 break;
            }
        }
        PersonRequest pr = queue.getFirst();
        .......
    }
}
````

由此可以看到，`queue.isEmpty()`和`queue.getStop()`之间可能会有线程安全问题，可能会插入别的语句，导致`queue`的内容被修改了，所以这里的条件判断就会出错，因此需要`synchronized`给`queue`加锁。

**2.关于如何结束电梯线程**

利用一个变量，当`Input`线程读入到`ctrl+D`的时候，置位，然后`Elevator`线程得到信号之后就可以`break`。

错误版本：没有实现线程安全的访问，`Input`中把`Elevator`中的静态变量`stop`设为`true`，`Elevator`中得到信号就可以`break`。但是这样不是线程安全的。

```java
Input:
if (request == null) {
    Elevator.setStop();
    break;
}
Elevator:
public class Elevator implements Runnable {
    private RequestQueue queue;
    private static boolean stop = false;
    public static void setStop() {
        stop = true;
    }
    run():
	while (true) {
    	PersonRequest pr = queue.getFirst();
    	if (pr != null) {
        	......
    	} else if (stop) {
       	 	break;
    	}
	}
}
```

正确版本：这个变量是共享的，加入`RequestQueue`类作为生产者消费者之间的共享缓冲区。

```java
Input:
if (request == null) {
    queue.setStop(true);
    break;
}
RequestQueue:
public class RequestQueue {
    private ArrayList<PersonRequest> bq;
    private boolean stop;
    public synchronized boolean getStop() {
        return stop;
    }
    public synchronized void setStop(boolean in) {
        stop = in;
    }
}
Elevator:
run():
synchronized (queue) {
   if (queue.isEmpty() && queue.getStop() && inEle.isEmpty()) {
        break;
   }
}
```

所以，经过发现并修改这2个bug，深刻的了解了一些线程安全的问题，在多线程的程序中如果不注意的话，就会有很大的问题。包括在后序作业中使用了`ConcurrentHashMap`和`CopyOnWriteArrayList`都是考虑到线程安全问题。**这个Debug真的很难**。

### (2)设计原则 ###

这几次作业主要都在考虑如何保证正确性并一定程度提升性能，所以都是集中于架构的考虑，没有十分注意设计原则问题，希望在之后的作业中可以多加注意。

通过对3次作业的分析可以看出，**SOLID (单一功能、开闭原则、里氏替换、接口隔离以及依赖反转)**这五个原则中，我基本做到了**[S] Single Responsibility Principle (单一功能原则)**和**[o] Open Close Principle （开闭原则）**，而对于**[L] Liskov Substitution Principle（里氏替换原则）**和**[I] Interface Segregation Principle（接口隔离原则）**则由于没有使用继承和接口而没有实现，最后对于**[D] Dependency Inversion Principle（依赖反转原则）**则并没有实现，我感觉这个原则是5大原则中最难理解和最难实现的一个，目前我对它并不是十分理解，将要在之后几天里多多了解一下。