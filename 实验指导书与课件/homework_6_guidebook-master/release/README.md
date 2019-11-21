# README for datacheck

## 使用说明
 - 我们提供了三种操作系统下的可执行文件，大家在各自平台的shell中运行即可，windows推荐使用`PowerShell`或`git-bash`
 - 具体的使用方法为`./datacheck -i <input_path>` 指定你需要测试的输入样例文件的路径即可。
 - 如果程序运行正确则会进行判定，判定为合法样例的将会输出$T_{base}和T_{max}$，不合法的将会输出对应的检查错误信息。如果程序运行错误则会反馈部分报错信息，请正确食用或在讨论区的专用问题反馈贴中回复。

## 使用Demo

准备输入文件`datacheck_in.txt`

```
[0.0]1-FROM-1-TO-15
[1.0]2-FROM-2-TO-15
[2.0]10-FROM-3-TO-15
[3.0]11-FROM-4-TO-15
[4.0]12-FROM-5-TO-15
[11.1]21-FROM-15-TO-1
[12.1]22-FROM-14-TO-2
[13.1]23-FROM-13-TO-3
[14.1]24-FROM-12-TO-4
[15.1]25-FROM-11-TO-5
[40.2]30-FROM-1-TO-3
[41.7]31-FROM-3-TO-5
[43.2]32-FROM-5-TO-7
[44.7]33-FROM-7-TO-9
[46.2]34-FROM-9-TO-15
[46.2]35-FROM-9-TO-15
[46.2]36-FROM-9-TO-14
[46.2]37-FROM-9-TO-10
```

执行命令

```
./datacheck -i datacheck_in.txt
```

输出结果

```
Check Pass!     Your input is valid, base time is 55, max time is 58
```

