import com.oocourse.uml2.interact.AppRunner;
import elements.MyGeneralInteraction;

/**
 * Emmmm这个地方应该不需要注释了吧？
 * （以下是官方吐槽系列：
 * 1、讲真，这次作业函数式真心是MVP[捂脸]，写起来超舒服，维护性超级好，多核环境下挂上并行跑起来还贼快
 * 2、如果大家这学期课程结束后感兴趣的话，可以作为兴趣了解下这方面的技术
 * ）
 */
public class Main {
    public static void main(String[] args)
            throws Exception {
        AppRunner appRunner = AppRunner.newInstance(
                MyGeneralInteraction.class);
        appRunner.run(args);
    }
}
