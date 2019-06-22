import com.oocourse.TimableOutput;
import com.oocourse.elevator3.PersonRequest;

public class Main {
    public static void main(String[] args) {
        try {
            TimableOutput.initStartTimestamp();
            RequestQueue<PersonRequest> queue = new RequestQueue();
            Thread producer = new Thread(new Input(queue), "input");
            Thread consumer = new Thread(new Schedule(queue), "schedule");
            producer.start();
            consumer.start();
        } catch (Exception e) {
            System.exit(0);
        }
    }
}
