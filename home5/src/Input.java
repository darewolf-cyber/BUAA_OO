import com.oocourse.elevator1.ElevatorInput;
import com.oocourse.elevator1.PersonRequest;

import java.io.IOException;

public class Input implements Runnable {
    private RequestQueue queue;

    public Input(RequestQueue queue) {
        this.queue = queue;
    }

    @Override
    public void run() {
        ElevatorInput elevatorInput = new ElevatorInput(System.in);
        while (true) {
            PersonRequest request = elevatorInput.nextPersonRequest();
            if (request == null) {
                queue.setStop(true);
                break;
            }
            else {
                // a new valid request
                queue.add(request);
            }
        }
        try {
            elevatorInput.close();
        } catch (IOException e) {
            e.printStackTrace();
        }
    }

}
