import com.oocourse.elevator3.ElevatorInput;
import com.oocourse.elevator3.PersonRequest;

import java.io.File;
import java.io.FileInputStream;
import java.io.IOException;

public class Input implements Runnable {
    private RequestQueue queue;

    public Input(RequestQueue queue) {
        this.queue = queue;
    }

    @Override
    public void run() {
        File f = new File("E:\\data.txt");
        FileInputStream input = null;
        try {
            input = new FileInputStream(f);
        } catch (Exception e) {
            //
        }
        ElevatorInput elevatorInput = new ElevatorInput(input);
        //ElevatorInput elevatorInput = new ElevatorInput(System.in);
        while (true) {
            PersonRequest request = elevatorInput.nextPersonRequest();
            synchronized (queue) {
                if (request == null) {
                    queue.setStop(true);
                    queue.notifyAll();
                    break;
                }
                else {
                    // a new valid request
                    queue.add(request);
                    queue.notifyAll();
                }
            }
        }
        try {
            elevatorInput.close();
        } catch (IOException e) {
            e.printStackTrace();
        }
    }

}
