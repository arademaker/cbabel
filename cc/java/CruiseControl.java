package concurrency.cruise;

import java.awt.*;
import java.applet.*;

public class CruiseControl extends Applet {

    CarSimulator car;
    CruiseDisplay disp;
    Controller control;
    Button engineOn;
    Button engineOff;
    Button accelerate;
    Button brake;
    Button on;
    Button off;
    Button resume;

    public  void init() {
        String fixed  = getParameter("fixed");
        boolean isfixed = fixed!=null?fixed.equals("TRUE"):false;
        setLayout(new BorderLayout());
        car = new CarSimulator();
        add("Center",car);
        disp = new CruiseDisplay();
        add("East",disp);
        control = new Controller(car,disp,isfixed);
        engineOn = new Button("engineOn");
        engineOff = new Button("engineOff");
        accelerate = new Button("accelerate");
        brake = new Button("brake");
        on = new Button("on");
        off = new Button("off");
        resume = new Button("resume");
        Panel p1 = new Panel();
        p1.setLayout(new FlowLayout());
        p1.add(engineOn);
        p1.add(engineOff);
        p1.add(accelerate);
        p1.add(brake);
        p1.add(on);
        p1.add(off);
        p1.add(resume);
        add("South",p1);
   }

    public void stop() {
        car.engineOff(); //kill engine thread
        control.engineOff();
    }

   public boolean handleEvent(Event event) {
        if (event.id != event.ACTION_EVENT) {
            return super.handleEvent(event);
        } else if(event.target==engineOn) {
            car.engineOn();
            control.engineOn();
            return true;
        } else if (event.target == engineOff) {
            car.engineOff();
            control.engineOff();
            return true;
        } else if (event.target == accelerate) {
            car.accelerate();
            control.accelerator();
            return true;
         } else if (event.target == brake) {
            car.brake();
            control.brake();
            return true;
         } else if (event.target == on) {
            control.on();
            return true;
         } else if (event.target == off) {
            control.off();
            return true;
         } else if (event.target == resume) {
            control.resume();
            return true;
         } else
            return super.handleEvent(event);
    }
}
