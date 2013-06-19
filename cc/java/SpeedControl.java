package concurrency.cruise;


 class SpeedControl implements Runnable {
  final static int DISABLED = 0; //speed control states
  final static int ENABLED  = 1;
  private int state = DISABLED;  //initial state
  private int setSpeed = 0;      //target cruise control speed
  private Thread speedController;
  private CarSpeed cs;         //interface to control speed of engine
  private CruiseDisplay disp;

  SpeedControl(CarSpeed cs, CruiseDisplay disp){
    this.cs=cs; this.disp=disp;
    disp.disable(); disp.record(0);
  }

  synchronized void recordSpeed(){
    setSpeed=cs.getSpeed(); disp.record(setSpeed);
  }

  synchronized void clearSpeed(){
    if (state==DISABLED) {setSpeed=0;disp.record(setSpeed);}
  }

  synchronized void enableControl(){
    if (state==DISABLED) {
      disp.enable();
      speedController= new Thread(this);
      speedController.start();
      state=ENABLED;
    }
  }

  synchronized void disableControl(){
    if (state==ENABLED)  {disp.disable(); state=DISABLED;}
  }

  public void run() {     // the speed controller thread
    try {
      while (state==ENABLED) {
        Thread.sleep(500);
        if (state==ENABLED) synchronized(this) {
          double error = (float)(setSpeed-cs.getSpeed())/6.0;
          double steady = (double)setSpeed/12.0;
          cs.setThrottle(steady+error); //simplified feed back control
        }
      }
    } catch (InterruptedException e) {}
    speedController=null;
  }
}





