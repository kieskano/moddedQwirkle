package server.controller;

public class Timer extends Thread{
  
  private Server server;
  private Object timerMonitor;
  private long time;
  private boolean stoppedFromTheOutside;
  
  /**
   * Creates a new timer thread which notifies the given 
   * server if the give time has ran out.
   * @param time The time in milliseconds for how long the timer
   *             needs to be set.
   * @param server The server which needs to be notified
   *               when the timer has stopped.
   */
  public Timer(int time, Server server) {
    this.server = server;
    this.time = new Long(time);
    this.stoppedFromTheOutside = false;
    timerMonitor = new Object();
  }
  
  /**
   * Starts the timer and notifies the server when the
   * timer stops if the timer was not stopped by the server.
   */
  public void run() {
    synchronized (timerMonitor) {
      try {
        timerMonitor.wait(time);
      } catch (InterruptedException e) {
        server.getObserver().print("Timer thread got interupted");
      }
      if (!stoppedFromTheOutside) {
        server.timerWakesServer();
      }
    }
  }
  
  /**
   * The function that can be called from another thread to stop the timer.
   */
  public void stopTimer() {
    stoppedFromTheOutside = true;
    synchronized (timerMonitor) {
      timerMonitor.notifyAll();
    }
  }
  
}
