package exceptions;

@SuppressWarnings("serial")
public class HandIsFullException extends Exception {
  
  public HandIsFullException() {
    super("Your hand is full.");
  }

}
