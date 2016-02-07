package exceptions;

@SuppressWarnings("serial")
public class InvalidMoveException extends Exception {
  
  public InvalidMoveException(String message) {
    super("Invalid move. " + message);
  }

}
