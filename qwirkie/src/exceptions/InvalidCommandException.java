package exceptions;

@SuppressWarnings("serial")
public class InvalidCommandException extends Exception {
  
  public InvalidCommandException(String message) {
    super("Invalid command. " + message);
  }

}
