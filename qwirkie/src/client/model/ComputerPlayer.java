package client.model;

import client.view.Printer;
import exceptions.InvalidMoveException;
import exceptions.TileNotInHandException;

/**
 * Computerm ontrolled player class.
 * @author Han Hollander
 */
public class ComputerPlayer extends Player {
  
  private Strategy strategy;
 
  /**
   * Creates a new player with an addition strategy.
   * @param name The name of the player.
   * @param playerNumber The ID of the player. 
   * @param strategy The strategy this player uses.
   */
  public ComputerPlayer(String name, int playerNumber, Strategy strategy) {
    super(name, playerNumber);
    this.strategy = strategy;
  }

  /**
   * Determines the next move the player is going to make.
   * @param board The board.
   * @return A valid move.
   */
  //@ensures board.checkMove(\result);
  public Move determineMove(Board board) throws InvalidMoveException {
    Move result = null;
    if (!isMadeMove()) {      
      result = strategy.determineMove(board, getHand(), this);
      try {
        removeFromHand(result.getTile());
      } catch (TileNotInHandException e) {
        Printer.print(e);
      }
      getMoves().add(result);
    } else if (isMadeMove()) {
      result = new Move();
      setMadeMove(false);
    } 
    return result;
  } 
}
