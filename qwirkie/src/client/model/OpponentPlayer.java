package client.model;

import exceptions.InvalidMoveException;

/**
 * Placeholder class for lack of better solution. 
 * This class is only created to fill the playerList in Game.
 * @author Han Hollander
 */
public class OpponentPlayer extends Player {
  
  /**
   * Constructs just a player.
   * @param name The player's name;
   * @param playerNumber The ID of the player.
   */
  public OpponentPlayer(String name, int playerNumber) {
    super(name, playerNumber);
  }

  /**
   * This function is never used.
   */
  public Move determineMove(Board board) throws InvalidMoveException {
    return null;
  }
  
}
