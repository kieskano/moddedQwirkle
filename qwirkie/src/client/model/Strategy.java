package client.model;

import java.util.List;

/**
 * Super simple interface for a strategy.
 * @author Han Hollander
 */
public interface Strategy {
  
  public Move determineMove(Board board, List<Tile> hand, ComputerPlayer player);

}