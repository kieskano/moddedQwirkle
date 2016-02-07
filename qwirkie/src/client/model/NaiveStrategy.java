package client.model;

import java.util.ArrayList;
import java.util.List;

/**
 * Class that determines a very naive move.
 * @author Han Hollander
 */
public class NaiveStrategy implements Strategy {
  
  public static final int DIM = 183;

  /**
   * Determines a valid move. Very, very bad AI.
   * @param board The board.
   * @param hand The hand.
   * @param player The computer player.
   */
  public Move determineMove(Board board, List<Tile> hand, ComputerPlayer player) {
    Move result = null;
    List<List<Integer>> places = getPossiblePlaces(board);
    for (Tile tile : hand) {
      for (List<Integer> place : places) {
        Move newMove = new Move(tile, place.get(0), place.get(1));
        if (board.checkMove(newMove)) {
          result = newMove;
        }
      }
    }
    if (result == null) {
      result = new Move(hand.get(0));
    }
    player.setMadeMove(true);
    return result;
  }
  
  /**
   * Gets places where a tile can be.
   * @param board The board.
   * @return A list of free places.
   */
  public List<List<Integer>> getPossiblePlaces(Board board) {
    List<List<Integer>> result = new ArrayList<>();
    Tile empty = new Tile(".", " ");
    for (int i = 0; i < DIM; i++) {
      for (int j = 0; j < DIM; j ++) {
        if (!board.getTile(i, j).equals(empty)) {
          if (board.getTile(i - 1, j).equals(empty)) {
            List<Integer> add = new ArrayList<>();
            add.add(i - 1);
            add.add(j);
            result.add(add);
          } 
          if (board.getTile(i + 1, j).equals(empty)) {
            List<Integer> add = new ArrayList<>();
            add.add(i + 1);
            add.add(j);
            result.add(add);
          }
          if (board.getTile(i, j - 1).equals(empty)) {
            List<Integer> add = new ArrayList<>();
            add.add(i);
            add.add(j - 1);
            result.add(add);
          }
          if (board.getTile(i, j + 1).equals(empty)) {
            List<Integer> add = new ArrayList<>();
            add.add(i);
            add.add(j + 1);
            result.add(add);
          }
        }
      }
    }
    if (result.size() == 0) {
      List<Integer> add = new ArrayList<>();
      add.add(91);
      add.add(91);
      result.add(add);
    }
    return result;
  }

  /**
   * Generate hint.
   * @param board The board.
   * @param hand The current hand.
   * @return hint A new hint.
   */
  public Move getHint(Board board, List<Tile> hand) {
    Move result = null;
    List<List<Integer>> places = getPossiblePlaces(board);
    for (Tile tile : hand) {
      for (List<Integer> place : places) {
        Move newMove = new Move(tile, place.get(0), place.get(1));
        if (board.checkMove(newMove)) {
          result = newMove;
        }
      }
    }
    if (result == null) {
      result = new Move(hand.get(0));
    }
    return result;
  }

}
