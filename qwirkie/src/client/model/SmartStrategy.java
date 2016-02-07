package client.model;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Set;

/**
 * A smart strategy to determine the best possible move.
 * @author Wijtse Rekker
 */
public class SmartStrategy implements Strategy {
  
  public static final int DIM = 183;

  private List<Move> thePerfectTurn;
  
  public SmartStrategy() {
    thePerfectTurn = new ArrayList<>();
  }
  
  /**
   * Calculates the best move possible with the current board and hand.
   */
  public Move determineMove(Board board, List<Tile> hand, ComputerPlayer player) {
    Move theMove;
    if (thePerfectTurn.size() == 0) {
      List<List<Integer>> possiblePlaces = getPossiblePlaces(board);
      HashMap<List<Move>, Integer> result = new HashMap<List<Move>, Integer>();
      for (List<Integer> coord : possiblePlaces) {
        for (Tile tile : hand) {
          int row = coord.get(0);
          int col = coord.get(1);
          Move move = new Move(tile, row, col);
          if (board.checkMove(move)) {
            calculateBestOutcome(board, hand, result, tile, move);
          }
        }
      }
      Set<List<Move>> resultKeySet = result.keySet();
      List<Move> bestTurn = new ArrayList<Move>();;
      int bestScore = -1;
      for (List<Move> selectedTurn : resultKeySet) {
        int turnScore = result.get(selectedTurn);
        if (turnScore > bestScore) {
          bestTurn = new ArrayList<Move>();
          bestTurn.addAll(selectedTurn);
          bestScore = turnScore;
        }
      }
      thePerfectTurn = new ArrayList<Move>();
      if (bestTurn.size() > 0) {
        thePerfectTurn.addAll(bestTurn);
      } else {
        thePerfectTurn.addAll(getBestSwapTurn(hand));
      }
      theMove = thePerfectTurn.get(0);
      thePerfectTurn.remove(0);
      if (thePerfectTurn.size() == 0) { 
        player.setMadeMove(true);
      }
    } else {
      theMove = thePerfectTurn.get(0);
      thePerfectTurn.remove(0);
      if (thePerfectTurn.size() == 0) { 
        player.setMadeMove(true);
      }
    }
    return theMove;
  }

  /**
   * Calculates the best possible moves with the given move as start move.
   * @param board The board.
   * @param hand The players hand.
   * @param result The result in which the best possible turns and scores will be added.
   * @param tile The tile that was just placed.
   * @param move The move that was just made.
   */
  private void calculateBestOutcome(Board board, List<Tile> hand,
      HashMap<List<Move>, Integer> result, Tile tile, Move move) {
    List<Tile> testHand = new ArrayList<>();
    List<Move> testTurn = new ArrayList<>();
    testTurn.add(move);
    testHand.addAll(hand);
    testHand.remove(tile);
    Board testBoard = board.deepCopy();
    testBoard.putTile(move);
    HashMap<List<Move>, Integer> tussenResult = new HashMap<List<Move>, Integer>();
    tussenResult = getBestTurn(testBoard, hand, testTurn);
    Set<List<Move>> tussenResultKeySet = tussenResult.keySet();
    for (List<Move> tussenTurn : tussenResultKeySet) {
      result.put(tussenTurn, tussenResult.get(tussenTurn));
    }
  }
  
  /**
   * Calculates which tiles out of the hand are the best tiles to swap.
   * @param hand From which the tiles need to be swapped.
   * @return A list of well calculated swap moves.
   */
  public List<Move> getBestSwapTurn(List<Tile> hand) {
    // Check if you got tiles double in your hand
    List<Tile> doubleTiles = new ArrayList<Tile>();
    for (Tile tile : hand) {
      List<Tile> testHand = new ArrayList<Tile>();
      testHand.addAll(hand);
      testHand.remove(tile);
      for (Tile tile2 : testHand) {
        if (tile.equals(tile2)) {
          doubleTiles.add(tile2);
        }
      }
    }
    
    List<Move> result = new ArrayList<Move>();
    if (doubleTiles.size() > 0) {
      for (Tile tile : doubleTiles) {
        result.add(new Move(tile));
      }
    }
    
    if (result.size() == 0) {
      result.add(new Move(hand.get(0)));
    }
    
    return result;
  }

  /**
   * Gets places where a tile can be.
   * @param board the board
   * @return list of places
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
   * A recursive function which calculates the outcome of every possible
   * move with the given board, hand and already placed tiles this turn.
   * @param board The board.
   * @param hand The hand of the player.
   * @param turn The already made moves this turn.
   * @return A hash map with the moves of a turn as key and the score of that turn as value.
   */
  public HashMap<List<Move>, Integer> getBestTurn(Board board, List<Tile> hand, List<Move> turn) {
    Tile empty = new Tile(".", " ");
    Move move = turn.get(turn.size() - 1);
    int row = move.getRow();
    int col = move.getColumn();
    HashMap<List<Move>, Integer> result = new HashMap<List<Move>, Integer>();
    if (board.getTile(row + 1, col).equals(empty)) {
      for (Tile tile : hand) {
        Move testMove = new Move(tile, row + 1, col);
        if (board.checkMove(testMove)) {
          List<Tile> testHand = new ArrayList<>();
          List<Move> testTurn = new ArrayList<>();
          testTurn.addAll(turn);
          testTurn.add(testMove);
          testHand.addAll(hand);
          testHand.remove(tile);
          Board testBoard = board.deepCopy();
          testBoard.putTile(testMove);
          HashMap<List<Move>, Integer> tussenResult = new HashMap<List<Move>, Integer>();
          tussenResult = getBestTurn(testBoard, hand, testTurn);
          Set<List<Move>> tussenResultKeySet = tussenResult.keySet();
          for (List<Move> tussenTurn : tussenResultKeySet) {
            result.put(tussenTurn, tussenResult.get(tussenTurn));
          }
        }
      }
    }
    if (board.getTile(row - 1, col).equals(empty)) {
      for (Tile tile : hand) {
        Move testMove = new Move(tile, row - 1, col);
        if (board.checkMove(testMove)) {
          List<Tile> testHand = new ArrayList<>();
          List<Move> testTurn = new ArrayList<>();
          testTurn.addAll(turn);
          testTurn.add(testMove);
          testHand.addAll(hand);
          testHand.remove(tile);
          Board testBoard = board.deepCopy();
          testBoard.putTile(testMove);
          HashMap<List<Move>, Integer> tussenResult = new HashMap<List<Move>, Integer>();
          tussenResult = getBestTurn(testBoard, hand, testTurn);
          Set<List<Move>> tussenResultKeySet = tussenResult.keySet();
          for (List<Move> tussenTurn : tussenResultKeySet) {
            result.put(tussenTurn, tussenResult.get(tussenTurn));
          }
        }
      }
    }
    if (board.getTile(row, col + 1).equals(empty)) {
      for (Tile tile : hand) {
        Move testMove = new Move(tile, row, col + 1);
        if (board.checkMove(testMove)) {
          List<Tile> testHand = new ArrayList<>();
          List<Move> testTurn = new ArrayList<>();
          testTurn.addAll(turn);
          testTurn.add(testMove);
          testHand.addAll(hand);
          testHand.remove(tile);
          Board testBoard = board.deepCopy();
          testBoard.putTile(testMove);
          HashMap<List<Move>, Integer> tussenResult = new HashMap<List<Move>, Integer>();
          tussenResult = getBestTurn(testBoard, hand, testTurn);
          Set<List<Move>> tussenResultKeySet = tussenResult.keySet();
          for (List<Move> tussenTurn : tussenResultKeySet) {
            result.put(tussenTurn, tussenResult.get(tussenTurn));
          }
        }
      }
    }
    if (board.getTile(row, col - 1).equals(empty)) {
      for (Tile tile : hand) {
        Move testMove = new Move(tile, row, col - 1);
        if (board.checkMove(testMove)) {
          List<Tile> testHand = new ArrayList<>();
          List<Move> testTurn = new ArrayList<>();
          testTurn.addAll(turn);
          testTurn.add(testMove);
          testHand.addAll(hand);
          testHand.remove(tile);
          Board testBoard = board.deepCopy();
          testBoard.putTile(testMove);
          HashMap<List<Move>, Integer> tussenResult = new HashMap<List<Move>, Integer>();
          tussenResult = getBestTurn(testBoard, hand, testTurn);
          Set<List<Move>> tussenResultKeySet = tussenResult.keySet();
          for (List<Move> tussenTurn : tussenResultKeySet) {
            result.put(tussenTurn, tussenResult.get(tussenTurn));
          }
        }
      }
    }
    if (result.size() == 0) {
      result.put(turn, board.getScoreCurrentTurn());
    } else {
      Set<List<Move>> resultKeySet = result.keySet();
      List<Move> bestTurn = new ArrayList<Move>();;
      int bestScore = -1;
      for (List<Move> selectedTurn : resultKeySet) {
        int turnScore = result.get(selectedTurn);
        if ( turnScore > bestScore) {
          bestTurn = new ArrayList<Move>();
          bestTurn.addAll(selectedTurn);
          bestScore = turnScore;
        }
      }
      result = new HashMap<List<Move>, Integer>();
      result.put(bestTurn, bestScore);
    }
    return result;
  }
}
