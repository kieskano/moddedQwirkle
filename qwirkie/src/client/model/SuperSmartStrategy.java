package client.model;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.List;
import java.util.Set;

/**
 * A smart strategy to determine the best possible move.
 * @author Wijtse Rekker
 */
public class SuperSmartStrategy implements Strategy {
  
  public static final List<String> COLOURS = Arrays.asList("R", "O", "B", "Y", "G", "P");
  public static final List<String> SHAPES = Arrays.asList("o", "d", "s", "c", "x", "*");
  
  public static final int DIM = 183;

  private List<Move> thePerfectTurn;
  
  public SuperSmartStrategy() {
    thePerfectTurn = new ArrayList<>();
  }
  
  /**
   * Calculates the best move possible with the current board and hand.
   */
  public Move determineMove(Board board, List<Tile> hand, ComputerPlayer player) {
    Move theMove;
    if (thePerfectTurn.size() == 0) {
      Board reserveBoard = board.deepCopy();
      List<List<Integer>> possiblePlaces = getPossiblePlaces(board);
      HashMap<List<Move>, Integer> result = new HashMap<List<Move>, Integer>();
      for (List<Integer> coord : possiblePlaces) {
        for (Tile tile : hand) {
          int row = coord.get(0);
          int col = coord.get(1);
          Move move = new Move(tile, row, col);
          if (board.checkMove(move)) {
            calculateBestOutcome(board, hand, result, tile, move, reserveBoard);
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
   * @param hand The players hand.432
   * @param result The result in which the best possible turns and scores will be added.
   * @param tile The tile that was just placed.
   * @param move The move that was just made.
   */
  private void calculateBestOutcome(Board board, List<Tile> hand,
      HashMap<List<Move>, Integer> result, Tile tile, Move move, Board reserveBoard) {
    List<Tile> testHand = new ArrayList<>();
    List<Move> testTurn = new ArrayList<>();
    testTurn.add(move);
    testHand.addAll(hand);
    testHand.remove(tile);
    Board testBoard = board.deepCopy();
    testBoard.putTile(move);
    HashMap<List<Move>, Integer> tussenResult = new HashMap<List<Move>, Integer>();
    tussenResult = getBestTurn(testBoard, hand, testTurn, reserveBoard);
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
  private List<Move> getBestSwapTurn(List<Tile> hand) {
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
    // Check if you got bad tiles in your hand
    // (tiles no potential rows can be made with)
    List<Tile> testHand = new ArrayList<Tile>();
    testHand.addAll(hand);
    testHand.removeAll(doubleTiles);
    List<Tile> badTiles = getBadTiles(testHand);
    List<Move> result = new ArrayList<Move>();
    
    // Add the double tiles to the swap pile
    for (Tile tile : doubleTiles) {
      result.add(new Move(tile));
    }
    
    // Add the bad tiles to the swap pile
    for (Tile tile : badTiles) {
      result.add(new Move(tile));
    }
    
    if (result.size() == 0) {
      result.add(new Move(hand.get(0)));
    }
    
    return result;
  }

  private List<Tile> getBadTiles(List<Tile> testHand) {
    List<List<Tile>> possibleRows = new ArrayList<List<Tile>>();
    for (Tile tile : testHand) {
      List<Tile> rowWithShapeTheSameTiles = new ArrayList<Tile>();
      List<String> rowWithShapeTheSameColors = new ArrayList<String>();
      rowWithShapeTheSameTiles.add(tile);
      rowWithShapeTheSameColors.add(tile.getColor());
      List<Tile> rowWithColorTheSameTiles = new ArrayList<Tile>();
      List<String> rowWithColorTheSameShapes = new ArrayList<String>();
      rowWithColorTheSameTiles.add(tile);
      rowWithColorTheSameShapes.add(tile.getShape());
      List<Tile> testTestHand = new ArrayList<Tile>();
      testTestHand.addAll(testHand);
      testTestHand.remove(tile);
      for (Tile tile2 : testTestHand) {
        if (tile.getShape().equals(tile2.getShape()) 
            && !rowWithShapeTheSameColors.contains(tile2.getColor())) {
          rowWithShapeTheSameTiles.add(tile2);
          rowWithShapeTheSameColors.add(tile2.getColor());
        }
        if (tile.getColor().equals(tile2.getShape())
            && !rowWithColorTheSameShapes.contains(tile2.getShape())) {
          rowWithColorTheSameTiles.add(tile2);
          rowWithColorTheSameShapes.add(tile2.getShape());
        }
      }
      possibleRows.add(rowWithShapeTheSameTiles);
      possibleRows.add(rowWithColorTheSameTiles);
    }
    List<Tile> badTiles = new ArrayList<Tile>();
    for (Tile tileInHand : testHand) {
      boolean isBadTile = true;
      for (List<Tile> possibleRow : possibleRows) {
        if (possibleRow.size() > 1 && possibleRow.contains(tileInHand)) {
          isBadTile = false;
          break;
        }
      }
      if (isBadTile) {
        badTiles.add(tileInHand);
      }
    }
    return badTiles;
  }

  /**
   * Gets places where a tile can be.
   * @param board the board
   * @return list of places
   */
  private List<List<Integer>> getPossiblePlaces(Board board) {
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
  private HashMap<List<Move>, Integer> getBestTurn(Board board, List<Tile> hand, 
      List<Move> turn, Board reserveBoard) {
    Tile empty = new Tile();
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
          tussenResult = getBestTurn(testBoard, hand, testTurn, reserveBoard);
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
          tussenResult = getBestTurn(testBoard, hand, testTurn, reserveBoard);
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
          tussenResult = getBestTurn(testBoard, hand, testTurn, reserveBoard);
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
          tussenResult = getBestTurn(testBoard, hand, testTurn, reserveBoard);
          Set<List<Move>> tussenResultKeySet = tussenResult.keySet();
          for (List<Move> tussenTurn : tussenResultKeySet) {
            result.put(tussenTurn, tussenResult.get(tussenTurn));
          }
        }
      }
    }
    if (result.size() == 0) {
      int score = board.getScoreCurrentTurn();
      // If this turn is not a smart turn, decrease its points so this turn
      // has a lower priority.
      if (isNotASmartTurn(turn, reserveBoard)) {
        if (score > 9) {
          score = score - 4;
        } else {
          score = score - 2;
        }
      }
      result.put(turn, score);
    } else {
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
      result = new HashMap<List<Move>, Integer>();
      result.put(bestTurn, bestScore);
    }
    return result;
  }

  private boolean isNotASmartTurn(List<Move> selectedTurn, Board reserveBoard) {
    boolean result = false;
    Board board = reserveBoard.deepCopy();
    Tile empty = new Tile();
    for (Move move : selectedTurn) {
      board.putTile(move);
    }
    board.endTurn();
    for (Move move : selectedTurn) {
      // This whole part is to check if this move makes a row of 5
      int column = move.getColumn() + 1;
      List<Tile> horizontalRow = new ArrayList<Tile>();
      horizontalRow.add(move.getTile());
      while (!board.getTile(move.getRow(), column).equals(empty)) {
        horizontalRow.add(board.getTile(move.getRow(), column));
        column++;
      }
      int maxColumnHorizontalRow = column;
      column = move.getColumn() - 1;
      while (!board.getTile(move.getRow(), column).equals(empty)) {
        horizontalRow.add(board.getTile(move.getRow(), column));
        column--;
      }
      int minColumnHorizontalRow = column;
      
      
      int row = move.getRow() + 1;
      List<Tile> verticalRow = new ArrayList<Tile>();
      verticalRow.add(move.getTile());
      while (!board.getTile(row, move.getColumn()).equals(empty)) {
        verticalRow.add(board.getTile(row, move.getColumn()));
        row++;
      }
      int maxRowVerticalRow = row;
      row = move.getRow() - 1;
      while (!board.getTile(row, move.getColumn()).equals(empty)) {
        verticalRow.add(board.getTile(row, move.getColumn()));
        row--;
      }
      int minRowVerticalRow = row;
      // If a row of 5 is actually made, here is checked if the missing
      // tile in that row is already three times on the board.
      // If so then there is nothing to worry about.
      if (horizontalRow.size() == 5) {
        Tile missingTile = getMissingTile(horizontalRow);
        if (!tileIsPlacedThreeTimes(reserveBoard, missingTile)
            && (board.checkMove(new Move(missingTile, move.getRow(), maxColumnHorizontalRow))
                || board.checkMove(new Move(missingTile, move.getRow(), minColumnHorizontalRow)))) {
          result = true;
          break;
        }
      }
      if (verticalRow.size() == 5) {
        Tile missingTile = getMissingTile(verticalRow);
        if (!tileIsPlacedThreeTimes(reserveBoard, missingTile)
            && (board.checkMove(new Move(missingTile, maxRowVerticalRow, move.getColumn()))
                || board.checkMove(new Move(missingTile, minRowVerticalRow, move.getColumn())))) {
          result = true;
          break;
        }
      }
    }
    return result;
  }

  private Tile getMissingTile(List<Tile> row) {
    List<String> shapes = new ArrayList<String>();
    List<String> colors = new ArrayList<String>();
    for (Tile tile : row) {
      shapes.add(tile.getShape());
      colors.add(tile.getColor());
    }
    String missingTileShape = "";
    String missingTileColor = "";
    if (shapes.get(0).equals(shapes.get(1))) {
      missingTileShape = shapes.get(0);
      for (String color : COLOURS) {
        if (!colors.contains(color)) {
          missingTileColor = color;
        }
      }
    } else {
      missingTileColor = colors.get(0);
      for (String shape : SHAPES) {
        if (!shapes.contains(shape)) {
          missingTileShape = shape;
        }
      }
    }
    return new Tile(missingTileColor, missingTileShape);
  }
  
  private boolean tileIsPlacedThreeTimes(Board board, Tile missingTile) {
    int amountTileIsPlaced = 0;
    for (int row = 0; row < 183; row++) {
      for (int column = 0; column < 183; column++) {
        if (board.getTile(row, column).equals(missingTile)) {
          amountTileIsPlaced++;
        }
      }
    }
    return amountTileIsPlaced == 3;
  }
}
