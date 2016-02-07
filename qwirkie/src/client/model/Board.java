package client.model;

import java.util.ArrayList;
import java.util.List;

public class Board {
  
  private ArrayList<ArrayList<Tile>> boardMatrix;
  private ArrayList<Move> currentLocalTurn;
  
  /**
   * Board constructor. Constructs a empty board.
   */
  public Board() {
    boardMatrix = new ArrayList<ArrayList<Tile>>();
    for (int row = 0; row < 183; row++) {
      boardMatrix.add(new ArrayList<Tile>());
      for (int column = 0; column < 183; column++) {
        boardMatrix.get(row).add(new Tile());
      }
    }
    currentLocalTurn = new ArrayList<Move>();
  }
  
  /**
   * Executes the given move on the board.
   * @param move The move you want to apply to the board.
   */
  public void putTile(Move move) {
    int row = move.getRow();
    int column = move.getColumn();
    boardMatrix.get(row).set(column, move.getTile());
    currentLocalTurn.add(move);
  }
  
  /**
   * Ends the current turn by removing all the moves from
   * the array of moves of the current (now previous) turn.
   */
  public void endTurn() {
    currentLocalTurn = new ArrayList<Move>();
  }
  
  /**
   * Undoes the given move.
   * @param move The move that needs to be undone.
   */
  public void undoMove(Move move) {
    Tile empty = new Tile();
    int row = move.getRow();
    int column = move.getColumn();
    if (!getTile(move.getRow(), move.getColumn()).equals(empty)) {
      boardMatrix.get(row).set(column, empty);
    }
  }
  
  /**
   * Undoes every move of the current turn.
   */
  public void resetTurn() {
    for (Move move : currentLocalTurn) {
      undoMove(move);
    }
    currentLocalTurn = new ArrayList<Move>();
  }
  
  /**
   * Creates a new board and copies the contents of the current board to the new board.
   * @return A copy of board.
   */
  public Board deepCopy() {
    Board result = new Board();
    for (int row = 0; row < 183; row++) {
      for (int column = 0; column < 183; column++) {
        result.boardMatrix.get(row).set(column, this.boardMatrix.get(row).get(column));
      }
    }
    result.currentLocalTurn.addAll(this.currentLocalTurn);
    return result;
  }
  
  /**
   * Returns a string representation of the board.
   */
  public String toString() {
    String result = "";
    ArrayList<ArrayList<Integer>> marges = getMargins();
    int columnMin = marges.get(1).get(0);
    int columnMax = marges.get(1).get(1);
    result = "XXX ";
    // This part creates the top row of column numbers
    for (int column = columnMin; column <= columnMax; column++) { 
      if (column > 99) {
        result = result + (column) + " ";
      } else if (column > 9) {
        result = result + (column) + "  ";
      } else {
        result = result + (column) + "   ";
      }
    }
    result = result + "\n";
    // This part creates the rest
    int rowMin = marges.get(0).get(0);
    int rowMax = marges.get(0).get(1);
    for (int row = rowMin; row <= rowMax; row++) {
      if (row > 99) {
        result = result + (row) + " ";
      } else if (row > 9) {
        result = result + (row) + "  ";
      } else {
        result = result + (row) + "   ";
      }
      for (int column = columnMin; column <= columnMax; column++) {
        result = result + boardMatrix.get(row).get(column).colourToString() + "   ";
      }
      result = result + "\n" + "\n";
    }
    return result;
  }
  
  public String toString(int pointerRow, int pointerColumn) {
    String result = "";
    ArrayList<ArrayList<Integer>> marges = getMargins();
    int columnMin = marges.get(1).get(0);
    int columnMax = marges.get(1).get(1);
    int rowMin = marges.get(0).get(0);
    int rowMax = marges.get(0).get(1);
    result = "XXX ";
    // This part creates the top row of column numbers
    for (int column = columnMin; column <= columnMax; column++) { 
      if (column > 99) {
        result = result + (column) + " ";
      } else if (column > 9) {
        result = result + (column) + "  ";
      } else {
        result = result + (column) + "   ";
      }
    }
    result = result + "\n" + "   ";
    if (pointerRow == rowMin) {
      int theCol = pointerColumn - columnMin;
      for (int i = 0; i < theCol; i++) {
        result = result + "    ";
      }
      result = result + "+--+";
    }
    result = result + "\n";
    // This part creates the rest
    for (int row = rowMin; row <= rowMax; row++) {
      if (row > 99) {
        result = result + (row) + "";
      } else if (row > 9) {
        result = result + (row) + " ";
      } else {
        result = result + (row) + "  ";
      }
      for (int column = columnMin; column <= columnMax; column++) {
        if (row == pointerRow && column == columnMin && column == pointerColumn) {
          result = result + "|" + boardMatrix.get(row).get(column).colourToString() + " | ";
        } else if (row == pointerRow && column == columnMin && column == pointerColumn - 1) {
          result = result + " " + boardMatrix.get(row).get(column).colourToString() + "  |";
        } else if (row == pointerRow && column == pointerColumn - 1){
          result = result + boardMatrix.get(row).get(column).colourToString() + "  |";
        } else if (row == pointerRow && column == pointerColumn) {
          result = result + boardMatrix.get(row).get(column).colourToString() + " | ";
        } else if (column == columnMin) {
          result = result + " " + boardMatrix.get(row).get(column).colourToString() + "   ";
        } else {
          result = result + boardMatrix.get(row).get(column).colourToString() + "   ";
        }
        
      }
      result = result + "\n" + "   ";
      if (row == pointerRow || row == pointerRow - 1) {
        int theCol = pointerColumn - columnMin;
        for (int i = 0; i < theCol; i++) {
          result = result + "    ";
        }
        result = result + "+--+";
      }
      result = result + "\n";
    }
    return result;
  }
  /**
   * Checks if the current move is a correct move according to the game rules.
   * @param move The move that needs to be checked.
   * @return True or false whether the move is a correct move or not.
   */
  /*@ pure */ public boolean checkMove(Move move) {
    boolean gotVerticalRow;
    boolean gotHorizontalRow;
    Tile empty = new Tile();
    boolean result = true;
    // Check if the destination of the move is empty on the board
    if (getTile(move.getRow(), move.getColumn()).equals(empty)) {
      // Check if the current move and the moves made this turn are in the same row
      if (currentMovesLineUp(move)) {
        // Check if the current move creates a vertical row and/or horizontal row.
        gotVerticalRow = !getTile(move.getRow() - 1, move.getColumn()).equals(empty) 
            || !getTile(move.getRow() + 1, move.getColumn()).equals(empty);
        gotHorizontalRow = !getTile(move.getRow(), move.getColumn() - 1).equals(empty) 
            || !getTile(move.getRow(), move.getColumn() + 1).equals(empty);
        
        if (gotHorizontalRow) {
          // Check if the current move fits in the horizontal row.
          ArrayList<String> adjesentHorizontalTilesShapes = new ArrayList<String>();
          ArrayList<String> adjesentHorizontalTilesColors = new ArrayList<String>();
          int row = move.getRow();
          int column = move.getColumn() + 1;
          // Add the adjesent tiles right of the placed tile to the horizontal row list
          while (!getTile(row, column).equals(empty)) {
            adjesentHorizontalTilesShapes.add(getTile(row, column).getShape());
            adjesentHorizontalTilesColors.add(getTile(row, column).getColor());
            column++;
          }
          // Add the adjesent tiles left of the placed tile to the horizontal row list
          column = move.getColumn() - 1;
          while (!getTile(row, column).equals(empty)) {
            adjesentHorizontalTilesShapes.add(getTile(row, column).getShape());
            adjesentHorizontalTilesColors.add(getTile(row, column).getColor());
            column--;
          }
          // Check if the row with the placed tile has all the shapes the same
          // and colors different.
          boolean shapesAreTheSame = true;
          String templateShape = move.getTile().getShape();
          for (String shape : adjesentHorizontalTilesShapes) {
            shapesAreTheSame = shapesAreTheSame && shape.equals(templateShape);
          }
          shapesAreTheSame = shapesAreTheSame 
              && !adjesentHorizontalTilesColors.contains(move.getTile().getColor());
          
          // Check if the row with the placed tile has all the colors the same
          // and shapes different.
          boolean colorsAreTheSame = true;
          String templateColor = move.getTile().getColor();
          for (String color : adjesentHorizontalTilesColors) {
            colorsAreTheSame = colorsAreTheSame && color.equals(templateColor);
          }
          colorsAreTheSame = colorsAreTheSame 
              && !adjesentHorizontalTilesShapes.contains(move.getTile().getShape());
          
          // Final check which checks if the placed tile connects two rows
          // (which already existed) which are not allowed to be connected.
          boolean moveConnectsInvalidRows = false;
          if (shapesAreTheSame) {
            List<String> testList = new ArrayList<String>();
            for (String color : adjesentHorizontalTilesColors) {
              if (testList.contains(color)) {
                moveConnectsInvalidRows = true;
                break;
              }
              testList.add(color);
            }
          } else if (colorsAreTheSame) {
            List<String> testList = new ArrayList<String>();
            for (String shape : adjesentHorizontalTilesShapes) {
              if (testList.contains(shape)) {
                moveConnectsInvalidRows = true;
                break;
              }
              testList.add(shape);
            }
          }
          result = ((shapesAreTheSame || colorsAreTheSame) && !moveConnectsInvalidRows);
        }
        
        if (gotVerticalRow && result) {
          // Check if the current move fits in the vertical row.
          ArrayList<String> adjesentVerticalTilesShapes = new ArrayList<String>();
          ArrayList<String> adjesentVerticalTilesColors = new ArrayList<String>();
          int row = move.getRow() + 1;
          int column = move.getColumn();
          // Add the adjesent tiles below the placed tile to the vertical row list
          while (!getTile(row, column).equals(empty)) {
            adjesentVerticalTilesShapes.add(getTile(row, column).getShape());
            adjesentVerticalTilesColors.add(getTile(row, column).getColor());
            row++;
          }
          // Add the adjesent tiles above the placed tile to the vertical row list
          row = move.getRow() - 1;
          while (!getTile(row, column).equals(empty)) {
            adjesentVerticalTilesShapes.add(getTile(row, column).getShape());
            adjesentVerticalTilesColors.add(getTile(row, column).getColor());
            row--;
          }
          // Check if the row with the placed tile has all the shapes the same
          // and colors different.
          boolean shapesAreTheSame = true;
          String templateShape = move.getTile().getShape();
          for (String shape : adjesentVerticalTilesShapes) {
            shapesAreTheSame = shapesAreTheSame && shape.equals(templateShape);
          }
          shapesAreTheSame = shapesAreTheSame 
              && !adjesentVerticalTilesColors.contains(move.getTile().getColor());
          // Check if the row with the placed tile has all the colors the same
          // and shapes different.
          boolean colorsAreTheSame = true;
          String templateColor = move.getTile().getColor();
          for (String color : adjesentVerticalTilesColors) {
            colorsAreTheSame = colorsAreTheSame && color.equals(templateColor);
          }
          colorsAreTheSame = colorsAreTheSame 
              && !adjesentVerticalTilesShapes.contains(move.getTile().getShape());
          // Final check which checks if the placed tile connects two rows
          // (which already existed) which are not allowed to be connected.
          boolean moveConnectsInvalidRows = false;
          if (shapesAreTheSame) {
            List<String> testList = new ArrayList<String>();
            for (String color : adjesentVerticalTilesColors) {
              if (testList.contains(color)) {
                moveConnectsInvalidRows = true;
                break;
              }
              testList.add(color);
            }
          } else if (colorsAreTheSame) {
            List<String> testList = new ArrayList<String>();
            for (String shape : adjesentVerticalTilesShapes) {
              if (testList.contains(shape)) {
                moveConnectsInvalidRows = true;
                break;
              }
              testList.add(shape);
            }
          }
          result = ((shapesAreTheSame || colorsAreTheSame) && !moveConnectsInvalidRows);
        }
        
        // Here it checks when the current move has no tiles next to it if this move
        // is in the middle of the board.
        if (!gotHorizontalRow && !gotVerticalRow) {
          result = move.getRow() == 91 && move.getColumn() == 91;
        }
      } else {
        result = false;
      }
    } else {
      result = false;
    }
    return result;
  }
  
  /**
   * Checks if all the done moves this turn and the given
   * move line up in the same row or column.
   * @param move The move that is added this turn.
   * @return True or False whether the moves line up or not.
   */
  public boolean currentMovesLineUp(Move move) {
    boolean result = false;
    if (!currentLocalTurn.isEmpty()) {
      boolean horizontalLineUp = true;
      Move previousMove = move;
      int lowestColumn = move.getColumn();
      int highestColumn = move.getColumn();
      // Check if all done moves and current move are on the same row.
      for (Move doneMove : currentLocalTurn) {
        horizontalLineUp = horizontalLineUp && previousMove.getRow() == doneMove.getRow();
        previousMove = doneMove;
        if (doneMove.getColumn() < lowestColumn) {
          lowestColumn = doneMove.getColumn();
        } else if (doneMove.getColumn() > highestColumn) {
          highestColumn = doneMove.getColumn();
        }
      }
      if (horizontalLineUp) {
        result = highestColumn - lowestColumn == currentLocalTurn.size();
      } else {
        boolean verticalLineUp = true;
        previousMove = move;
        int lowestRow = move.getRow();
        int highestRow = move.getRow();
        // Check if all done moves and current move are on the same column.
        for (Move doneMove : currentLocalTurn) {
          verticalLineUp = verticalLineUp && previousMove.getColumn() == doneMove.getColumn();
          previousMove = doneMove;
          if (doneMove.getRow() < lowestRow) {
            lowestRow = doneMove.getRow();
          } else if (doneMove.getRow() > highestRow) {
            highestRow = doneMove.getRow();
          }
        }
        if (verticalLineUp) {
          result = highestRow - lowestRow == currentLocalTurn.size();
        }
      }
    } else {
      result = true;
    }
    return result;
  }
  
  /**
   * Returns the Tile located at the given row and column.
   * @param row A row number of the board.
   * @param column A column number of the board.
   * @return the Tile located at the given row and column.
   */
  public Tile getTile(int row, int column) {
    return boardMatrix.get(row).get(column);
  }

  /**
   * Calculates the part of the board where there are tiles.
   * @return A list with 2 tupels, in the first: the min and 
   *         max row margin, in the second: the min and max 
   *         column margin.
   */
  public ArrayList<ArrayList<Integer>> getMargins() {
    ArrayList<ArrayList<Integer>> result = new ArrayList<ArrayList<Integer>>();
    result.add(new ArrayList<Integer>());
    result.add(new ArrayList<Integer>());
    // the result will be like [[rowMin, rowMax], [columnMin, columnMax]]
    int row = 0;
    int column = 0;
    int rowMin = 0;
    int columnMin = 0;
    int columnMax = 0;
    String empty = ". ";
    
    //Get the start row
    while (row < 182 && boardMatrix.get(row).get(column).toString().equals(empty)) { 
      if (column < 182) {
        column++;
      } else {
        column = 0;
        row++;
      }
    }
    
    rowMin = row - 1;
    
    row = 182;
    column = 0;
    //Get the end row
    while (row > 0 && boardMatrix.get(row).get(column).toString().equals(empty)) { 
      if (column > 0) {
        column--;
      } else {
        column = 182;
        row--;
      }
    }
    //For checkstyle purposes it is placed here, not by the others...
    int rowMax = 0;
    
    rowMax = row + 1;
    
    // rowMin < rowMax == true when there are no tiles placed on the board.
    if (rowMin < rowMax) {
      row = 0;
      column = 0;
      //Get the start column
      while (column < 182 && boardMatrix.get(row).get(column).toString().equals(empty)) { 
        if (row < 182) {
          row++;
        } else {
          row = 0;
          column++;
        }
      }
      columnMin = column - 1;
      
      row = 0;
      column = 182;
      //Get the end row
      while (column > 0 && boardMatrix.get(row).get(column).toString().equals(empty)) { 
        if (row > 0) {
          row--;
        } else {
          row = 182;
          column--;
        }
      }
      columnMax = column + 1;
    } else {
      result.get(0).add(90);
      result.get(0).add(92);
      result.get(1).add(90);
      result.get(1).add(92);
    }
    if (result.get(0).size() == 0) {
      result.get(0).add(rowMin);
      result.get(0).add(rowMax);
      result.get(1).add(columnMin);
      result.get(1).add(columnMax);
    }
    
    return result;
  }

  /**
   * Calculates the amount of points that are earned with
   * the current turn.
   * @return The calculated the amount of points that are 
   *         earned with the current turn.
   */
  public int getScoreCurrentTurn() {
    Tile empty = new Tile();
    int verticalResult = 0;
    int horizontalResult = 0;
    for (Move move : currentLocalTurn) {
      boolean gotVerticalRow;
      boolean gotHorizontalRow;
      // Check in which directions the move has rows.
      gotVerticalRow = !getTile(move.getRow() - 1, move.getColumn()).equals(empty) 
          || !getTile(move.getRow() + 1, move.getColumn()).equals(empty);
      gotHorizontalRow = !getTile(move.getRow(), move.getColumn() - 1).equals(empty) 
          || !getTile(move.getRow(), move.getColumn() + 1).equals(empty);
      int verticalPoints = 0;
      int horizontalPoints = 0;
      if (gotVerticalRow) {
        int row = move.getRow() + 1;
        int column = move.getColumn();
        verticalPoints++;
        // Add points while the space above the current tile is not empty
        while (!getTile(row, column).equals(empty)) {
          verticalPoints++;
          row++;
        }
        row = move.getRow() - 1;
        // Add points while the space below the current tile is not empty
        while (!getTile(row, column).equals(empty)) {
          verticalPoints++;
          row--;
        }
        // If row of 6 is made, add 6 bonus points.
        if (verticalPoints == 6) {
          verticalPoints += 6;
        }
      }
      if (gotHorizontalRow) {
        int row = move.getRow();
        int column = move.getColumn() + 1;
        horizontalPoints++;
        // Add points while the space to the right of the current tile is not empty
        while (!getTile(row, column).equals(empty)) {
          horizontalPoints++;
          column++;
        }
        column = move.getColumn() - 1;
        // Add points while the space to the left of the current tile is not empty
        while (!getTile(row, column).equals(empty)) {
          horizontalPoints++;
          column--;
        }
        // If row of 6 is made, add 6 bonus points.
        if (horizontalPoints == 6) {
          horizontalPoints += 6;
        }
      }
      horizontalResult += horizontalPoints;
      verticalResult += verticalPoints;
      // !gotHorizontalRow && !gotVerticalRow == true only when in the first move on the board
      // one tile is placed. This is always worth 1 point.
      if (!gotHorizontalRow && !gotVerticalRow) {
        horizontalResult = 1;
      }
    }
    // Here is checked whether the placed tiles this turn are placed horizontally or not.
    boolean horizontalLineUp = true;
    Move previousMove = currentLocalTurn.get(0);
    for (Move doneMove : currentLocalTurn) {
      horizontalLineUp = horizontalLineUp && previousMove.getRow() == doneMove.getRow();
      previousMove = doneMove;
    }
    if (currentLocalTurn.size() > 1) {
      // Get rid of points that are counted too many times.
      if (horizontalLineUp) {
        horizontalResult = horizontalResult / currentLocalTurn.size();
      } else {
        verticalResult = verticalResult / currentLocalTurn.size();
      }
    }
    
    return horizontalResult + verticalResult;
  }
  
  public List<Move> getMoveList() {
    return currentLocalTurn;
  }
  
  /**
   * Checks if this board is the same as the given board.
   * @param board That needs to be compared.
   * @return True or False whether the boards are equal or not.
   */
  public boolean equals(Board board) {
    boolean result = true;
    for (int row = 0; row < 183; row++) {
      for (int column = 0; column < 183; column++) {
        if (!boardMatrix.get(row).get(column).equals(board.getTile(row, column))) {
          result = false;
          break;
        }
      }
      if (!result) {
        break;
      }
    }
    return result;
  }
  
  public static void main(String[] args) {
    Board b = new Board();
    System.out.println(b.toString(92, 92));
  }
}
