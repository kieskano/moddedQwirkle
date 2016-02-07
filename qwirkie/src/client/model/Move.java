package client.model;

/**
 * Class representing a move.
 * @author Han Hollander
 */
public class Move {
  
  public enum Type { MOVE, SWAP, END, ANY; }
  
  private Type type;
  private Tile tile;
  private int row;
  private int column;
  
  /**
   * Constructor for MOVE move.
   * @param tile Tile which is to be placed.
   * @param row Row where the tile is to be placed.
   * @param column Column where the tile is to be placed.
   */
  public Move(Tile tile, int row, int column) {
    this.type = Type.MOVE;
    this.tile = tile;
    this.row = row;
    this.column = column;
  }
  
  /**
   * Constructor for SWAP move.
   * @param tile The tile that is to be swapped.
   */
  public Move(Tile tile) {
    this.type = Type.SWAP;
    this.tile = tile;
  }
  
  public Move() {
    this.type = Type.END;
  }

  public Tile getTile() {
    return tile;
  }

  public int getRow() {
    return row;
  }

  public int getColumn() {
    return column;
  }
  
  public Type getType() {
    return type;
  }
  
  public String toString() {
    return "[" + tile.toString() + ", " + row + ", " + column + "]";
  }
  
  public String colourToString() {
    return "[" + tile.colourToString() + ", " + row + ", " + column + "]";
  }

  /**
   * Custom equals function to make life easier.
   * @param move The move to compare this to.
   * @return If the moves are equal.
   */
  public boolean equals(Move move) {
    boolean equals = false;
    if (type == Type.MOVE) {
      if (type.equals(move.getType()) && tile.equals(move.getTile()) 
          && column == move.getColumn() && row == move.getRow()) {
        equals = true;
      }
    } else if (type == Type.SWAP) {
      if (type.equals(move.getType()) && tile.equals(move.getTile())) {
        equals = true;
      }
    } else if (type == Type.END) {
      if (type.equals(move.getType())) {
        equals = true;
      }
    }
    return equals;
  }

}
