package server.model;

public class Move {
  
  public enum Type { MOVE, SWAP, END, ANY; }
  
  /*@ invariant getType() == Type.MOVE || getType() == Type.SWAP 
                || getType() == Type.END || getType() == Type.ANY;
      invariant getRow() >= 0 & getRow() < 183;
      invariant getColumn() >= 0 & getColumn() < 183;
   */
  
  private Type type;
  private Tile tile;
  private int row;
  private int column;
  
  /*@ requires tile != null;
      requires row >= 0 & row < 183;
      requires column >= 0 & column < 183;
      ensures getTile().equals(tile);
      ensures getRow() == row;
      ensures getColumn() == column;
      ensures getType() == Type.MOVE;
   */
  /**
   * Constructor for MOVE move.
   * @param tile Tile
   * @param row Row on the board
   * @param column Column on the board
   */
  public Move(Tile tile, int row, int column) {
    this.type = Type.MOVE;
    this.tile = tile;
    this.row = row;
    this.column = column;
  }
  
  /*@ requires tile != null;
      ensures getTile().equals(tile);
      ensures getType() == Type.SWAP;
   */
  /**
   * Constructor for SWAP move.
   * @param colour colour of tile
   * @param shape shape of tile
   */
  public Move(Tile tile) {
    this.type = Type.SWAP;
    this.tile = tile;
  }
  
  /*@ requires type != null;
      ensures getType() == type;
   */
  public Move(Type type) {
    this.type = type;
  }

  /*@ pure*/ public Tile getTile() {
    return tile;
  }

  /*@ pure*/ public int getRow() {
    return row;
  }

  /*@ pure*/ public int getColumn() {
    return column;
  }
  
  /*@ pure*/ public Type getType() {
    return type;
  }
  
  public String toString() {
    return getTile().toString() + " " + getRow() + " " + getColumn();
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
