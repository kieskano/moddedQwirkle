package server.model;

public class Tile {
  
  private String color;
  private String shape;
  
  //@ ensures getColor().equals(".");
  //@ ensures getColor().equals(" ");
  public Tile() {
    color = ".";
    shape = " ";
  }
  
  //@ ensures getColor().equals(color);
  //@ ensures getColor().equals(shape);
  public Tile(String color, String shape) {
    this.color = color;
    this.shape = shape;
  }
  
  /*@ pure*/ public String getColor() {
    return color;
  }
  
  /*@ pure*/ public String getShape() {
    return shape;
  }
  
  /*@ pure*/ public String toString() {
    return color + shape;
  }
  
  /*@ requires tile != null;
      ensures \result == this.getColor().equals(tile.getColor()) 
              & this.getShape().equals(tile.getShape());
   */
  /*@ pure*/ public boolean equals(Tile tile) {
    return (color.equals(tile.getColor()) && shape.equals(tile.getShape()));
  }

}
