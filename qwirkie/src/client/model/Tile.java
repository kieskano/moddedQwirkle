package client.model;

/**
 * Simple representation of a tile.
 * @author Wijtse Rekker
 */
public class Tile {
  
  private String color;
  private String shape;
  
  public static final String ANSI_RESET = "\u001B[0m";
  public static final String ANSI_RED = "\u001B[31m";   //R
  public static final String ANSI_GREEN = "\u001B[32m"; //G
  public static final String ANSI_YELLOW = "\u001B[33m";  //Y
  public static final String ANSI_WHITE = "\u001B[37m"; //B
  public static final String ANSI_PURPLE = "\u001B[35m"; //P
  public static final String ANSI_CYAN = "\u001B[36m"; //O
  
  public Tile() {
    color = ".";
    shape = " ";
  }
  
  public Tile(String color, String shape) {
    this.color = color;
    this.shape = shape;
  }
  
  public String getColor() {
    return color;
  }
  
  public String getShape() {
    return shape;
  }
  
  public String toString() {
    return color + shape;
  }
  
  /**
   * Custom equals function to make life easier.
   * @param tile The tile to compare this to.
   * @return If the tiles match.
   */
  public boolean equals(Tile tile) {
    return (color.equals(tile.getColor()) && shape.equals(tile.getShape()));
  }
  
  /**
   * Coloured letters!
   * @return letter in colour.
   */
  // o d s c x *
  public String colourToString() {
    String letter = "";
    if (shape.equals("o")) { 
      letter = "A"; 
    } else if (shape.equals("d")) { 
      letter = "B"; 
    } else if (shape.equals("s")) { 
      letter = "C"; 
    } else if (shape.equals("c")) { 
      letter = "D"; 
    } else if (shape.equals("x")) { 
      letter = "E"; 
    } else if (shape.equals("*")) { 
      letter = "F"; 
    } else { 
      letter = "."; 
    }
    String result = "";
    if (color.equals("R")) {
      result = ANSI_RED + letter + ANSI_RESET;
    } else if (color.equals("G")) {
      result = ANSI_GREEN + letter + ANSI_RESET;
    } else if (color.equals("B")) {
      result = ANSI_WHITE + letter + ANSI_RESET;
    } else if (color.equals("P")) {
      result = ANSI_PURPLE + letter + ANSI_RESET;
    } else if (color.equals("Y")) {
      result = ANSI_CYAN + letter + ANSI_RESET;
    } else if (color.equals("O")) {
      result = ANSI_YELLOW + letter + ANSI_RESET;
    } else { 
      result = letter; 
    }
    return result;
  }
  
  
  
  
  
  
  
  
  
  
  
  
  

}
