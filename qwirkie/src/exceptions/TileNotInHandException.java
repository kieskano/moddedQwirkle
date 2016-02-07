package exceptions;

import client.model.Tile;

@SuppressWarnings("serial")
public class TileNotInHandException extends Exception {
  
  public TileNotInHandException(Tile tile) {
    super("Tile [" + tile.toString() + "] is not in your hand.");
  }

}
