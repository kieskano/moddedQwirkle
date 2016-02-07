package client.model;

import exceptions.HandIsFullException;
import exceptions.InvalidMoveException;
import exceptions.TileNotInHandException;

import java.util.ArrayList;
import java.util.List;

/**
 * Class representing a player.
 * @author Han Hollander
 */
public abstract class Player {
    
  private String name;
  private int playerNumber;
  private List<Tile> hand;
  private List<Move> moves;
  private int score;
  private boolean madeMove;
        
  /**
   * Constructor for a Player.
   * @param name the name
   * @param playerNumber the number
   */
  public Player(String name, int playerNumber) {
    this.name = name;
    this.playerNumber = playerNumber;
    this.hand = new ArrayList<Tile>();
    this.setMoves(new ArrayList<Move>());
  }

  /**
   * Function that determines what move is played next.
   * @throws InvalidMoveException invalid move
   */
  public abstract Move determineMove(Board board) throws InvalidMoveException;
  
  /**
   * Add a tile to a hand.
   * @param tile the tile to add
   * @throws HandIsFullException if hand is full
   */
  public void addToHand(Tile tile) throws HandIsFullException {
    if (hand.size() < 6) {
      hand.add(tile);
    } else {
      throw new HandIsFullException();
    }
  }
  
  /**
   * Remove tile from hand.
   * @param tile tile to remove
   * @throws TileNotInHandException tile is not in hand
   */
  public void removeFromHand(Tile tile) throws TileNotInHandException {
    boolean contains = false;
    Tile remove = null;
    for (Tile check : hand) {
      if (check.toString().equals(tile.toString())) {
        remove = check;
        contains = true;
      }
    }
    if (contains) {
      hand.remove(remove);
    } else {
      throw new TileNotInHandException(tile);
    }
  }
  
  public String getName() {
    return name;
  }
  
  public List<Tile> getHand() {
    return hand;
  }
  
  /**
   * Returns a nice list with colour.
   * @return nice list
   */
  public String handToString() {
    String result = "";
    for (int i = 0; i < hand.size(); i++) {
      result = result + " " + hand.get(i).colourToString() + "  ";
    }
    return result;
  }
  
  public String handToString(int position) {
    String result = "";
    for (int i = 0; i <= position && position < hand.size(); i++) {
      if (i == position) {
        result = result + "+--+";
      } else {
        result = result + "    ";
      }
    }
    if (position == hand.size()) {
      for (int i = 0; i < position; i++) {
        result = result + "    ";
      }
      result = result + "+---+";
    }
    result = result + "\n";
    for (int i = 0; i < hand.size(); i++) {
      if (i == position) {
        result = result + "|" + hand.get(i).colourToString() + " |";
      } else {
        result = result + " " + hand.get(i).colourToString() + "  ";
      }
    }
    if (position == hand.size()) {
      result = result + "|END|\n";
    } else {
      result = result + " END \n";
    }
    for (int i = 0; i <= position && position < hand.size(); i++) {
      if (i == position) {
        result = result + "+--+";
      } else {
        result = result + "    ";
      }
    }
    if (position == hand.size()) {
      for (int i = 0; i < position; i++) {
        result = result + "    ";
      }
      result = result + "+---+";
    }
    return result;
  }
    
  public int getPlayerNumber() {
    return playerNumber;
  }
  
  public String toString() {
    return "Player " + playerNumber + ": " + name;
  }

  public List<Move> getMoves() {
    return moves;
  }

  public void setMoves(List<Move> moves) {
    this.moves = moves;
  }

  public int getScore() {
    return score;
  }

  public void setScore(int score) {
    this.score = score;
  }

  public boolean isMadeMove() {
    return madeMove;
  }

  public void setMadeMove(boolean madeMove) {
    this.madeMove = madeMove;
  }
}
