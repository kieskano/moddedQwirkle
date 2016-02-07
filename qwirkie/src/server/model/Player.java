package server.model;

import java.util.ArrayList;
import java.util.List;

import exceptions.HandIsFullException;
import exceptions.TileNotInHandException;

/**
 * Abstract player class.
 * @author Han Hollander
 */

public class Player {
  
  /*@ invariant getHand().size() >= 0 & getHand().size() < 7;
      invariant (\forall int i; i >= 0 & i < getName().length(); 
                server.controller.ClientHandler.ALLOWEDCHARS.contains(getName().substring(i, i + 1))
                );
      invariant getName().length() > 0 & getName().length() < 17;
      invariant getScore() >= 0;
      invariant getPlayerNumber() > 0 & getPlayerNumber() < 5;
   */
  
  //Fields\\
    
  private String name;
  private int playerNumber;
  private List<Tile> hand;
  private int score;
    
  //Constructor\\
  
  /*@ ensures getName().equals(name);
      ensures getPlayerNumber() == playerNumber;
      ensures getHand().size() == 0;
   */
  /**
   * Constructor for a Player.
   * @param name the name
   * @param playerNumber the number
   */
  public Player(String name, int playerNumber) {
    this.name = name;
    this.playerNumber = playerNumber;
    this.hand = new ArrayList<Tile>();
    score = 0;
  }
    
  //Functions\\
  
  /*@ requires tile != null;
      requires getHand().size() < 6;
      ensures getHand().contains(tile);
   */
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
  
  /*@ requires tile != null;
      requires getHand().contains(tile);
      ensures getHand().size() == \old(getHand().size()) - 1;
   */
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
      throw new TileNotInHandException(new client.model.Tile(tile.getColor(), tile.getShape()));
    }
  }
  
  
    
  //Getters, toString\\
        
  /**
   * Return a string representation of the hand.
   * @return string representation of the hand
   *         " (tile) (tile) (tile) (tile) (tile) (tile)"
   */
  public String handToString() {
    String result = "";
    for (Tile tile : hand) {
      result = result + " " + tile.toString();
    }
    return result;
  }
        
  /**
   * Get the name of the player.
   * @return name
   */
  /*@ pure */ public String getName() {
    return name;
  }
        
  /**
   * Get the hand of the player.
   * @return hand
   */
  /*@ pure */ public List<Tile> getHand() {
    List<Tile> result = new ArrayList<Tile>();
    result.addAll(hand);
    return result;
  }

  /**
   * get number of the player.
   * @return playerNumber
   */
  /*@ pure */ public int getPlayerNumber() {
    return playerNumber;
  }
  
  public String toString() {
    return "Player-" + playerNumber + " " + name;
  }
  
  /*@ pure */ public int getScore() {
    return score;
  }
  
  //@ requires extraPoints > 0;
  //@ ensures getScore() == \old(getScore()) + extraPoints;
  public void addToScore(int extraPoints) {
    score += extraPoints;
  }
    
}
