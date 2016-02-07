package server.model;

import exceptions.HandIsFullException;
import exceptions.TileNotInHandException;
import server.controller.Server;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.List;
import java.util.Observable;
import java.util.Set;

public class Game extends Observable{
  
  //Fields\\
  
  public static final List<String> COLOURS = Arrays.asList("R", "O", "B", "Y", "G", "P");
  public static final List<String> SHAPES = Arrays.asList("o", "d", "s", "c", "x", "*");
  public static final int DIM = 183;
  
  /*@ invariant getPoolSize() >= 0 & getPoolSize() <= 108;
      invariant getWinningPlayerNr() > 0 & getWinningPlayerNr() < 5;
      invariant getCurrentPlayer() > 0 & getCurrentPlayer() < 5;
      invariant getPlayerNrs().size() >= 0 & getPlayerNrs().size() < 5;
   */
  
  private /*@ spec_public */ Board board;
  private /*@ spec_public */ HashMap<Integer, Player> playerList;
  private /*@ spec_public */ int currentPlayer;
  private /*@ spec_public */ ArrayList<Tile> pool;
  private /*@ spec_public */ Server server;
  
  //Constructor\\
  /*@ requires server != null;
      ensures getServer() == server;
      ensures getPlayerNrs() != null;
      ensures getPlayerNrs().size() == 0;
      ensures getCurrentPlayer() == 0;
      ensures getPoolSize() == 108;
   */
  /**
   * The Constructor of a game.
   * @param server The server through which the game can communicate with the players.
   */
  public Game(Server server) {
    addObserver(server.getObserver());
    this.server = server;
    board = new Board();
    playerList = new HashMap<Integer, Player>();
    currentPlayer = 0;
    pool = new ArrayList<Tile>();
    
    for (int i = 0; i < 3; i++) {
      for (String color : COLOURS) {
        for (String shape : SHAPES) {
          pool.add(new Tile(color, shape));
        }
      }
    }
  }
  
  /*@ requires checkSwapTurn(turn, player);
      ensures \old(getPoolSize()) >= turn.size() ==> player.getHand().size() == 6;
      ensures \old(getPoolSize()) < turn.size() ==> player.getHand().size() 
              == \old(player.getHand().size()) - turn.size() + \old(getPoolSize()); 
   */
  /**
   * Applies the given turn to the pool and sends it to all the players.
   * @param player The player that made the turn.
   * @param turn The turn that needs to be applied.
   */
  public void applySwapTurn(List<Tile> turn, Player player) {
    List<Tile> newTiles = new ArrayList<Tile>();
    for (Tile tile : turn) {
      // Remove the tile from the hand of the player
      try {
        player.removeFromHand(tile);
      } catch (TileNotInHandException e) {
        System.out.println(e);
      }
      // Swap the tile with a random tile of the pool
      // and put the received tile in the hand of the player.
      try {
        Tile newTile = swapTileWithPool(tile);
        player.addToHand(newTile);
        newTiles.add(newTile);
      } catch (HandIsFullException e) {
        System.out.println(e);
      }
    }
    setChanged();
    notifyObservers("turn made");
    server.giveTiles(player.getPlayerNumber(), newTiles);
    server.broadcast("TURN " + player.getPlayerNumber() + " empty");
  }
  
  /*@ requires checkMoveTurn(turn, player);
      ensures \old(getPoolSize()) >= turn.size() ==> player.getHand().size() == 6;
      ensures \old(getPoolSize()) < turn.size() ==> player.getHand().size() 
              == \old(player.getHand().size()) - turn.size() + \old(getPoolSize());
      ensures (\forall Move move; turn.contains(move); 
              getBoard().getTile(move.getRow(), move.getColumn()).equals(move.getTile())); 
   */
  /**
   * Applies the given turn to the board and sends it to all the players.
   * @param player The player that made the turn.
   * @param turn The turn that needs to be applied.
   */
  public void applyMoveTurn(Player player, List<Move> turn) {
    //Put tiles on the board
    for (int i = 0; i < turn.size(); i++) {
      Move move = turn.get(i);
      board.putTile(move);
      try {
        player.removeFromHand(move.getTile());
      } catch (TileNotInHandException e) {
        System.out.println("Tried to remove tile [" + move.getTile().toString() + "]"
            + " from the hand of (" + player.toString() + ")"
            + " but the tile was not in his/her hand.");
      }
    }
    //Get tiles from the pool
    List<Tile> tilesBack = new ArrayList<Tile>();
    for (int i = 0; i < turn.size() && pool.size() > 0; i++) {
      Tile tile = drawRandomTileFromPool();
      try {
        player.addToHand(tile);
      } catch (HandIsFullException e) {
        System.out.println(e);
      }
      tilesBack.add(tile);
    }
    
    server.giveTiles(player.getPlayerNumber(), tilesBack);
    server.sendTurn(player.getPlayerNumber(), turn);
    int score = board.getScoreCurrentTurn();
    player.addToScore(score);
    getServer().getObserver().print("Player-" + player.getPlayerNumber() 
        + " gained " + score + " points!");
    board.endTurn();
    
    setChanged();
    notifyObservers("turn made");
  }
  
  /*@ requires turn != null;
      requires player != null;
      ensures (\forall Tile tile; turn.contains(tile); 
              !player.getHand().contains(tile) ==> \result == false); 
   */
  /**
   * Checks if the tiles that the given player wants to swap
   * are all in the current hand of the player.
   * @param turn The tiles that needs to be checked.
   * @param player The player who made/suggested the turn.
   * @return True of False whether the turn is valid or not.
   */
  /*@ pure */ public boolean checkSwapTurn(List<Tile> turn , Player player) {
    boolean result = true;
    // Check if there are enough tiles in the pool to swap with.
    if (getPoolSize() >= turn.size()) {
      List<Tile> hand = player.getHand();
      for (Tile tile : turn) {
        // Check if the hand actually contains the tile.
        boolean containsTile = false;
        for (Tile tileInHand : hand) {
          containsTile = tile.equals(tileInHand);
          if (containsTile) {
            hand.remove(tileInHand);
            break;
          }
        }
        result = result && containsTile;
      }
    } else {
      result = false;
    }
    return result;
  }
  
  /*@ requires turn != null;
      requires player != null;
      ensures (\forall Move move; turn.contains(move); 
              !player.getHand().contains(move.getTile()) ==> \result == false); 
   */
  /**
   * Checks if the turn is valid according to the Qwirkle rules.
   * @param turn The turn that needs to be checked.
   * @param player The player who made/suggested the turn.
   * @return True of False whether the turn is valid or not.
   */
  /*@ pure */ public boolean checkMoveTurn(List<Move> turn, Player player) {
    Boolean result = true;
    Board testBoard = board.deepCopy();
    List<Tile> hand = player.getHand();
    for (int i = 0; i < turn.size(); i++) {
      Move move = turn.get(i);
      Tile tile = move.getTile();
      // Check if the hand of the player actually contains the tile.
      boolean containsTile = false;
      for (Tile tileInHand : hand) {
        containsTile = tile.equals(tileInHand);
        if (containsTile) {
          hand.remove(tileInHand);
          break;
        }
      }
      if (!containsTile) {
        result = false;
        break;
      }
      // Check if the move is a valid move on the board
      result = result && testBoard.checkMove(move);
      if (result) {
        testBoard.putTile(move);
      } else {
        break;
      }
    }
    return result;
  }
  
  /*@ requires getPlayer(playerNr) != null;
      ensures (\forall List<Integer> coordinate; getPossiblePlaces(getBoard()).contains(coordinate);
              (\forall Tile tile; getPlayer(playerNr).getHand().contains(tile); 
              getBoard().checkMove(new Move(tile, coordinate.get(0), coordinate.get(1))) 
              & getPoolSize() == 0 ==> \result == true));
   */
  /**
   * Checks if the given player can make a move.
   * @param playerNr The number of the player that needs to be checked.
   * @return True of False whether the player can make a move or not.
   */
  public boolean movePossible(int playerNr) {
    boolean result = false;
    if (getPoolSize() == 0) {
      List<List<Integer>> places = getPossiblePlaces(board);
      List<Tile> hand = getPlayer(playerNr).getHand();
      for (Tile tile : hand) {
        for (List<Integer> place : places) {
          Move newMove = new Move(tile, place.get(0), place.get(1));
          if (board.checkMove(newMove)) {
            result = true;
            break;
          }
        }
      }
    } else {
      result = true;
    }
    return result;
  }
  
  /*@ requires board != null;
      ensures (\forall int i, j; i >= 0 & j >= 0 & i < 183 & j < 183;
              !board.getTile(i, j).toString().equals(". ") & 
              board.getTile(i, j + 1).toString().equals(". ")
              ==> \result.contains(Arrays.asList(i, j + 1)));
      ensures (\forall int i, j; i >= 0 & j >= 0 & i < 183 & j < 183;
              !board.getTile(i, j).toString().equals(". ") & 
              board.getTile(i, j - 1).toString().equals(". ")
              ==> \result.contains(Arrays.asList(i, j - 1)));
      ensures (\forall int i, j; i >= 0 & j >= 0 & i < 183 & j < 183;
              !board.getTile(i, j).toString().equals(". ") & 
              board.getTile(i + 1, j).toString().equals(". ")
              ==> \result.contains(Arrays.asList(i + 1, j)));
      ensures (\forall int i, j; i >= 0 & j >= 0 & i < 183 & j < 183;
              !board.getTile(i, j).toString().equals(". ") & 
              board.getTile(i - 1, j).toString().equals(". ")
              ==> \result.contains(Arrays.asList(i - 1, j)));
   */
  /**
   * Gets places where a tile can be.
   * @param board The board.
   * @return A list of free places.
   */
  /*@ pure */public List<List<Integer>> getPossiblePlaces(Board board) {
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
  
  /*@ requires getPoolSize() > 0;
      ensures getPoolSize() == \old(getPoolSize());
      ensures \result != null;
   */
  /**
   * Swaps a tile with a random tile from the pool.
   * @param tile The tile that goes into the pool.
   * @return The tile that comes out of the pool.
   */
  public Tile swapTileWithPool(Tile tile) {
    addTileToPool(tile);
    return drawRandomTileFromPool();
  }
  
  /*@ requires getPoolSize() > 0;
      ensures getPoolSize() == \old(getPoolSize()) - 1;
   */
  /**
   * Takes a random tile from the pool and removes it from the pool.
   * @return A random tile from the pool.
   */
  public Tile drawRandomTileFromPool() {
    int randomIndex = (int)Math.round(Math.random() * (pool.size() - 1));
    Tile result = pool.get(randomIndex);
    pool.remove(randomIndex);
    return result;
  }

  /*@ requires tile != null;
      ensures getPoolSize() == \old(getPoolSize()) + 1;
   */
  /**
   * Adds a tile to the pool.
   * @param tile The tile that needs to be added to the pool.
   */
  public void addTileToPool(Tile tile) {
    pool.add(tile);
  }
  
  /*@ requires getPlayerNrs() != null;
      ensures (\forall int playerNr; getPlayerNrs().contains(playerNr); 
              getPlayer(playerNr).getHand().size() == 6);
      ensures getPoolSize() == \old(getPoolSize()) - (getPlayerNrs().size() * 6);
   */
  /**
   * Gives every player 6 random tiles from the pool and sends those to the players personally.
   */
  public void dealTiles() {
    Set<Integer> playerNrs = getPlayerNrs();
    for (int i = 0; i < 6; i++) {
      for (int playerNr : playerNrs) {
        Player player = getPlayer(playerNr);
        try {
          player.addToHand(drawRandomTileFromPool());
        } catch (HandIsFullException e) {
          System.out.println("HandIsFullException occured while dealing the tiles");
        }
      }
    }
    Set<Integer> playerNumbers = getPlayerNrs();
    for (int number : playerNumbers) {
      server.getThread(number).sendMessage("NEW" + getPlayer(number).handToString());
    }
    // The player with the best hand is here set as the starting player.
    setCurrentPlayer(calculatePlayerNrWithBestHand());
  }

  /*@ requires !getPlayerNrs().contains(playerNr);
      ensures getPlayerNrs().contains(playerNr);
      ensures getPlayer(playerNr) != null;
      ensures getPlayerNrs().size() == \old(getPlayerNrs().size()) + 1;
   */
  /**
   * Creates a new player and adds it to the playerList.
   * @param playerNr The player number of the new player.
   * @param name The name of the new player.
   */
  public synchronized void addPlayer(int playerNr, String name) {
    synchronized (playerList) {
      playerList.put(playerNr, new Player(name, playerNr));
    }
  }
  
  /*@ requires getPlayerNrs().contains(playerNr);
      ensures !getPlayerNrs().contains(playerNr);
      ensures getPlayer(playerNr) == null;
      ensures getPlayerNrs().size() == \old(getPlayerNrs().size()) - 1;
   */
  /**
   * Removes the player with the given playerNr from the playerList.
   * @param playerNr The number of the player that needs to be removed.
   */
  public void removePlayer(int playerNr) {
    synchronized (playerList) {
      playerList.remove(playerNr);
    }
  }
  
  /*@ requires getPlayerNrs().contains(currentPlayer);
      ensures getCurrentPlayer() == currentPlayer;
   */
  public void setCurrentPlayer(int currentPlayer) {
    this.currentPlayer = currentPlayer;
  }
  
  /*@ requires getPlayerNrs() != null;
      ensures \result > 0 & \result < 5;
      ensures (\forall int playerNr; getPlayerNrs().contains(playerNr); 
              getPlayer(playerNr).getScore() <= \result); 
   */
  /**
   * Searches for the player with the highest score.
   * @return The player with the highest score.
   */
  /*@ pure */ public int getWinningPlayerNr() {
    Set<Integer> playerNrs = getPlayerNrs();
    int highestPointsYet = -1;
    int playerNrWithhighestPointsYet = 0;
    for (int playerNr : playerNrs) {
      int score = getPlayer(playerNr).getScore();
      if (score > highestPointsYet) {
        highestPointsYet = score;
        playerNrWithhighestPointsYet = playerNr;
      }
    }
    return playerNrWithhighestPointsYet;
  }

  /*@ pure */ public int getCurrentPlayer() {
    return currentPlayer;
  }
  
  /*@ pure */ public Player getPlayer(int playerNr) {
    return playerList.get(playerNr);
  }

  /*@ pure */ public Server getServer() {
    return server;
  }

  /*@ pure */ public Board getBoard() {
    return board;
  }
  
  /*@ pure */ public Set<Integer> getPlayerNrs() {
    return playerList.keySet();
  }
  
  //@ ensures \result >= 0;
  /*@ pure */ public int getPoolSize() {
    return pool.size();
  }
  
  //@ requires getCurretPlayer() == 0;
  //@ ensures getPlayerNrs().contains(\result);
  /**
   * Calculates which player has the best move in their hand
   * and applies that move to the board.
   */
  public int calculatePlayerNrWithBestHand() {
    Set<Integer> playerNrs = getPlayerNrs();
    int playerNrWithBestPossibleHandPointsYet = 0;
    List<Tile> overAllBestRow = new ArrayList<Tile>();
    for (int playerNr : playerNrs) {
      List<Tile> hand = getPlayer(playerNr).getHand();
      List<Tile> bestRow = new ArrayList<Tile>();
      for (Tile tile : hand) {
        // The list only tiles will be added in if they have the same shape and if 
        // the list rowWithShapeTheSameColors doesn't already contain the color of the tiles.
        List<Tile> rowWithShapeTheSame = new ArrayList<Tile>();
        List<String> rowWithShapeTheSameColors = new ArrayList<String>();
        rowWithShapeTheSame.add(tile);
        rowWithShapeTheSameColors.add(tile.getColor());
        // The list only tiles will be added in if they have the same color and if 
        // the list rowWithColorTheSameShapes doesn't already contain the shape of the tiles.
        List<Tile> rowWithColorTheSame = new ArrayList<Tile>();
        List<String> rowWithColorTheSameShapes = new ArrayList<String>();
        rowWithColorTheSame.add(tile);
        rowWithColorTheSameShapes.add(tile.getShape());
        // Add the tiles to the lists if they match the above description.
        for (Tile tile2 : hand) {
          if (tile.getShape().equals(tile2.getShape()) 
              && !rowWithShapeTheSameColors.contains(tile2.getColor())) {
            rowWithShapeTheSame.add(tile2);
            rowWithShapeTheSameColors.add(tile2.getColor());
          }
          
          if (tile.getColor().equals(tile2.getColor()) 
              && !rowWithColorTheSameShapes.contains(tile2.getShape())) {
            rowWithColorTheSame.add(tile2);
            rowWithColorTheSameShapes.add(tile2.getShape());
          }
        }
        // Check if the current list is bigger than the previous biggest list yet.
        // If so, then the current list is the biggest list yet.
        if (rowWithShapeTheSame.size() > bestRow.size()) {
          bestRow = new ArrayList<Tile>();
          bestRow.addAll(rowWithShapeTheSame);
        }
        if (rowWithColorTheSame.size() > bestRow.size()) {
          bestRow = new ArrayList<Tile>();
          bestRow.addAll(rowWithColorTheSame);
        }
      }
      // Check if the current list is bigger than the previous biggest list yet.
      // If so, then the current list is the biggest list yet.
      if (bestRow.size() > overAllBestRow.size()) {
        playerNrWithBestPossibleHandPointsYet = playerNr;
        overAllBestRow = new ArrayList<Tile>();
        overAllBestRow.addAll(bestRow);
      }
    }
    return playerNrWithBestPossibleHandPointsYet;
  }
  
  /*@ requires getPlayerNrs() != null;
      ensures getPoolSize() > 0 ==> \result == false;
      ensures (\forall int playerNr; getPlayerNrs().contains(playerNr); 
              (getPlayer(playerNr).getHand().size() == 0 & getPoolSize() == 0) 
              ==> \result == true); 
   */
  /**
   * Checks if the game is over. The game is over when the
   * pool is empty and someone's hand is empty.
   * @return True of False whether the game is over or not.
   */
  public boolean isGameOver() {
    boolean result = getPoolSize() == 0;
    if (result) {
      result = false;
      Set<Integer> playerNrs = getPlayerNrs();
      for (int playerNr : playerNrs) {
        if (getPlayer(playerNr).getHand().size() == 0) {
          result = true;
          break;
        }
      }
    }
    return result;
  }
}
