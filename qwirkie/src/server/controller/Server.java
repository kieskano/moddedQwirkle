package server.controller;

import server.model.Game;
import server.model.Move;
import server.model.Tile;
import server.view.TuiView;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.net.ServerSocket;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

public class Server extends Thread{
  private static final String USAGE = "usage: " + Server.class.getName() 
      + " <port> <numberOfPlayers(2,3,4)> <AITime>";
  
  /** Start een Server-applicatie op. */
  public static void main(String[] args) {
    int portInt = 0;
    int numberOfPlayers = 0;
    int aiTime = 0;
    ServerSocket serverSocket = null;
    if (args.length > 0) {
      // Create server with main arguments
      if (args.length != 3) {
        System.out.println(USAGE);
        System.exit(0);
      }
      try {
        portInt = Integer.parseInt(args[0]);
        numberOfPlayers = Integer.parseInt(args[1]);
        aiTime = Integer.parseInt(args[2]);
      } catch (NumberFormatException e) {
        System.out.println(USAGE);
        System.exit(0);
      }
      
      if (numberOfPlayers < 2 && numberOfPlayers > 4) {
        System.out.println(USAGE);
        System.exit(0);
      }
      try {
        serverSocket = new ServerSocket(portInt);
      } catch (IOException e) {
        System.out.println("Could not create server socket on port " + portInt);
      }
    } else {
      // Create server with user input.
      Boolean validAnswer = false;
      String answer = "";
      while (!validAnswer) {
        System.out.print("Number of players allowed per game (2,3 or 4):    ");
        try {
          BufferedReader reader = new BufferedReader(new InputStreamReader(System.in));
          answer = reader.readLine();
          validAnswer = true;
        } catch (IOException e) {
          System.out.println("Could not read line");
        }
        if (validAnswer) {
          try {
            numberOfPlayers = Integer.parseInt(answer);
          } catch (NumberFormatException e) {
            System.out.println(answer + " is not a valid number");
            validAnswer = false;
          }
          validAnswer = validAnswer && (numberOfPlayers > 1 && numberOfPlayers < 5);
          if (!validAnswer) {
            System.out.println("Not a valid answer. Enter the number 2, 3 or 4!");
          }
        }
      }
      
      validAnswer = false;
      while (!validAnswer) {
        System.out.print("Allowed time to think per turn (in milliseconds): ");
        try {
          BufferedReader reader = new BufferedReader(new InputStreamReader(System.in));
          answer = reader.readLine();
          validAnswer = true;
        } catch (IOException e) {
          System.out.println("Could not read line");
        }
        if (validAnswer) {
          try {
            aiTime = Integer.parseInt(answer);
          } catch (NumberFormatException e) {
            System.out.println(answer + " is not a valid waiting time");
            validAnswer = false;
          }
          validAnswer = validAnswer && aiTime > 0;
          if (!validAnswer) {
            System.out.println("Not a valid time. Please try again!");
          }
        }
      }
      validAnswer = false;
      while (!validAnswer) {
        System.out.print("Create game servers on port (1 - 65535):          ");
        try {
          BufferedReader reader = new BufferedReader(new InputStreamReader(System.in));
          answer = reader.readLine();
          validAnswer = true;
        } catch (IOException e) {
          System.out.println("Could not read line");
        }
        if (validAnswer) {
          try {
            portInt = Integer.parseInt(answer);
          } catch (NumberFormatException e) {
            System.out.println(answer + " is not a valid number");
            validAnswer = false;
          }
          validAnswer = validAnswer && (portInt > 0 && portInt < 65536);
          if (validAnswer) {
            try {
              serverSocket = new ServerSocket(portInt);
            } catch (IOException e) {
              System.out.println("Could not create server socket on port " + portInt);
              validAnswer = false;
            }
          } else {
            System.out.println("Not a valid port. Please enter a number between 1 and 65535");
          }
        }
      }
    }
    
    Object waitingForFullLoby = new Object();
    int serverNr = 1;
    while (true) {
      Server server = new Server(serverSocket, numberOfPlayers, 
          aiTime, waitingForFullLoby, serverNr);
      server.start();
      synchronized (waitingForFullLoby) {
        try {
          waitingForFullLoby.wait();
        } catch (InterruptedException e) {
          System.out.println("Server got interupted while waiting for the new lobby to get full.");
          System.exit(0);
        }
      }
      serverNr++;
    }
  }


  private HashMap<Integer, ClientHandler> threads;
  private ServerSocket serverSocket;
  private int numberOfPlayers;
  private Game game;
  private Object listener;
  private Object monitor;
  private int aiTime;
  private boolean wokenByTimer;
  private boolean imReady;
  private Object waitingForFullLoby;
  private int serverNr;
  private TuiView tui;
  
  /*@ requires serverSocket != null;
      requires numberOfPlayers > 1 & numberOfPlayers < 5;
      requires aiTime > 0;
      requires waitingForFullLoby != null;
      requires serverNr > 0;
      ensures getServerNr() == serverNr;
      ensures isReady() == true;
   */
  /** Constructs a new Server object. */
  public Server(ServerSocket serverSocket, int numberOfPlayers, 
      int aiTime, Object waitingForFullLoby, int serverNr) {
    this.serverNr = serverNr;
    tui = new TuiView(this);
    this.numberOfPlayers = numberOfPlayers;
    threads = new HashMap<Integer, ClientHandler>();
    game = new Game(this);
    monitor = new Object();
    listener = new Object();
    imReady = true;
    this.aiTime = aiTime;
    this.waitingForFullLoby = waitingForFullLoby;
    this.serverSocket = serverSocket;
    
  }

  /**
   * Listens to a port of this Server if there are any Clients that 
   * would like to connect. For every new socket connection a new
   * ClientHandler thread is started that takes care of the further
   * communication with the Client.
   */
  public void run() {
    // For every client that connects a client handler is made and started
    // until the max player limit is reached.
    tui.print("Waiting for clients to connect");
    int numberOfConnectingPlayer = 1;
    while (numberOfConnectingPlayer - 1 < numberOfPlayers) {
      try {
        tui.print("Clients connected: [" + (numberOfConnectingPlayer - 1) 
            + " of " + numberOfPlayers + "]");
        ClientHandler ch = new ClientHandler(numberOfConnectingPlayer - 1, 
            this, serverSocket.accept(), listener);
        addHandler(numberOfConnectingPlayer - 1, ch); // - 1 is added so the players are numbered 0, 1, 2, 3
        ch.start();
        numberOfConnectingPlayer++;
      } catch (IOException e) {
        tui.print("Could not connect to client " + numberOfConnectingPlayer);
      }
    }
    
    // This notifies the main method that this game server is full
    // so the main method can create and start another game server.
    synchronized (waitingForFullLoby) {
      waitingForFullLoby.notifyAll();
    }
    
    tui.print("Clients connected: [" + (numberOfConnectingPlayer - 1) 
        + " of " + numberOfPlayers + "]");
    tui.print("Waiting for everyone to send their name" + "\n");
    
    while (!allPlayerNamesAreKnown()) {
      synchronized (monitor) {
        try {
          monitor.wait();
        } catch (InterruptedException e) {
          tui.print("Interupted while waiting for everyone to send their name");
        }
      }
    }
    // When every client handler has received a "HELLO <name>" message
    // and has send a "WELCOME <playerNr>" message.
    
    // Send every player the names of the other players and the time 
    // they have to determine their turn in the format of:
    // "NAMES <playerNr> <name> <playerNr> <name> <playerNr> <name> <time>"
    Set<Integer> playerNrs = threads.keySet();
    tui.print("Everyone has send their name");
    String namesMsg = "NAMES";
    for (int number : playerNrs) {
      namesMsg = namesMsg + " " + game.getPlayer(number).getName() + " " + number;
    }
    broadcast(namesMsg + " " + aiTime);
    
    
    if (threads.size() > 1) {
      // Here are the tiles dealt and the server calculates the best move
      // for every player and places the best move on the board.
      // After that all the hands of the players will be send to them in the format of:
      // "NEW <tile> <tile> <tile> <tile> <tile> <tile>"
      tui.print("Dealing tiles and calculating who may start");
      game.dealTiles();
      tui.print("Tiles dealt and " + game.getCurrentPlayer() + " may start");
      broadcast("NEXT " + game.getCurrentPlayer());
    }
    
    while (!game.isGameOver() && threads.size() > 1) {
      synchronized (monitor) {
        Timer timer = new Timer(aiTime, this);
        timer.start();
        try {
          imReady = true;
          wokenByTimer = false;
          synchronized (listener) {
            listener.notifyAll();
          }
          monitor.wait(); // Wait for a clientHandler to do something (make a move or kick)
          imReady = false;
        } catch (InterruptedException e) {
          tui.print("Interupted while waiting for someone to make a move");
        }
        if (wokenByTimer) {
          kick(game.getCurrentPlayer(), "Did not make a move in time");
          getThread(game.getCurrentPlayer()).shutdown();
        } else {
          timer.stopTimer();
        }
        if (!game.isGameOver() && threads.size() > 1) {
          nextPlayerTurn();
        }
      }
    }
    imReady = true;
    // Send the winner to all players
    // "WINNER <playerNr>
    broadcast("WINNER " + game.getWinningPlayerNr());
    
    // Close the connection with all players
    playerNrs = threads.keySet();
    List<Integer> players = new ArrayList<Integer>();
    players.addAll(playerNrs);
    while (players.size() > 0) {
      threads.get(players.get(0)).shutdown();
      players.remove(0);
    }
  }
  
  /*@ requires getGame().getPlayerNrs() != null;
      ensures (\forall int playerNr; getThread(playerNr) != null; 
              !getGame().getPlayerNrs().contains(playerNr) ==> \result == false); 
   */
  /**
   * Checks if all connected players have send their name.
   * @return True of false whether all players have send their name or not.
   */
  public boolean allPlayerNamesAreKnown() {
    // Here is checked if for every client handler in server
    // also a player in game is created.
    boolean result = true;
    Set<Integer> playerNrs = threads.keySet();
    Set<Integer> knownPlayers = game.getPlayerNrs();
    for (int playerNr : playerNrs) {
      result = result && knownPlayers.contains(playerNr);
    }
    return result;
  }

  /**
   * Sends a message using the collection of connected ClientHandlers
   * to all connected Clients.
   * @param msg message that is send
   */
  public synchronized void broadcast(String msg) {
    synchronized (threads) {
      for (Map.Entry<Integer, ClientHandler> entry : threads.entrySet()) {
        entry.getValue().sendMessage(msg);
      }
    }
  }

  //@ ensures getThread(playerNr) == handler;
  /**
   * Add a ClientHandler to the collection of ClientHandlers.
   * @param handler ClientHandler that will be added
   */
  public synchronized void addHandler(int playerNr, ClientHandler handler) {
    synchronized (threads) {
      threads.put(playerNr, handler);
    }
  }

  //@ ensures getThread(playerNr) == null;
  /**
   * Remove a ClientHandler from the collection of ClientHanlders. 
   * @param playerNr number of the ClientHandler that will be removed.
   */
  public synchronized void removeHandler(int playerNr) {
    synchronized (threads) {
      threads.remove(playerNr);
    }
  }
  
  /*@ pure */ public Game getGame() {
    return game;
  }
  
  /*@ pure */ public ClientHandler getThread(int playerNr) {
    return threads.get(playerNr);
  }
  
  /*@ pure */ public int getServerNr() {
    return serverNr;
  }
  
  /*@ pure */ public Set<Integer> getPlayerNrs() {
    return threads.keySet();
  }
  
  /*@ pure */ public TuiView getObserver() {
    return tui;
  }
  
  /*@ pure */ public boolean isReady() {
    return imReady;
  }
  
  /*@ requires getThread(playerNr) != null;
      ensures getGame().getPlayer(playerNr) == null;
      ensures getGame().getPoolSize() == \old(getGame().getPoolSize()) 
              + \old(getGame().getPlayer(playerNr).getHand().size()); 
   */
  /**
   * Kicks the given player, removes all references to that player
   * in the game and broadcasts it to all players. (the game keeps going
   * without the player, but the tiles he/she had in his/her hand are returned
   * to the pool)
   * @param playerNr The number of the player that is being kicked.
   * @param reason A String with a message about the reason of the kick.
   */
  public void kick(int playerNr, String reason) {
    List<Tile> hand = game.getPlayer(playerNr).getHand();
    game.removePlayer(playerNr);
    for (Tile tile : hand) {
      game.addTileToPool(tile);
    }
    // "KICK <playerNr> <ammountOfTilesBackIntoThePool> <reason>"
    broadcast("KICK " + playerNr + " " + hand.size() + " " + reason);
  }
  
  //@ ensures getGame().getCurrentPlayer() != \old(getGame().getCurrentPlayer());
  /**
   * Gives the turn to the next player and broadcasts it to all players.
   */
  public void nextPlayerTurn() {
    // Here it gets the current player and keeps going through the
    // numbers 1, 2, 3 and 4 from the current player number until
    // it has found another valid player number.
    Set<Integer> playingPlayers = threads.keySet();
    int previousPlayer = game.getCurrentPlayer();
    int nextPlayer = (previousPlayer + 1) % 5;
    while (!playingPlayers.contains(nextPlayer)) {
      nextPlayer = (nextPlayer + 1) % 5;
    }
    game.setCurrentPlayer(nextPlayer);
    // Here the server sends a message to all the players who's turn 
    // it is now with the format:
    // "NEXT <playerNr>"
    broadcast("NEXT " + nextPlayer);
  }
  
  //@ requires getThread(playerNr) != null;
  //@ requires turn != null;
  /**
   * Broadcasts the given turn and the player who made that turn.
   * @param playerNr The player who made the turn.
   * @param turn The turn which was made.
   */
  public void sendTurn(int playerNr, List<Move> turn) {
    String msg = "TURN " + playerNr;
    for (int i = 0; i < turn.size(); i++) {
      msg = msg + " " + turn.get(i).toString();
    }
    // "TURN <playerNr> <tile> <row> <column> <tile> <row> <column>"
    broadcast(msg);
  }
  
  //@ requires getThread(playerNr) != null;
  //@ requires tiles != null;
  /**
   * Sends a player the given tiles
   * @param playerNr The player to whom the tiles need to be send to.
   * @param tiles The tiles that need to be send
   */
  public void giveTiles(int playerNr, List<Tile> tiles) {
    String msg;
    if (tiles.size() > 0) {
      msg = "NEW";
      for (Tile tile : tiles) {
        msg = msg + " " + tile.toString();
      }
    } else {
      msg = "NEW empty";
    }
    // "NEW <tile> <tile> <tile>"
    // "NEW empty" (if the pool is empty)
    threads.get(playerNr).sendMessage(msg);
  }
  
  /**
   * A function that is only called by the timer. This function wakes
   * the server and makes sure that the server can tell that it is
   * woken by the timer.
   */
  public void timerWakesServer() {
    synchronized (monitor) {
      wokenByTimer = true;
      monitor.notifyAll();
    }
  }
  
  /**
   * A function that is only called by a clientHandler. This function wakes
   * the server.
   */
  public void handlerWakesServer() {
    synchronized (monitor) {
      monitor.notifyAll();
    }
  }
}
