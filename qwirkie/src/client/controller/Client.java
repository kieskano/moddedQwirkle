package client.controller;

import client.model.ComputerPlayer;
import client.model.HumanPlayer;
import client.model.Move;
import client.model.NaiveStrategy;
import client.model.OpponentPlayer;
import client.model.Player;
import client.model.SmartStrategy;
import client.model.Strategy;
import client.model.SuperSmartStrategy;
import client.model.Tile;
import client.view.Printer;
import exceptions.HandIsFullException;
import exceptions.InvalidCommandException;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.OutputStreamWriter;
import java.net.InetAddress;
import java.net.Socket;
import java.util.ArrayList;
import java.util.List;

/**
 * The client that communicates with the server and recognizes commands received from the server.
 * @author Han Hollander
 */
public class Client extends Thread {
  private static final String USAGE = "usage: java week7.cmdchat.Client <name> <address> <port>";

  private String clientName;
  private Socket sock;
  private BufferedReader in;
  private BufferedWriter out;
  private Game game;
  
  private InetAddress host;
  private int port;
  

  /**
   * Constructs a socket and input and output to write and listen for the server.
   * @param name name of client
   * @param host host 
   * @param port port of server
   * @param game game that made the client
   * @throws IOException if socket cant be created
   */
  public Client(String name, InetAddress host, int port, Game game) throws IOException {
    clientName = name;
    this.host = host;
    this.port = port;
    sock = new Socket(this.host, this.port);
    this.game = game;
    in = new BufferedReader(new InputStreamReader(sock.getInputStream()));
    out = new BufferedWriter(new OutputStreamWriter(sock.getOutputStream()));
  }

  /**
   * Reads the messages in the socket connection. Each message will be checked.
   */
  public synchronized void run() {
    String text = "";
    try {
      while (text != null) {
        text = in.readLine();
        if (!(text == null) && !text.equals("\n")) {
          //Check for all the commands if the text is such a command. If so, excecute things.
          checkWelcome(text);
          checkNames(text);
          checkTurn(text);
          checkNext(text);
          checkNew(text);
          checkKick(text);
          checkWinner(text);
          Printer.printToLog("IN: " + text);
        }
      }
    } catch (IOException e) {
      Printer.print("Previous game will now stop.");
      shutdown();
    } catch (InvalidCommandException e) {
      Printer.print("Invalid command received: " + e);
    }
  }
  
  /**
   * Check incoming messages with NEW command.
   * @param text The command.
   */
  public void checkNew(String text) {
    String[] command = text.split(" ");
    if (text.startsWith(Game.NEW) && command.length <= 8) {
      if (command.length == 2 && command[1].equals("empty")) {
        //[NEW empty] command is received if the pool has no tiles left.
        Printer.printBoard(game);
        Printer.print("There are no tiles left in the pool." + "\n");
      } else {
        //If the command is not empty, add all tiles in the command to the hand of the player.
        for (int i = 1; i < command.length; i++) {
          String colour = command[i].substring(0, 1);
          String shape = command[i].substring(1, 2);
          Tile tile = new Tile(colour, shape);
          try {
            game.getPlayer().addToHand(tile);
          } catch (HandIsFullException e) {
            Printer.print(e);
          }
          //Update the pool.
          game.setPool(game.getPool() - 1);
        }
        Printer.printBoard(game);
        Printer.print("Tiles in pool: " + game.getPool() + "\n");
      }
    }
  }
  
  /**
   * Check incoming messages with KICK command.
   * @param text The command.
   */
  public void checkKick(String text) {
    String[] command = text.split(" ");
    int tilesBackToPool = 0;
    int playerNumber = -1;
    if (text.startsWith(Game.KICK)) {
      try {
        playerNumber = Integer.parseInt(command[1]);
        tilesBackToPool = Integer.parseInt(command[2]);
      } catch (NumberFormatException e) {
        Printer.print("Not a number. (KICK)");
      }
      //Update the pool. The tiles of the kicked player go back into the pool.
      game.setPool(game.getPool() + tilesBackToPool);
      Printer.print("Tiles in pool: " + game.getPool() + "\n");
      
      Printer.print(getPlayerName(playerNumber) 
          +  " IS KICKED FOR THE FOLLOWING REASON:" + text.substring(8) + "\n");
    }
  }
  
  /**
   * Check incoming messages with WINNER command.
   * @param text The command.
   */
  public void checkWinner(String text) {
    String[] command = text.split(" ");
    int playerNumber = -1;
    if (text.startsWith(Game.WINNER)) {
      try {
        playerNumber = Integer.parseInt(command[1]);
      } catch (NumberFormatException e) {
        Printer.print("Not a number. (WINNER)");
      }
      //Print board for the last time.
      Printer.printBoard(game);
      if (playerNumber == game.getPlayer().getPlayerNumber()) {
        Printer.print("You won!\n");
      } else {
        Printer.print("The winner is... " + getPlayerName(playerNumber) + "!\n");
      }
      //Ask if client wants to play again.
      Printer.print("Would you like to play another game? Y/N");
      String answer = Qwirkle.readInput();
      if (answer.equals("Y") || answer.equals("y")) {
        //Create new game and before shutting the current game down.
        String[] args = new String[4];
        args[0] = clientName;
        args[1] = host.getHostAddress();
        args[2] = Integer.toString(port);
        args[3] = game.getPlayerType();
        Qwirkle.main(args);
      }
      //Shut down.
      shutdown();
    }
  }
  
  /**
   * Check incoming messages with TURN command.
   * @param text The command.
   */
  public void checkTurn(String text) throws InvalidCommandException {
    String[] command = text.split(" ");
    int playerNumber = -1;
    List<Move> moves = new ArrayList<>();
    if (text.startsWith(Game.TURN)) {
      try {
        playerNumber = Integer.parseInt(command[1]);
      } catch (NumberFormatException e) {
        Printer.print("Not a number. (TURN1)");
      }
      if (command.length == 3 && command[2].equals("empty")) {
        //[TURN <pnr> empty] command is received if somebody swapped.
        Printer.print(getPlayerName(playerNumber) + " swapped." + "\n");
      } else if (command.length <= 20 && ((command.length - 2) % 3 == 0)) {
        //Else, make a list with every move in the command.
        for (int i = 0; i < ((command.length - 2) / 3); i++ ) {
          int row = 0;
          int column = 0;
          try {
            row = Integer.parseInt(command[(3 * i) + 3]);
            column = Integer.parseInt(command[(3 * i) + 4]);
          } catch (NumberFormatException e) {
            Printer.print("Not a number. (TURN2)");
          }
          String colour = command[(3 * i) + 2].substring(0, 1);
          String shape = command[(3 * i) + 2].substring(1, 2);
          moves.add(new Move(new Tile(colour, shape), row, column));
        }
      } else {
        throw new InvalidCommandException("(In TURN)");
      }
      // If the player that executed the turn is not the player itself 
      // update the board.
      if (playerNumber != game.getPlayer().getPlayerNumber()) {
        game.opponentTurn(moves, game.getPlayerWithNumber(playerNumber));
        if (!(command.length == 3)) {
          Printer.print("\n" + getPlayerName(playerNumber) 
              + " just made the following move: " + moves  + "\n");
        }
      }
    }  
  }
  
  /**
   * Check incoming messages with NEXT command.
   * @param text The command.
   */
  public void checkNext(String text) throws InvalidCommandException {
    String[] command = text.split(" ");
    int playerNumber = -1;
    if (text.startsWith(Game.NEXT) && command.length == 2) {
      try {
        playerNumber = Integer.parseInt(command[1]);
      } catch (NumberFormatException e) {
        Printer.print("Not a number. (NEXT)");
      }
      //If the pnr is that of the player itself, it's their turn.
      if (playerNumber == game.getPlayer().getPlayerNumber()) {
        game.playerTurn();
      } else {
        //Else, it's the opponents turn.
        String playerName = getPlayerName(playerNumber);
        Printer.print("It is now " + playerName + "'s turn." + "\n");
      }
    }  
  }  
  
  /**
   * Check incoming messages with NAMES command.
   * @param text The command.
   */
  public void checkNames(String text) throws InvalidCommandException {
    String[] command = text.split(" ");
    if (text.startsWith(Game.NAMES) 
        && (command.length == 6 || command.length == 8 || command.length == 10)) {
      //Add every player to the list of players in game.
      int numberOfPlayers = (command.length - 2) / 2;
      for (int i = 0; i < numberOfPlayers; i++) {
        String name = command[(2 * i) + 1];
        String number = command[(2 * i) + 2];
        addPlayer(name, number);
      }
      //Update the pool;
      for (int j = 0; j < numberOfPlayers  - 1; j++) {
        game.setPool((game.getPool() - 6));
      }
    } else if (command.length == 4 && text.startsWith(Game.NAMES)) {
      addPlayer(command[1], command[2]);
    }
  }

  /**
   * Check incoming messages with WELCOME command.
   * @param text The command.
   */
  public void checkWelcome(String text) throws InvalidCommandException {
    String[] command = text.split(" ");
    int playerNumber = -1;
    if (text.startsWith(Game.WELCOME) && command.length == 3) {
      try {
        playerNumber = Integer.parseInt(command[2]);
      } catch (NumberFormatException e) {
        Printer.print("Not a number. (WELCOME)");
      }
      //If player type is human, create a new human player.
      if (game.getPlayerType().equals("h")) {
        Player player = new HumanPlayer(command[1], playerNumber, game);
        game.setPlayer(player);
      } else if (game.getPlayerType().equals("b")) {
        //If player type is AI, creat a new computer player.
        //determine strategy
        Strategy strat = null;
        if (Qwirkle.getStrategyType().equals("n")) {
          strat = new NaiveStrategy();
        } else if (Qwirkle.getStrategyType().equals("s")) {
          strat = new SmartStrategy();
        } else if (Qwirkle.getStrategyType().equals("ss")) {
          strat = new SuperSmartStrategy();
        }
        Player player = new ComputerPlayer(command[1], playerNumber, strat);
        game.setPlayer(player);
      }
      Printer.print("Welcome message received.");
      Printer.print("Waiting for other players to connect...");
    }
  }

  /**
   * Gets the name of the player with playerNumber.
   * @param playerNumber The ID of the player.
   * @return The name of the player.
   */
  public String getPlayerName(int playerNumber) {
    String playerName = "";
    for (Player player : game.getPlayerList()) {
      if (playerNumber == player.getPlayerNumber()) {
        playerName = player.getName();
      }
    }
    return playerName;
  }
  
  /**
   * Adds player to the list in game.
   * @param name The name of the player;
   * @param number The ID of the player;
   */
  public void addPlayer(String name, String number) {
    int playerNumber = -1;
    try {
      playerNumber = Integer.parseInt(number);
    } catch (NumberFormatException e) {
      Printer.print("Not a valid number. (addPlayer)");
    }
    Player player1 = new OpponentPlayer(name, playerNumber);
    game.addPlayerToList(player1);
  }
  
  /**
   * Sends message to client handler.
   * @param msg The message.
   */
  public void sendMessage(String msg) {
    try {
      Printer.printToLog("OUT: " + msg);
      out.write(msg);
      out.newLine();
      out.flush();
    } catch (IOException e) {
      Printer.print("Lost connection. (Maybe you were kicked...?)");
      shutdown();
    }

  }
  
  /**
   * Close the socket connection.
   */
  public void shutdown() {
    Printer.print("Closing socket connection from previous game...");
    try {
      sock.close();
    } catch (IOException e) {
      Printer.print("Could not close socket.");
    }
    Printer.print("Socket from previous game closed");
  }

  public String getClientName() {
    return clientName;
  }

  public static String getUsage() {
    return USAGE;
  }

 
}
