package server.controller;

import server.model.Move;
import server.model.Tile;
import server.view.TuiView;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.OutputStreamWriter;
import java.net.Socket;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

public class ClientHandler extends Thread {
  
  public static final List<String> COLOURS = Arrays.asList("R", "O", "B", "Y", "G", "P");
  public static final List<String> SHAPES = Arrays.asList("o", "d", "s", "c", "x", "*");
  public static final List<String> ALLOWEDCHARS = Arrays.asList("a", "b", "c", "d", "e", 
      "f", "g", "h", "i", "j", "k", "l", "m", "n", "o", "p", "q", "r", "s", "t", "u", "v", 
      "w", "x", "y", "z", "A", "B", "C", "D", "E", "F", "G", "H", "I", "J", "K", "L", "M", 
      "N", "O", "P", "Q", "R", "S", "T", "U", "V", "W", "X", "Y", "Z");
  
  /*@ invariant getClientName().length() > 0 & getClientName().length() < 17;
      invariant (\forall int i; i >= 0 & i < getClientName().length();
                ALLOWEDCHARS.contains(getClientName().substring(i, i + 1)));
   */
  
  private /*@ spec_public */ Server server;
  private /*@ spec_public */ Socket socket;
  private BufferedReader in;
  private BufferedWriter out;
  private String clientName;
  private /*@ spec_public */ int playerNr;
  private Object listener;
  private boolean isShutDown;
  private TuiView tui;
  
  /**
   * Constructor for client handler.
   * @param playerNr The number of the player which this client handler
   *        communicates with.
   * @param server server
   * @param sock socket
   * @param listener the object on which the server notifies when 
   *        it's ready to receive another update.
   * @throws IOException if not able to create in or out stream.
   */
  public ClientHandler(int playerNr, Server server, Socket sock, 
      Object listener) throws IOException {
    this.server = server;
    this.socket = sock;
    this.playerNr = playerNr;
    this.listener = listener;
    isShutDown = false;
    tui = server.getObserver();
    in = new BufferedReader(new InputStreamReader(this.socket.getInputStream()));
    out = new BufferedWriter(new OutputStreamWriter(this.socket.getOutputStream()));
  }
  
  /**
   * THIS CONSTRUCTOR IS ONLY USED FOR JUnit TESTING.  
   * @param playerNr playerNr
   * @param server server
   */
  public ClientHandler(int playerNr, Server server) {
    this.server = server;
    this.playerNr = playerNr;
    isShutDown = false;
    tui = server.getObserver();
  }
  
  /**
   * Reads the in of the socket and handles the input according to the protocol.
   */
  public synchronized void run() {
    String text = "";
    // Starting procedure
    // Here the client handler expects to receive: "HELLO <name>"
    // If everything is as expected, the client handler sends to the player:
    // "WELCOME <playerNr>"
    try {
      text = in.readLine();
      if (isValidStartMessage(text)) {
        String[] textParts = text.split(" ");
        clientName = textParts[1];
        tui.print("Received from client " + playerNr + ": " + text);
        sendMessage("WELCOME " + clientName + " " + playerNr);
        server.getGame().addPlayer(playerNr, clientName);
        server.handlerWakesServer();
      } else {
        server.kick(playerNr, "Did not recieve valid start message");
        shutdown();
      }
    } catch (IOException e) {
      server.kick(playerNr, "lost connection with player");
      shutdown();
    }
    
    // Here the client handler enters a loop in which it reads from the socket
    // and handles accordingly. If the client sends something that is not valid
    // according the protocol, the client is immediately kicked.
    while (!server.getGame().isGameOver() && !isShutDown) {
      try {
        text = in.readLine();
        tui.print("Received from player-" + playerNr + ": " + text);
        if (server.getGame().getCurrentPlayer() == playerNr) {
          if (isValidMoveTurnMessage(text)) {
            if (server.getGame().movePossible(playerNr)) {
              List<Move> turn = convertStringToMoveTurn(text);
              server.getGame().applyMoveTurn(server.getGame().getPlayer(playerNr), turn);
            }
          } else if (isValidSwapTurnMessage(text)) {
            List<Tile> turn = convertStringToSwapTurn(text);
            server.getGame().applySwapTurn(turn, server .getGame().getPlayer(playerNr));
          } else {
            if (!isShutDown) {
              server.kick(playerNr, "made an invalid turn");
              shutdown();
            }
          }
        } else {
          if (!isShutDown) {
            server.kick(playerNr, "spoke before his/her turn");
            shutdown();
          }
        }
      } catch (IOException e) {
        if (!isShutDown) {
          server.kick(playerNr, "lost connection with player");
          shutdown();
        }
      }
      while (!server.isReady()) {
        synchronized (listener) {
          try {
            listener.wait();
            wait(100);
          } catch (InterruptedException e) {
            tui.print("ClientHandler-" + playerNr 
                + " got interupted while waiting for the server to get ready.");
          }
        }
      }
      if (server.getGame().getCurrentPlayer() == playerNr) {
        tui.print("clientHandler-" + playerNr + " wakes server");
        server.handlerWakesServer();
      }
    }
  }
  
  //@ requires text != null;
  //@ requires isValidSwapTurnMessage(text) == true;
  /**
   * Converts the given text to a actual swap turn, which is a list of tiles.
   * @param text The text that needs to be converted.
   * @return The list of tiles that was made from the text.
   */
  public List<Tile> convertStringToSwapTurn(String text) {
    String[] swapTextParts = text.substring(5).split(" ");
    List<Tile> turn = new ArrayList<Tile>();
    for (String tileText : swapTextParts) {
      turn.add(new Tile(tileText.substring(0, 1), tileText.substring(1, 2)));
    }
    return turn;
  }
  
  //@ requires text != null;
  //@ requires isValidMoveTurnMessage(text) == true;
  /**
   * Converts the given text to a actual move turn, which is a list of moves.
   * @param text The text that needs to be converted.
   * @return The list of moves that was made from the text.
   */
  public List<Move> convertStringToMoveTurn(String text) {
    String[] moveTextParts = text.substring(5).split(" ");
    List<Move> turn = new ArrayList<Move>();
    for (int i = 0; i < moveTextParts.length; i += 3) {
      String colour = Character.toString(moveTextParts[i].charAt(0));
      String shape = Character.toString(moveTextParts[i].charAt(1));
      int row = Integer.parseInt(moveTextParts[i + 1]);
      int column = Integer.parseInt(moveTextParts[i + 2]);
      turn.add(new Move(new Tile(colour, shape), row, column));
    }
    return turn;
  }
  
  /*@ ensures !text.startsWith("SWAP ") ==> \result == false;
      ensures text.split(" ").length < 2 || text.split(" ").length > 7 ==> \result == false;
      ensures (\forall int i; i >= 0 & i < text.substring(5).split(" ").length; 
              (!COLOURS.contains(text.substring(5).split(" ")[i].substring(0,1)) 
              || !SHAPES.contains(text.substring(5).split(" ")[i].substring(1,2))) 
              ==> \result == false); */
  /**
   * Checks if the given text is a valid swap turn according to the protocol.
   * @param text The text that needs to be checked.
   * @return True of false whether this text is a valid swap turn or not.
   */
  /*@ pure */ public boolean isValidSwapTurnMessage(String text) {
    boolean result = true;
    String[] swapTextParts = null;
    if (text.startsWith("SWAP ")) {
      String swapText = text.substring(5);
      swapTextParts = swapText.split(" ");
      if (swapTextParts.length > 0 && swapTextParts.length < 7) {
        for (String tile : swapTextParts) {
          if (tile.length() == 2) {
            // Check if the tiles are valid tiles
            result = result && (COLOURS.contains(tile.substring(0,1)) 
                && SHAPES.contains(tile.substring(1,2)));
          } else {
            result = false;
            break;
          }
        }
      } else {
        result = false;
      }
    } else {
      result = false;
    }
    
    //Check if tiles are in the hand of the player and the pool has that many tiles left.
    if (result) {
      List<Tile> turn = convertStringToSwapTurn(text);
      result = result && server.getGame().checkSwapTurn(turn, server.getGame().getPlayer(playerNr));
    }
    return result;
  }
  
  /*@ ensures !text.startsWith("MOVE ") ==> \result == false;
      ensures (\forall int i; i >= 0 & i < text.substring(5).split(" ").length & i % 3 == 0; 
              (!COLOURS.contains(text.substring(5).split(" ")[i].substring(0,1)) 
              || !SHAPES.contains(text.substring(5).split(" ")[i].substring(1,2))) 
              ==> \result == false);
      ensures (\forall int i; i >= 0 & i < text.substring(5).split(" ").length & !(i % 3 == 0); 
              Integer.parseInt(text.substring(5).split(" ")[i]) >= 0
              & Integer.parseInt(text.substring(5).split(" ")[i]) < 183
              ==> \result == false); */
  /**
   * Checks if the given text is a valid move turn according to the protocol
   * and the rules of Qwirkle.
   * @param text The text that needs to be checked.
   * @return True of false whether this text is a valid move turn or not.
   */
  /*@ pure */ public boolean isValidMoveTurnMessage(String text) {
    boolean result = true;
    String[] moveTextParts = null;
    if (text.startsWith("MOVE ")) {
      String moveText = text.substring(5);
      moveTextParts = moveText.split(" ");
      if ((moveTextParts.length % 3) == 0) {
        for (int i = 0; i < moveTextParts.length; i++) {
          // Check if the tiles are valid tiles
          if ((i % 3) == 0) {
            String tileText = moveTextParts[i];
            if (tileText.length() == 2) {
              result = result && (COLOURS.contains(tileText.substring(0,1)) 
                  && SHAPES.contains(tileText.substring(1,2)));
            } else {
              result = false;
              break;
            }
          } else {
            int coordinate;
            try {
              coordinate = Integer.parseInt(moveTextParts[i]);
            } catch (NumberFormatException e) {
              result = false;
              break;
            }
            if (coordinate >= 0 && coordinate <= 182) {
              result = result && true;
            } else {
              result = false;
              break;
            }
          }
        }
      } else {
        result = text.substring(5).equals("emtpy");
      }
    } else {
      result = false;
    }
    
    //Check if the move is valid in the game
    if (result) {
      List<Move> turn = convertStringToMoveTurn(text);
      result = result && server.getGame().checkMoveTurn(turn, server.getGame().getPlayer(playerNr));
    }
    return result;
  }
  
  /*@ requires text != null;
      ensures !text.startsWith("HELLO ") ==> \result == false;
      ensures text.substring(6).length() > 16 ==> \result == false;
      ensures (\forall int i; i >= 0 & i < text.substring(6).length();
              !ALLOWEDCHARS.contains(text.substring(6).substring(i, i + 1))
              ==> \result == false);
   */
  /**
   * Checks if the given text is a valid start message according to the protocol.
   * @param text The text that needs to be checked.
   * @return True of false whether this text is a valid start message or not.
   */
  public boolean isValidStartMessage(String text) {
    // The name may only contain lower and upper case letters
    Boolean result;
    result = text.startsWith("HELLO ");
    if (result) {
      String name = text.substring(6);
      result = result && name.length() < 17 && name.length() > 0;
      for (int i = 0; i < name.length(); i++) {
        // Here is checked for every character in the name if it is one of the allowed characters.
        result = result && ALLOWEDCHARS.contains(name.substring(i, i + 1));
      }
    }
    return result;
  }

  /*@ requires msg.startsWith("WELCOME ") || msg.startsWith("NEW ") ||
               msg.startsWith("NEXT ") || msg.startsWith("TURN ") ||
               msg.startsWith("KICK ") || msg.startsWith("WINNER ") ||
               msg.startsWith("NAMES ");
   */
  /**
   * Sends a message to the client through the out of the socket.
   * @param msg message
   */
  public void sendMessage(String msg) {
    boolean messageSent = true;
    try {
      out.write(msg);
      out.newLine();
      out.flush();
    } catch (IOException e) {
      tui.print("Could not send to player-" + playerNr + ": " + msg);
      messageSent = false;
    }
    if (messageSent) {
      tui.print("Sent to player-" + playerNr + ": " +  msg);
    }
  }
  
  /*@ pure */ public String getClientName() {
    return clientName;
  }
  
  //@ ensures socket.isClosed();
  //@ ensures server.getThread(playerNr) == null;
  /**
   * Closes the socket of this clientHandler.
   */
  public void shutdown() {
    isShutDown = true;
    try {
      socket.close();
    } catch (IOException e) {
      tui.print("Could not close socket in the shutdown procedure.");
    }
    server.removeHandler(playerNr);
    tui.print("Closed the connection with player-" + playerNr);
  }

}
