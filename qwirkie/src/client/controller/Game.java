package client.controller;

import client.model.Board;
import client.model.ComputerPlayer;
import client.model.HumanPlayer;
import client.model.Move;
import client.model.Move.Type;
import client.model.NaiveStrategy;
import client.model.Player;
import client.model.Tile;
import client.view.Printer;
import exceptions.InvalidMoveException;
import exceptions.TileNotInHandException;

import java.awt.Component;
import java.awt.event.KeyEvent;
import java.awt.event.KeyListener;
import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.net.InetAddress;
import java.nio.Buffer;
import java.nio.CharBuffer;
import java.util.ArrayList;
import java.util.List;

import javax.swing.JFrame;
import javax.swing.JTextField;

/**
 * The main controller class. Controls the players, board and client.
 * @author Han Hollander
 */
public class Game extends Component{
     
  private Board board;
    
  private List<Player> playerList;
  private Player player;
  private String playerName;
  
  public static final String MOVE = "MOVE";
  public static final String SWAP = "SWAP";
  public static final String END = "END";
  public static final String HELLO = "HELLO";
  public static final String WELCOME = "WELCOME";
  public static final String NAMES = "NAMES";
  public static final String NEXT = "NEXT";
  public static final String NEW = "NEW";
  public static final String TURN = "TURN";
  public static final String KICK = "KICK";
  public static final String WINNER = "WINNER";
  public static int state = 0;
  public static int row = 91;
  public static int column = 91;
  public static int handPosition = -1;
  public static int turnType = -1;
  public static boolean decided;
  public static boolean endTurn;
  
  private Client client;
  private String playerType; 
  
  private int pool = 108;
  private boolean playerTurn;
  
  private NaiveStrategy hintGen;
  public static Object waitForInput = new Object();;
  
  /**
   * Constructs a new game and a new client.
   * @param name name of client.
   * @param host server.
   * @param port port of server.
   */
  public Game(String name, InetAddress host, int port) {
    this.board = new Board();
    playerList = new ArrayList<>();
    this.playerName = name;
    this.setPlayerType(Qwirkle.getPlayerType());
    setHintGen(new NaiveStrategy());
    //Try creating a client.
    try {
      Printer.print("Creating client... ");
      client = new Client(name, host, port, this);
      Printer.print("Client " + client.getClientName() + " created");
      Printer.print("Starting client... ");
      client.start();
      Printer.print("Client started.");
      Printer.print("Sending registration message... ");
      client.sendMessage(HELLO + " " + playerName);
      Printer.print("Registration message send.");
      Printer.print("Waiting for welcome message... ");
    } catch (IOException | NullPointerException e) {
      Printer.print("Client could not be created or started, trying again.\n");
      String[] args = new String[0];
      Qwirkle.main(args);
    }
  }

  /**
   * Gets called when it is the turn of the player.
   */
  public void playerTurn() {
    if (getPlayer() instanceof ComputerPlayer) {
      Printer.printBoard(this);
      //Get one single hint, only at start of turn.
      if (getPlayer() instanceof HumanPlayer && getPlayer().getHand().size() != 0) {
        Printer.print("\nHint: " + getHint().colourToString());
      }
      setPlayerTurn(true);
      Printer.print("\nIt is your turn!");
      while (playerTurn) {
        Printer.print("\nWhat is your action?");
        //Get user input.
        makeMove();
        Printer.printBoard(this);
      }
    } else {
      row = 91;
      column = 91;
      determineMoveType();
      endTurn = false;
      while (!endTurn) {
        determineTile();
        if (handPosition == getPlayer().getHand().size()) {
          endTurn = true;
        }
        if (!endTurn) {
          if (turnType == 1) {
            determinePlace();
          } else {
            Tile tile = getPlayer().getHand().get(handPosition);
            getPlayer().getMoves().add(new Move(tile));
            try {
              getPlayer().removeFromHand(tile);
            } catch (TileNotInHandException e) {
              // TODO Auto-generated catch block
              e.printStackTrace();
            }
          }
        }
      }
    }
    //Update score.
    int score = 0;
    if (board.getMoveList().size() != 0) {
      score = board.getScoreCurrentTurn();
    } 
    //Since the player in the list is different than the player field:
    getPlayerWithNumber(player.getPlayerNumber())
      .setScore(getPlayerWithNumber(player.getPlayerNumber()).getScore() + score);
    //End the turn (after the END command).
    endTurn();
  }
  
  private void determinePlace() {
    state = 3;
    decided = false;
    while (!decided) {
      Printer.printBoard(this, handPosition, row, column);
      keyTyped();
      if (decided) {
        Move move = new Move(getPlayer().getHand().get(handPosition), row, column);
        if (board.checkMove(move)) {
          board.putTile(move);
          getPlayer().getMoves().add(move);
          try {
            getPlayer().removeFromHand(getPlayer().getHand().get(handPosition));
          } catch (TileNotInHandException e) {
            // TODO Auto-generated catch block
            e.printStackTrace();
          }
        }
      }
    }
  }

  private void determineTile() {
    state = 2;
    handPosition = 0;
    decided = false;
    while (!decided) {
      Printer.printBoard(this, handPosition);
      keyTyped();
    }
  }

  private void determineMoveType() {
    state = 1;
    turnType = 1;
    decided = false;
    while (!decided) {
      if (turnType == 1) {
        Printer.printBoard(this);
        System.out.println("+----+");
        System.out.println("|MOVE|  SWAP");
        System.out.println("+----+");
      } else {
        Printer.printBoard(this);
        System.out.println("       +----+");
        System.out.println(" MOVE  |SWAP|");
        System.out.println("       +----+");
      }
      keyTyped();
    }
  }

  /**
   * Gets called when it is an opponents turn.
   * @param moves The moves the opponent made.
   */
  public void opponentTurn(List<Move> moves, Player player) {
    for (Move move : moves) {
      //Place all the moves on the board.
      board.putTile(move);
      if (getPool() > 0) {
        setPool(getPool() - 1);
      }
    }
    //Get score
    int score = 0;
    if (board.getMoveList().size() != 0) {
      score = board.getScoreCurrentTurn();
    } 
    player.setScore(player.getScore() + score);
    Printer.printBoard(this);
    //Reset board counters.
    board.endTurn();
  }

  /**
   * Gets called when it is the players turn. More than one move can be done in one turn.
   */
  public void makeMove() {
    Move move = null;
    try {
      //Get the user-input and convert it to a move;
      move = player.determineMove(board);
      //If the move is of the type MOVE put the tile on the board.
      if (move.getType().equals(Type.MOVE)) {
        board.putTile(move);
        //If it is of the type END, end the turn
      } else if (move.getType().equals(Type.END)) {
        setPlayerTurn(false);
      }
    } catch (InvalidMoveException e) {
      Printer.print(e);
    }
  }

  /**
   * Gets called when the turn is over.
   */
  public void endTurn() {
    String command;
    //Compile the command.
    if (player.getMoves().size() > 0) {
      String listType = player.getMoves().get(0).getType().toString();
      command = listType + " ";
      if (listType == MOVE) {
        for (Move move : player.getMoves()) {
          command = command + move.getTile().toString() 
              + " " + move.getRow() + " " + move.getColumn() + " ";
        }
      } else if (listType == SWAP) {
        for (Move move : player.getMoves()) {
          command = command + move.getTile().toString() + " ";
          setPool(getPool() + 1);
        }
      }
      player.setMoves(new ArrayList<Move>());
    } else {
      command = MOVE + "empty";
    }
    //Send the command to server.
    client.sendMessage(command);
    //Reset the board counters.
    board.endTurn();
  }
  
  /**
   * Print the scores.
   */
  public void printScores() {
    for (Player player : playerList) {
      Printer.print(player.getName() + "'s score is: " + player.getScore());
    }
  }
  
  public void addPlayerToList(Player player) {
    playerList.add(player);
  }

  public Player getPlayer() {
    return player;
  }
  
  /**
   * Get player with specific ID.
   * @param nr The player ID.
   * @return The player.
   */
  public Player getPlayerWithNumber(int nr) {
    Player result = null;
    for (Player player : playerList) {
      if (player.getPlayerNumber() == nr) {
        result = player;
      }
    }
    return result;
  }
  
  /**
   * Determines a hint for the human player.
   */
  public Move getHint() {
    return hintGen.getHint(board, player.getHand());
  }

  public void setPlayer(Player player) {
    this.player = player;
  }

  public Board getBoard() {
    return board;
  }

  public void setBoard(Board board) {
    this.board = board;
  }

  public List<Player> getPlayerList() {
    return playerList;
  }

  public void setPlayerList(List<Player> playerList) {
    this.playerList = playerList;
  }
  
  public int getPool() {
    return pool;
  }

  public void setPool(int pool) {
    this.pool = pool;
  }

  public String getPlayerType() {
    return playerType;
  }

  public void setPlayerType(String playerType) {
    this.playerType = playerType;
  }

  public void setPlayerTurn(boolean bool) {
    playerTurn = bool;
  }

  public NaiveStrategy getHintGen() {
    return hintGen;
  }

  public void setHintGen(NaiveStrategy hintGen) {
    this.hintGen = hintGen;
  }
  
  public void keyTyped() {
    int readCharacter = 0;
    try {
      readCharacter = jline.Terminal.getTerminal().readCharacter(System.in);
    } catch (IOException e2) {
      // TODO Auto-generated catch block
      e2.printStackTrace();
    }
    
    int a = 97;
    int d = 100;
    int w = 119;
    int s = 115;
    int e = 101;
    if (Game.state == 1) {
      if (readCharacter == a) {
        Game.turnType = 1;
      } else if (readCharacter == d) {
        Game.turnType = 2;
      } else if (readCharacter == e) {
        Game.decided = true;
        Game.state = 0;
      }
    } else if (Game.state == 2) {
      if (readCharacter == a) {
        if (Game.handPosition != 0) {
          Game.handPosition = Game.handPosition - 1;
        } else {
          Game.handPosition = getPlayer().getHand().size();
        }
      } else if (readCharacter == d) {
        if (Game.handPosition != getPlayer().getHand().size()) {
          Game.handPosition = Game.handPosition + 1;
        } else {
          Game.handPosition = 0;
        }
      } else if (readCharacter == e) {
        Game.decided = true;
        Game.state = 0;
      }
    } else if (Game.state == 3){
      List<ArrayList<Integer>> margins = getBoard().getMargins();
      int columnMin = margins.get(1).get(0);
      int columnMax = margins.get(1).get(1);
      int rowMin = margins.get(0).get(0);
      int rowMax = margins.get(0).get(1);
      if (readCharacter == a) {
        if (Game.column != columnMin) {
          Game.column = Game.column - 1;
        } else {
          Game.column = columnMax;
        }
      } else if (readCharacter == d) {
        if (Game.column != columnMax) {
          Game.column = Game.column + 1;
        } else {
          Game.column = columnMin;
        }
      } else if (readCharacter == s) {
        if (Game.row != rowMax) {
          Game.row = Game.row + 1;
        } else {
          Game.row = rowMin;
        }
      } else if (readCharacter == w) {
        if (Game.row != rowMin) {
          Game.row = Game.row - 1;
        } else {
          Game.row = rowMax;
        }
      } else if (readCharacter == e) {
        Game.decided = true;
      }
    }
  }
}
