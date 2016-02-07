package client.model;

import client.controller.Game;
import client.model.Move.Type;
import client.view.Printer;
import exceptions.InvalidCommandException;
import exceptions.InvalidMoveException;
import exceptions.TileNotInHandException;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.util.Arrays;
import java.util.List;

/**
 * Human player class.
 * @author Han Hollander
 */
public class HumanPlayer extends Player {
  
  public static final String MOVEUSAGE = "Usage: [MOVE <tileNr> <row> <column>]";
  public static final String SWAPUSAGE = "Usage: [SWAP <tile>]";
  
  public static final List<String> COLOURS = Arrays.asList("R", "O", "B", "Y", "G", "P");
  public static final List<String> SHAPES = Arrays.asList("o", "d", "s", "c", "x", "*");
  
  private Type listType;

  /**
   * Constructor for a human.
   * @param name name of human
   * @param playerNumber nr of human
   */
  public HumanPlayer(String name, int playerNumber, Game game) {
    super(name, playerNumber);
  }
  
  /**
   * determine human move.
   * @param board board where move can take place
   * @return a valid move
   */
  public Move determineMove(Board board) throws InvalidMoveException {
    boolean validMove = false;
    Move move = null;
    while (!validMove) {
      if (getMoves().size() == 0) {
        listType = Type.ANY;
      } else {
        listType = getMoves().get(0).getType();
      }
      Printer.print("Type of turn: " + listType);
      try {
        //Get the move from user input
        move = getMove();
        //Check if move can be done with respect to earlier moves.
        if (move.getType().equals(Type.MOVE) 
            && (listType.equals(Type.ANY) || listType.equals(Type.MOVE))) {
          //Check if the move is valid.
          if (board.checkMove(move)) {
            try {
              removeFromHand(move.getTile());
            } catch (TileNotInHandException e) {
              Printer.print(e);
            }
            validMove = true;
            getMoves().add(move);
          } else {
            throw new InvalidMoveException("The move can not be done on the current board.");
          }
        //Again, check if move can be done.  
        } else if (move.getType().equals(Type.SWAP) 
            && (listType.equals(Type.ANY) || listType.equals(Type.SWAP))) {
          try {
            removeFromHand(move.getTile());
          } catch (TileNotInHandException e) {
            Printer.print(e);
          }
          validMove = true;
          getMoves().add(move);
        } else  if (move.getType().equals(Type.END)) {
          validMove = true;
        //If the move is not one of the above, or several kinds of moves are done in one turn.  
        } else {
          throw new InvalidMoveException("You can only make one type of move per turn.");
        }
      } catch (InvalidCommandException e) {
        Printer.print(e);
      }
    }
    return move;
  }
  
  /**
   * Verifies the command and returnes a newly made move.
   * @param input the command
   * @return a new move
   * @throws InvalidCommandException if the command is invalid
   */
  public Move verifyMove(String input) throws InvalidCommandException {
    boolean validInput = false;
    String[] command = null;
    Move move = null;
    //MOVE command
    if (input.startsWith("MOVE")) {
      //Validates the move format/command.
      validInput = validMoveCommand(input);
      if (validInput) {
        command = input.split(" ");
        int handIndex = Integer.parseInt(command[1]);
        int row = Integer.parseInt(command[2]);
        int column = Integer.parseInt(command[3]);
        move = new Move(getHand().get(handIndex - 1), row, column);   
      }
    //SWAP command
    } else if (input.startsWith("SWAP")) {
      //Validates the move format/command.
      validInput = validSwapCommand(input);
      if (validInput) {
        command = input.split(" ");
        Tile tile = getHand().get(Integer.parseInt(command[1]) - 1);
        move = new Move(tile);
      }
    //END command
    } else if (input.startsWith("END")) {
      //Validates the move format/command.
      validInput = validEndCommand(input);
      if (validInput) {
        move = new Move();
      }
    } else { 
      //Neither MOVE nor SWAP nor END move
      throw new InvalidCommandException(MOVEUSAGE + " " + SWAPUSAGE);
    }
    return move;
  }
  
  /**
   * Get input from console.
   * @return returns the command, only if move is valid
   * @throws InvalidCommandException no valid command tho
   */
  public Move getMove() throws InvalidCommandException {
    Move move = null;
    String input = "";
    BufferedReader reader = new BufferedReader(new InputStreamReader(System.in));
    while (move == null) {
      try {
        input = reader.readLine();
      } catch (IOException e) {
        Printer.print("Could not read line.");
      }
      //Verify the move before returning it.
      move = verifyMove(input);
    }
    return move;
  }
  
  /**
   * Check if move command is valid.
   * @param input input command
   * @return boolean if valid
   * @throws InvalidCommandException not valid
   */
  public boolean validMoveCommand(String input) throws InvalidCommandException {
    boolean validInput = false;
    String[] command = input.split(" "); 
    int handIndex = 0;
    if (command.length == 4) { 
      //Command length must be four
      try { 
        //Row and column must be integers
        handIndex = Integer.parseInt(command[1]);
        Integer.parseInt(command[2]);
        Integer.parseInt(command[3]);
      } catch (NumberFormatException e) { 
        //Throw exception if row or column are invalid
        throw new InvalidCommandException(MOVEUSAGE);
      }
      Tile tile = null;
      try {
        tile = getHand().get(handIndex - 1);
      } catch (IndexOutOfBoundsException e) {
        throw new InvalidCommandException(MOVEUSAGE);
      } 
      String colour = tile.getColor();
      String shape = tile.getShape();
      if (COLOURS.contains(colour) && SHAPES.contains(shape)) { 
        //Colour and shape must exist.
        validInput = true;
      } else { 
        //Invalid colour and shape.
        throw new InvalidCommandException("Colours: " + COLOURS + ", shapes: " + SHAPES);
      }
    } else { 
      //Throw exception if command lenght is not four
      throw new InvalidCommandException(MOVEUSAGE);
    }
    validInput = true;
    return validInput;
  }
  
  /**
   * Check if move command is valid.
   * @param input input command
   * @return boolean if valid
   * @throws InvalidCommandException not valid
   */
  public boolean validSwapCommand(String input) throws InvalidCommandException {
    boolean validInput = false;
    int tileNr = -1;
    String[] command = input.split(" ");
    if (command.length == 2) { 
      //Command length must be 2.
      try {
        tileNr = Integer.parseInt(command[1]);
      } catch (NumberFormatException e) {
        Printer.print(e);
      }
      Tile tile = null;
      try {
        tile = getHand().get(tileNr - 1);
      } catch (IndexOutOfBoundsException e) {
        throw new InvalidCommandException(SWAPUSAGE);
      }
      String colour = tile.getColor();
      String shape = tile.getShape();
      if (COLOURS.contains(colour) && SHAPES.contains(shape)) { 
        //Colour and shape must exist.
        validInput = true;
      } else { 
        //Invalid colour and shape.
        throw new InvalidCommandException("Colours: " + COLOURS + ", shapes: " + SHAPES);
      }
    } else { 
      //Invalid command usage.
      throw new InvalidCommandException(SWAPUSAGE);
    }
    return validInput;
  }
  
  /**
   * Checks if valid endcommand.
   * @param input input
   * @return if valid
   * @throws InvalidCommandException if not valid
   */
  public boolean validEndCommand(String input) throws InvalidCommandException {
    boolean validInput = false;
    if (input.length() == 3) { 
      validInput = true;
    } else {
      throw new InvalidCommandException("Usage: END.");
    }
    return validInput;
  }
  
  public Type getListType() {
    return listType;
  }
  
  public void setListType(Type type) {
    listType = type;
  }
  
}
