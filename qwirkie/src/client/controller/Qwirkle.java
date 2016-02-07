package client.controller;

import client.view.Printer;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.net.InetAddress;
import java.net.UnknownHostException;
import java.text.DateFormat;
import java.text.SimpleDateFormat;
import java.util.Arrays;
import java.util.Date;
import java.util.List;

/**
 * The startup class for a new game.
 * @author Han Hollander
 */
public class Qwirkle { 
  
  private static BufferedReader reader = new BufferedReader(new InputStreamReader(System.in));
  private static String fileName;
  private static String playerType;
  private static String strategyType;
  private static String name;
  private static String addr;
  private static String portString;
  private static InetAddress host;
  private static int port;
  

  /**
   * Main method to run the game.
   * @param args args
   */
  public static synchronized void main(String[] args) {
    //Create a log name
    DateFormat df = new SimpleDateFormat("ddMMyyHHmmss");
    Date dateobj = new Date();
    fileName = df.format(dateobj);
    
    if (args.length == 4) {
      //If 4 arguments are given at startup.
      name = args[0];
      addr = args[1];
      try {
        host = InetAddress.getByName(addr);
      } catch (UnknownHostException e) {
        Printer.print("\nHost name not valid, please try again.\n");
      }
      portString = args[2];
      try {
        port = Integer.parseInt(portString);
      } catch (NumberFormatException e) {
        Printer.print("\nPort number not valid, please try again!\n");
      }
      playerType = args[3];
    } else if (args.length == 5) {
      //If 4 arguments are given at startup.
      name = args[0];
      addr = args[1];
      try {
        host = InetAddress.getByName(addr);
      } catch (UnknownHostException e) {
        Printer.print("\nHost name not valid, please try again.\n");
      }
      portString = args[2];
      try {
        port = Integer.parseInt(portString);
      } catch (NumberFormatException e) {
        Printer.print("\nPort number not valid, please try again!\n");
      }
      playerType = args[3];
      strategyType = args[4];
    } else {
      Printer.print("Welcome in Qwirkle");
      Printer.print("(only characters a-z A-Z and 1 to 16 characters long)");
      Printer.print("What is your name? \n");
      //Check for valid name
      boolean validName = false;
      while (!validName) {
        name = readInput();
        validName = isValidName(name);
        if (!validName) {
          Printer.print("\nName not valid, please try again." + "\n");
        }
      }
      Printer.print("\nServer IP-adress: \n");
      //Check for valid address
      boolean validAddress = false;
      while (!validAddress) {
        addr = readInput();
        try {
          host = InetAddress.getByName(addr);
          validAddress = true;
        } catch (UnknownHostException e) {
          Printer.print("\nHost name not valid, please try again.\n");
        }
      }
      Printer.print("\nServer port: \n");
      //Check for valid port
      boolean validPort = false;
      while (!validPort) {
        portString = readInput();
        try {
          port = Integer.parseInt(portString);
          validPort = true;
        } catch (NumberFormatException e) {
          Printer.print("\nPort number not valid, please try again!\n");
        }
        if (validPort && (port < 1 || port > 65535)) {
          validPort = false;
          Printer.print("\nPort number not valid, please try again!\n");
        }
      }
      Printer.print("\nBot: 'b', Human: 'h'\n");
      //Check for valid player type
      boolean validPlayerType = false;
      while (!validPlayerType) {
        playerType = readInput();
        if (playerType.equals("b") || playerType.equals("h")) {
          validPlayerType = true;
        }
        if (!validPlayerType) {
          Printer.print("\nPlayer type not valid, please try again." + "\n");
        }
      }
      if (playerType.equals("b")) {
        Printer.print("\nNaive: 'n', Smart: 's', SuperSmart: 'ss'");
        boolean validStratType = false;
        //Check for valid type
        while (!validStratType) {
          strategyType = readInput();
          if (strategyType.equals("n") || strategyType.equals("s") || strategyType.equals("ss")) {
            validStratType = true;
          }
          if (!validStratType) {
            Printer.print("\nStrategy type not valid, please try again." + "\n");
          }
        }
      }
    }
    
    //Start a new game.
    new Game(name, host, port);
  }
  
  /**
   * Read input from System.in.
   * @return The input.
   */
  public static String readInput() {
    String input = "";
    boolean validInput = false;
    while (!validInput) {
      try {
        input = reader.readLine();
      } catch (IOException e) {
        Printer.print("Could not read line.");
      }
      validInput = true;
    }
    return input;
  }
  
  /**
   * Checks if name is valid.
   * @param text The text
   * @return If the name is valid.
   */
  private static boolean isValidName(String text) {
    List<String> allowedChars = Arrays.asList("a", "b", "c", "d", "e", "f", "g", "h", "i", "j", 
        "k", "l", "m", "n", "o", "p", "q", "r", "s", "t", "u", "v", "w", "x", "y", "z", "A", 
        "B", "C", "D", "E", "F", "G", "H", "I", "J", "K", "L", "M", "N", "O", "P", "Q", "R", 
        "S", "T", "U", "V", "W", "X", "Y", "Z");
    boolean result = true;
    String name = text;
    result = result && name.length() < 17;
    for (int i = 0; i < name.length(); i++) {
      result = result && allowedChars.contains(name.substring(i, i + 1));
    }
    return result;
  }

  public static String getFileName() {
    return fileName;
  }

  public static void setFileName(String fileName) {
    Qwirkle.fileName = fileName;
  }
  
  public static String getPlayerType() {
    return playerType;
  }
  
  public static String getStrategyType() {
    return strategyType;
  }
}
