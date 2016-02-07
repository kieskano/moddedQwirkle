package server.view;

import server.controller.Server;
import server.model.Game;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintStream;
import java.text.DateFormat;
import java.text.SimpleDateFormat;
import java.util.Date;
import java.util.Observable;
import java.util.Observer;
import java.util.Set;

public class TuiView implements Observer {

  public static final String PATH = "logs" + File.separator;
  
  private Server server;
  private PrintStream output;
  private String fileName;
  private File file;
  private BufferedWriter writer;
  
  /**
   * Creates a new Tuiview for the given server.
   * @param server Server
   */
  public TuiView(Server server) {
    this.server = server;
    output = System.out;
    
    DateFormat df = new SimpleDateFormat("ddMMyyHHmmss");
    Date dateobj = new Date();
    fileName = df.format(dateobj);
    file = new File(PATH + "s" + fileName + "game-" + this.server.getServerNr() + ".txt");
    if (!file.exists()) {
      try {
        file.createNewFile();
      } catch (IOException e) {
        System.out.println("Could not create new file.");
      }
    }
    writer = null;
    try {
      writer = new BufferedWriter(new FileWriter(file));
    } catch (IOException e) {
      System.out.println("Could not create writer.");
    }
  }
  
  /**
   * Prints a message to System.out with the number of the game server in front of the message.
   * @param msg Message
   */
  public void print(String msg) {
    output.println("Game-" + server.getServerNr() + ": " + msg);
    String[] lines = msg.split("\n");
    for (String line : lines) {
      try {
        writer.write(line);
        writer.newLine();
        writer.flush();
      } catch (IOException e) {
        output.println("Could not write to file.");
      }
    }
  }
  
  /**
   * Prints the board situation to System.out.
   */
  public void update(Observable observable, Object arg) {
    if (arg.equals("turn made")) {
      Game game = server.getGame();
      String situation = "\n" + "Current game situation" + "\n"
          + game.getBoard().toString() + "\n" + "Scores:" + "\n";
      //output.println("\n" + "Game " + server.getServerNr() + ": Current game situation");
      //output.println(game.getBoard().toString());
      //output.println("Scores:");
      Set<Integer> playerNrs = server.getPlayerNrs();
      for (int playerNr : playerNrs) {
        situation = situation + game.getPlayer(playerNr).getName() + ": " 
            + game.getPlayer(playerNr).getScore() + "\n";
      }
      situation = situation + "Hands:" + "\n";
      //output.println("Hands");
      for (int playerNr : playerNrs) {
        situation = situation + game.getPlayer(playerNr).getName() + ": " 
            + game.getPlayer(playerNr).getHand().toString() + "\n";
      }
      situation = situation + "Tiles in pool: " + server.getGame().getPoolSize() + "\n" + "\n";
      //output.println("Tiles in pool: " + server.getGame().getPoolSize() + "\n");
      print(situation);
      
    }
  }

}
