package client.controller;

import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.awt.event.KeyEvent;
import java.util.ArrayList;
import java.util.List;

public class MyKeyListener implements java.awt.event.KeyListener {

  private Game game;
  
  public MyKeyListener(Game game) {
    this.game = game;
  }
  
  @Override
  public void keyTyped(KeyEvent e) {
    System.out.println("DINKIE");
    if (Game.state == 1) {
      if (e.getKeyChar() == KeyEvent.VK_LEFT) {
        Game.turnType = 1;
        synchronized (Game.waitForInput) {
          Game.waitForInput.notifyAll();
        }
      } else if (e.getKeyChar() == KeyEvent.VK_RIGHT) {
        Game.turnType = 2;
        synchronized (Game.waitForInput) {
          Game.waitForInput.notifyAll();
        }
      } else if (e.getKeyChar() == KeyEvent.VK_ENTER) {
        Game.decided = true;
        synchronized (Game.waitForInput) {
          Game.waitForInput.notifyAll();
        }
        Game.state = 0;
      }
    } else if (Game.state == 2) {
      if (e.getKeyChar() == KeyEvent.VK_LEFT) {
        if (Game.handPosition != 0) {
          Game.handPosition = Game.handPosition - 1;
          synchronized (Game.waitForInput) {
            Game.waitForInput.notifyAll();
          }
        }
      } else if (e.getKeyChar() == KeyEvent.VK_RIGHT) {
        if (Game.handPosition != game.getPlayer().getHand().size()) {
          Game.handPosition = Game.handPosition + 1;
          synchronized (Game.waitForInput) {
            Game.waitForInput.notifyAll();
          }
        }
      } else if (e.getKeyChar() == KeyEvent.VK_ENTER) {
        Game.decided = true;
        synchronized (Game.waitForInput) {
          Game.waitForInput.notifyAll();
        }
        Game.state = 0;
      }
    } else if (Game.state == 3){
      List<ArrayList<Integer>> margins = game.getBoard().getMargins();
      int columnMin = margins.get(1).get(0);
      int columnMax = margins.get(1).get(1);
      int rowMin = margins.get(0).get(0);
      int rowMax = margins.get(0).get(1);
      if (e.getKeyChar() == KeyEvent.VK_LEFT) {
        if (Game.column != columnMin) {
          Game.column = Game.column - 1;
          synchronized (Game.waitForInput) {
            Game.waitForInput.notifyAll();
          }
        }
      } else if (e.getKeyChar() == KeyEvent.VK_RIGHT) {
        if (Game.column != columnMax) {
          Game.column = Game.column + 1;
          synchronized (Game.waitForInput) {
            Game.waitForInput.notifyAll();
          }
        }
      } else if (e.getKeyChar() == KeyEvent.VK_UP) {
        if (Game.row != rowMax) {
          Game.row = Game.row + 1;
          synchronized (Game.waitForInput) {
            Game.waitForInput.notifyAll();
          }
        }
      } else if (e.getKeyChar() == KeyEvent.VK_RIGHT) {
        if (Game.row != rowMin) {
          Game.row = Game.row - 1;
          synchronized (Game.waitForInput) {
            Game.waitForInput.notifyAll();
          }
        }
      } else if (e.getKeyChar() == KeyEvent.VK_ENTER) {
        Game.decided = true;
        synchronized (Game.waitForInput) {
          Game.waitForInput.notifyAll();
        }
        Game.state = 0;
      }
    }
  }

  @Override
  public void keyPressed(KeyEvent e) {
  }

  @Override
  public void keyReleased(KeyEvent e) {
  }
}
