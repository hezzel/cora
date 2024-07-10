package cora.rwinduction.tui;

import java.util.function.Consumer;

public class REPL {

  String quit = ":quit";

  // The interpreter reads the expression and decides... well, how to interpret it.
  Consumer<String> interpreter = expression -> {
    if (quit.equals(expression)) {
      System.exit(0);
    } else {
      System.out.println("> " + expression);
    }
  };

  public void runRepl() {

    KeyStrokeListener keyStrokeListener = new KeyStrokeListener();
    keyStrokeListener.test();

  }
}
