package cora.rwinduction.engine;

import java.util.function.Consumer;

class ActionsStatics {

  static Consumer<String[]> forceQuit = _ -> {
    System.exit(0);
  };

  static Consumer<String[]> quitAskNoSave = args -> {
    if(args.length == 2 && args[1].equalsIgnoreCase("y")) {
      System.exit(0);
    }
  };

}
