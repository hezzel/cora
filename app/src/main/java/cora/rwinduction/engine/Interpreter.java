package cora.rwinduction.engine;

import com.google.common.collect.ImmutableList;

import java.util.function.Consumer;

public class Interpreter {

  private static final ImmutableList<String> _actions =
    ImmutableList.<String>builder()
      .add(":quit")
      .build();

  public static Consumer<String> interpreter =
    args -> {
      if(args.equalsIgnoreCase(":quit")) {
        ActionsStatics.forceQuit.accept(args);
      }
    };

}
