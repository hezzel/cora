package cora.rwinduction.engine;

import charlie.util.Pair;
import charlie.util.either.Either;
import charlie.util.either.Left;
import charlie.util.either.Right;
import com.google.common.collect.ImmutableList;
import cora.rwinduction.engine.data.ProofState;
import cora.rwinduction.engine.deduction.DeductionArguments;
import cora.rwinduction.engine.deduction.DeductionDelete;
import org.jetbrains.annotations.NotNull;

public class CommandDeleteRule implements Command {

  private @NotNull Either<String, Boolean> runAux(Prover prover,
                                                  @NotNull DeductionDelete deleteRule,
                                                  DeductionArguments decArgs,
                                                  String cmdLiteral) {

    Either<String, ProofState> decResult = deleteRule.applyRule(decArgs);

    return switch (decResult) {
      case Left<String, ProofState>(String err) -> new Left<>(err);
      case Right<String, ProofState>(ProofState nextProofState) -> {
        prover.getProverContext().addProofStep(nextProofState, cmdLiteral);
        yield new Right<>(true);
      }
    };
  }

  @Override
  public Either<String, Boolean> run(Prover prover, String args) {
    DeductionDelete deleteRule = new DeductionDelete();
    String[] split = CommandParser.split(args);

    // Process each way of calling this command.
    // In this case the command is called without any integer argument:
    // which means that delete is applied in the first equation in the list.
    // This is considered to be the index 0.
    if(split.length == 1 && split[0].equalsIgnoreCase("delete")) {

      DeductionArguments decArgs =
        new DeductionArguments(
          prover.getProverContext().getProofState(),
          0
        );

      return runAux(prover, deleteRule, decArgs, "delete");
    }

    if (split.length == 2 && split[0].equalsIgnoreCase("delete")) {
      try {
        int ruleIndex = Integer.parseInt(split[1]);

        DeductionArguments decArgs = new DeductionArguments(
          prover.getProverContext().getProofState(),
          ruleIndex
        );

        return runAux(prover, deleteRule, decArgs, "delete");

      } catch (NumberFormatException e) {
        return new Left<>("Invalid rule index: " + split[1] + "." +
          "Please provide a number as argument for the delete command.");
      }
    }

    if (!split[0].equalsIgnoreCase("delete")) {
      return new Left<>("Wrong command name syntax. " +
        "You should call this command using the name 'delete'.");
    }

    if (split.length == 0 || split.length > 2) {
      return new Left<>("Command cannot be applied. Wrong number of arguments.");
    }

    return new Left<>("Hell got loose...");
  }

  @Override
  public String descriptor() {
    return "applies the the delete deduction rule to the current proof state";
  }

  @Override
  public ImmutableList<Pair<String, String>> callDescriptor() {
    return ImmutableList.of(
      new Pair<>("delete <index>", "TODO"),
      new Pair<>("delete", "TODO")
    );
  }

  @Override
  public ImmutableList<String> argDescriptor() {
    return null;
  }
}
