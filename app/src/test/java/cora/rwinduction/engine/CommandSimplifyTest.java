package cora.rwinduction.engine;

import charlie.reader.CoraInputReader;
import charlie.terms.Renaming;
import charlie.terms.Term;
import charlie.trs.TRS;
import charlie.util.Pair;
import com.google.common.collect.ImmutableList;
import cora.io.DefaultOutputModule;
import cora.io.OutputModule;
import cora.rwinduction.engine.data.Equation;
import cora.rwinduction.engine.data.ProverContext;
import org.junit.jupiter.api.Test;

import java.util.Arrays;
import java.util.List;
import java.util.Optional;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

class CommandSimplifyTest {

  TRS trs = CoraInputReader.readTrsFromString (
    "sum :: Int -> Int\n" +
      "sum(x) -> 0         | x ≤ 0\n" +
      "sum(x) -> x + sum(x - 1) | x > 0"
  );

  OutputModule outputModule =
    DefaultOutputModule.createUnicodeModule(trs);

  Term lhs = CoraInputReader.readTerm("sum(x)", trs);
  Term rhs = CoraInputReader.readTerm("sum(y)", trs);
  Term ctr = CoraInputReader.readTerm("true", trs);

  Renaming eqRenaming =
    outputModule.queryTermPrinter().generateUniqueNaming(lhs, rhs, ctr);

  Equation eq = new Equation(lhs, rhs, ctr, eqRenaming);

  Prover prover =
    new Prover(new ProverContext(trs, ImmutableList.of(eq), outputModule));

  @Test
  void run() {
    outputModule.print("%a = %a | %a", lhs, rhs, ctr);
  }

  @Test
  void testCommandRegex() {

    String cmdFullTest = "simplify 0 0   2.3.4 with [ x := f(x) ]";

    CommandSimplify commandSimplify = new CommandSimplify();
    commandSimplify.run(prover, cmdFullTest);

    Optional<String[]> result =
      CommandSimplify.splitStringRegex(CommandSimplify.cmdRegexComplete, cmdFullTest);

//    result.ifPresent(x -> System.out.println(Arrays.toString(x)));


  }

  @Test
  void testSubstitutionRegex() {

    final String substTest = "x1 := f x ; xn := tn";

    Optional<List<Pair<String, String>>> t =
      CommandSimplify.splitSubst(substTest);

    t.ifPresent(System.out::println);

  }

}
