package cora.rwinduction.engine;

import charlie.reader.CoraInputReader;
import charlie.trs.TRS;
import charlie.util.Pair;
import cora.io.DefaultOutputModule;
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

//  Prover prover =
//    new Prover(new ProverContext(trs, DefaultOutputModule.createUnicodeModule(trs)));

  @Test
  void run() {
    String c = "simplify 1 0.256 with [ x := f(x) ]";
    String[] splitWith = c.trim().split("\\s with \\s");

//    System.out.println(Arrays.toString(c.trim().split("with")));

    Pattern p = Pattern.compile("\\s*(simplify)\\s*(\\d)\\s*(.*)\\s*with\\s*");
    Matcher m = p.matcher(c);

    System.out.println(m.groupCount());

    for (int i = 1; i <= m.groupCount(); i++) {
      if (m.find()) {
        System.out.println(m.group(i) + i);
      }
    }
  }

  @Test
  void testCommandRegex() {

    String cmdFullTest = "simplify 0 0   2.3.4 with [ x := f(x) ]";

    Optional<String[]> result =
      CommandSimplify.splitStringRegex(CommandSimplify.cmdRegexComplete, cmdFullTest);

    result.ifPresent(x -> System.out.println(Arrays.toString(x)));


  }

  @Test
  void testSubstitutionRegex() {

    final String substTest = "x1 := f x ; xn := tn";

    Optional<List<Pair<String, String>>> t =
      CommandSimplify.splitSubst(substTest);

    t.ifPresent(System.out::println);

  }

}
