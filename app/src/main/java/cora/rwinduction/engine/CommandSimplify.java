package cora.rwinduction.engine;

import charlie.reader.CoraInputReader;
import charlie.terms.*;
import charlie.trs.TRS;
import charlie.util.Pair;
import charlie.util.either.Either;
import charlie.util.either.Left;
import charlie.util.either.Right;
import com.google.common.collect.ImmutableList;
import java.util.ArrayList;
import java.util.List;
import java.util.Optional;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

public class CommandSimplify implements Command {

  // Command Parsing utilities
  // ----------------------------------------------------------------------------

  // simplify <eq_index> <rule_index> <pos> with <subst>, where <subst> := [ <string> ]
  final static String cmdRegexComplete =  "\\s*(?<cmd>simplify|simpl)\\s+(?<eqIndex>\\d+)\\s+" +
    "(?<ruleIndex>\\d+)\\s+(?<pos>[^a-z\\s\\?]+)\\s+with\\s+\\[(?<subst>.*)\\]\\s*";

  // simplify <rule_index> <pos> with <subst> where <subst> := [ <string> ]
  // in this case, the selected equation is the equation with index 0
  final static String cmdRegexNoEqIndex = "\\s*(?<cmd>simplify|simpl)\\s+(?<ruleIndex>\\d+)" +
    "\\s+(?<pos>[^a-z\\s\\?]+)\\s+with\\s+\\[(?<subst>.*)\\]\\s*";

  // simplify <rule_index> <pos>
  final static String regex = "\\s*(?<cmd>simplify|simpl)\\s+(?<ruleIndex>\\d+)\\s+" +
    "(?<pos>[^a-z\\s\\?]+)" +
    "\\s*";

  /**
   * If
   * @param regex
   * @param cmd
   * @return
   */
  static Optional<String[]> splitStringRegex(String regex, String cmd) {
    final Pattern pattern = Pattern.compile(regex, Pattern.MULTILINE);
    final Matcher matcher = pattern.matcher(cmd);

    if(matcher.matches()) {
      matcher.reset();

      String[] data = new String[matcher.groupCount()];

      while(matcher.find()) {
        for(int i = 1; i <= matcher.groupCount(); i++) {
          data[i - 1] = matcher.group(i).trim();
        }
      }
      return Optional.of(data);
    } else {
      return Optional.empty();
    }
  }

  static Optional<List<Pair<String, String>>> splitSubst(String subst) {
    final String regex = "\\s*(?<var>.*)\\s*:=\\s*(?<term>.*)";
    List<Pair<String, String>> ret = new ArrayList<>();

    String[] splitSubst = subst.trim().split("\\;");
    for (int i = 0; i < splitSubst.length; i++) {
      splitSubst[i] = splitSubst[i].trim();
    }

    for (String s : splitSubst) {
      Optional<String[]> splitAt =
        CommandSimplify.splitStringRegex(regex, s);
      if (splitAt.isPresent() && splitAt.get().length == 2) {
        ret.add(new Pair<>(splitAt.get()[0], splitAt.get()[1]));
      } else {
        return Optional.empty();
      }
    }
    return Optional.of(ret);
  }

  static Either<String, Pair<Renaming, Substitution>> computeSubst(Prover prover,
                                                   int ruleIndex,
                                                   int equationIndex,
                                                   String subst) {
    Renaming ruleRenaming = prover
      .getProverContext()
      .getRuleRenaming(ruleIndex);

    Renaming newRenaming = prover
      .getProverContext()
      .getProofState()
      .getEquations()
      .get(equationIndex)
      .getVarNaming()
      .copy();

    TRS trs = prover
      .getProverContext()
      .getProofState()
      .getTRS();

    Substitution sub = TermFactory.createEmptySubstitution();

    Optional<List<Pair<String, String>>> mappings = splitSubst(subst);

    if(mappings.isPresent()) {
      List<Pair<String, String>> mapping = mappings.get();
      for (Pair<String, String> pair : mapping) {
        Variable x = ruleRenaming.getVariable(pair.fst());
        if (x == null) {
          return new Left<>("Variable " + pair.fst() + " out of scope.");
        } else {
          Term t = CoraInputReader
            .readTerm(pair.snd(), newRenaming, true, trs);
          sub.extend(x, t);
        }
      }
      return new Right<>(new Pair<>(newRenaming, sub));
    } else {
      return new Left("Cannot parse substitution. The argument [" + sub + "] is not a valid " +
        "substitution");
    }
  }

  // ----------------------------------------------------------------------------------------------



  @Override
  public Either<String, Boolean> run(Prover prover, String args) {
    return null;
  }

  @Override
  public String descriptor() {
    return "";
  }

  @Override
  public ImmutableList<Pair<String, String>> callDescriptor() {
    return null;
  }

  @Override
  public ImmutableList<String> argDescriptor() {
    return null;
  }
}
