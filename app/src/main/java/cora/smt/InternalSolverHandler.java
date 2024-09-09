package cora.smt;

import charlie.types.TypeFactory;
import charlie.terms.Term;
import charlie.terms.Substitution;
import charlie.terms.Variable;
import charlie.smt.SmtProblem;
import charlie.smt.SmtSolver;
import charlie.smt.Valuation;
import charlie.theorytranslation.TermAnalyser;
import cora.io.OutputModule;
import cora.io.ProofObject;

public class InternalSolverHandler {
  public static ProofObject proveSatisfiability(Term term) {
    TermAnalyser.Result result = TermAnalyser.satisfy(term, new InternalSolver());
    return new SmtSolutionObject(term, result);
  }

  private static class SmtSolutionObject implements ProofObject {
    Term _original;
    TermAnalyser.Result _answer;

    SmtSolutionObject(Term orig, TermAnalyser.Result answer) {
      _original = orig;
      _answer = answer;
    }

    public Answer queryAnswer() {
      return switch (_answer) {
        case TermAnalyser.Result.YES(Substitution val) -> ProofObject.Answer.YES;
        case TermAnalyser.Result.NO() -> ProofObject.Answer.NO;
        case TermAnalyser.Result.MAYBE(String reason) -> ProofObject.Answer.MAYBE;
      };
    }

    public void justify(OutputModule output) {
      switch (_answer) {
        case TermAnalyser.Result.YES(Substitution substitution):
          printSubstitution(output, _original, substitution);
          break;
        case TermAnalyser.Result.MAYBE(String reason):
          output.println(reason);
          break;
        case TermAnalyser.Result.NO():
          output.println("The internal prover has verified that there is no " +
            "valuation satisfying these constraints.");
      }
    }
  }

  private static void printSubstitution(OutputModule module, Term original, Substitution subst) {
    module.startTable();
    for (Variable x : original.vars()) {
      module.nextColumn(x.toString());
      module.println(subst.get(x).toString());
    }
    module.endTable();
  }
}
