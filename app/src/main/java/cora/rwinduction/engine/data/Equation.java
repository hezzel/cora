package cora.rwinduction.engine.data;

import charlie.terms.Renaming;
import charlie.terms.Term;
import java.util.Objects;

/**
 * Data structure for equations.
 */
public class Equation {
  private Term _lhs;
  private Term _rhs;
  private Term _constraint;
  private Renaming _varNaming;

  public Equation(Term lhs, Term rhs, Term constraint, Renaming varNaming) {
    Objects.requireNonNull(lhs);
    Objects.requireNonNull(rhs);
    Objects.requireNonNull(constraint);
    Objects.requireNonNull(varNaming);

    _lhs = lhs;
    _rhs = rhs;
    _constraint = constraint;
    _varNaming = varNaming;
  }

  public Term getLhs() {
    return _lhs;
  }

  public Term getRhs() {
    return _rhs;
  }

  public Term getConstraint()   { return _constraint; }

  public Renaming getRenaming() { return _varNaming;  }

}
