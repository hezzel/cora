package cora.rwinduction.engine.data;

import charlie.terms.Renaming;
import charlie.terms.Term;

public class Equation {
  private Term _lhs;
  private Term _rhs;
  private Term _constraint;
  private Renaming _varNaming;

  public Equation(Term lhs, Term rhs, Term constraint) {
    _lhs = lhs;
    _rhs = rhs;
    _constraint = constraint;
  }

  public Term getLhs() {
    return _lhs;
  }

  public Term getRhs() {
    return _rhs;
  }

  public Term getConstraint() {
    return _constraint;
  }

}
