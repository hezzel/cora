package cora.rwinduction.engine;

import charlie.terms.Term;

class Equation {
  private Term _lhs;
  private Term _rhs;
  private Term _constraint;

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
