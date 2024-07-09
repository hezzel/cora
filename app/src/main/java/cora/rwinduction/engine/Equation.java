package cora.rwinduction.engine;

import charlie.terms.Term;

class Equation {
  private Term _lhs;
  private Term _rhs;
  private Term _constraint;

  Equation(Term lhs, Term rhs, Term constraint) {
    _lhs = lhs;
    _rhs = rhs;
    _constraint = constraint;
  }

  Term getLhs() {
    return _lhs;
  }

  Term getRhs() {
    return _rhs;
  }

  Term getConstraint() {
    return _constraint;
  }

}
