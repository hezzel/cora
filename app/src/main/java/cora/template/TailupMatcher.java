/**************************************************************************************************
 Copyright 2025 Cynthia Kop & Liye Guo

 Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 in compliance with the License.
 You may obtain a copy of the License at

 http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software distributed under the
 License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 express or implied.
 See the License for the specific language governing permissions and limitations under the License.
 *************************************************************************************************/

package cora.template;

import charlie.exceptions.IndexingException;
import charlie.smt.Addition;
import charlie.smt.Constraint;
import charlie.smt.Geq0;
import charlie.smt.IValue;
import charlie.smt.IVar;
import charlie.smt.SmtFactory;
import charlie.terms.FunctionSymbol;
import charlie.terms.Substitution;
import charlie.terms.Term;
import charlie.terms.TermFactory;
import charlie.terms.TheoryFactory;
import charlie.terms.Variable;
import charlie.terms.position.Position;
import charlie.theorytranslation.TermSmtTranslator;
import charlie.trs.Rule;
import charlie.trs.TrsFactory;
import charlie.types.Type;
import charlie.types.TypeFactory;
import charlie.util.Pair;
import cora.rwinduction.engine.Equation;

import java.util.List;

/**
 * The Tailup template:
 * leftHandSide -> accumulator | loopVariable > upperBound
 * leftHandSide -> rightHandSide | loopVariable <= upperBound
 * where rightHandSide contains operatorDefinition.
 */
public class TailupMatcher implements TemplateMatcher {
  private Term _leftHandSide;
  private Variable _accumulator;
  private Variable _loopVariable;
  private Term _upperBound;
  private Term _operatorDefinition;

  private TailupMatcher() {}

  /**
   * Checks if there are exactly two rewrite rules and exactly one of them has a variable as its
   * right-hand side, then reorders the rules to make it the first.
   */
  private static Pair<Rule, Rule> reorderTwoRules(Iterable<Rule> rules) {
    var iter = rules.iterator();
    if (!iter.hasNext()) return null; // there is at least one rule
    var fst = iter.next();
    if (!iter.hasNext()) return null; // there are at least two rules
    var snd = iter.next();
    if (iter.hasNext()) return null;  // there are no more than two rules
    if (fst.queryRightSide().isVariable()) {
      if (snd.queryRightSide().isVariable()) return null;
      return new Pair<>(fst, snd);
    }
    else {
      if (!snd.queryRightSide().isVariable()) return null;
      return new Pair<>(snd, fst);
    }
  }

  /**
   * Checks if the left-hand sides are equal (modulo renaming) and satisfy certain conditions,
   * then stores a representative.
   * @return a substitution subst such that fst.queryLeftSide() subst = snd.queryLeftSide().
   */
  private Substitution setLeftHandSide(Rule fst, Rule snd) {
    _leftHandSide = snd.queryLeftSide();
    // The linearity of snd.queryLeftSide() implies the linearity of fst.queryLeftSide(), given
    // fst.queryLeftSide() subst = snd.queryLeftSide() and that subst maps variables to variables.
    if (!_leftHandSide.isLinear()) return null;
    // Likewise, it suffices to check only that fst.queryLeftSide() is a functional term.
    if (!fst.queryLeftSide().isFunctionalTerm()) return null;
    var subst = fst.queryLeftSide().match(_leftHandSide);
    if (subst == null) return null;
    // To ensure that the left-hand sides are equal modulo renaming, subst must map variables to
    // variables.  Because snd.queryLeftSide() is linear, subst is guaranteed to be injective.
    for (var x : subst.domain()) {
      if (!subst.get(x).isVariable()) return null;
    }
    return subst;
  }

  /**
   * Fetches the addends in an addition of form variable + value.
   */
  private static Pair<IVar, IValue> fetchAddends(Addition a) {
    if (a.numChildren() == 2) {
      if (a.queryChild(1) instanceof IVar) {
        if (a.queryChild(2) instanceof IValue) {
          return new Pair<>((IVar) a.queryChild(1), (IValue) a.queryChild(2));
        }
      }
      else if (a.queryChild(1) instanceof IValue) {
        if (a.queryChild(2) instanceof IVar) {
          return new Pair<>((IVar) a.queryChild(2), (IValue) a.queryChild(1));
        }
      }
    }
    return null;
  }

  /**
   * Determines the loop variable and the upper bound.
   * @param constraint should essentially have the form _loopVariable <= _upperBound.
   * @param translator must be the one in which constraint has been generated.
   * @return true if both components are determined successfully, and false otherwise.
   */
  private boolean setLoopVariableAndUpperBound(Constraint constraint, TermSmtTranslator translator) {
    if (!(constraint instanceof Geq0)) return false;
    // To make use of split(), we first add 0 to the integer expression.
    var splitExpr = ((Addition) SmtFactory.createAddition(
      ((Geq0) constraint).queryExpression(),
      SmtFactory.createValue(0)))
      .split();

    // The loop variable should occur in the negative part, which can be either _loopVariable or
    // _loopVariable + value.
    int shift = 0; // shift will eventually be added to the upper bound.
    if (splitExpr.snd() instanceof IVar) {
      _loopVariable = translator.getVarOfIVar((IVar) splitExpr.snd());
    }
    else if (splitExpr.snd() instanceof Addition) {
      Pair<IVar, IValue> addends = fetchAddends((Addition) splitExpr.snd());
      if (addends == null) return false;
      _loopVariable = translator.getVarOfIVar(addends.fst());
      shift -= addends.snd().queryValue();
    }
    else {
      return false;
    }
    if (_loopVariable.equals(_accumulator)) return false;

    // The positive part may contain a variable.
    Variable y = null;
    if (splitExpr.fst() instanceof IVar) {
      y = translator.getVarOfIVar((IVar) splitExpr.fst());
    }
    else if (splitExpr.fst() instanceof IValue) {
      shift += ((IValue) splitExpr.fst()).queryValue();
    }
    else if (splitExpr.fst() instanceof Addition) {
      Pair<IVar, IValue> addends = fetchAddends((Addition) splitExpr.fst());
      if (addends == null) return false;
      y = translator.getVarOfIVar(addends.fst());
      shift += addends.snd().queryValue();
    }
    else {
      return false;
    }

    if (y == null) {
      _upperBound = TheoryFactory.createValue(shift);
    }
    else {
      if (y.equals(_accumulator)) return false;
      if (shift == 0) {
        _upperBound = y;
      }
      else {
        _upperBound = TermFactory.createApp(
          TheoryFactory.plusSymbol,
          y,
          TheoryFactory.createValue(shift));
      }
    }
    return true;
  }

  /**
   * Determines the definition of the binary operator for the recursive step.
   * @return true if the definition is determined successfully, and false otherwise.
   */
  private boolean setOperatorDefinition(Term rightHandSide) {
    Pair<Term, Position> loopVariable = _leftHandSide.findSubterm(
      (t, p) -> t.equals(_loopVariable));
    if (loopVariable == null) return false;
    Pair<Term, Position> accumulator = _leftHandSide.findSubterm(
      (t, p) -> t.equals(_accumulator));
    if (accumulator == null) return false;

    Term loopVariableNew;
    Term accumulatorNew;
    try {
      loopVariableNew = rightHandSide.querySubterm(loopVariable.snd());
      accumulatorNew = rightHandSide.querySubterm(accumulator.snd());
    }
    catch (IndexingException e) {
      return false;
    }

    if (!loopVariableNew.equals(TermFactory.createApp(
      TheoryFactory.plusSymbol, _loopVariable, TheoryFactory.createValue(1)))
      && !loopVariableNew.equals(TermFactory.createApp(
      TheoryFactory.plusSymbol, TheoryFactory.createValue(1), _loopVariable))) {
      return false;
    }
    if (!_leftHandSide.equals(rightHandSide
      .replaceSubterm(loopVariable.snd(), _loopVariable)
      .replaceSubterm(accumulator.snd(), _accumulator))) {
      return false;
    }

    for (var x : accumulatorNew.vars()) {
      if (!x.equals(_accumulator) && !x.equals(_loopVariable)) return false;
    }
    _operatorDefinition = accumulatorNew;
    return true;
  }

  /**
   * The method testing for the Tailup template, publicly accessible.
   * @param rules collects the rewrite rules defining a certain function symbol.
   * @return a matcher object if the rules conform to the template, and null otherwise.
   */
  public static TailupMatcher match(Iterable<Rule> rules) {
    var rulePair = reorderTwoRules(rules);
    if (rulePair == null) return null;

    var matcher = new TailupMatcher();
    var subst = matcher.setLeftHandSide(rulePair.fst(), rulePair.snd());
    if (subst == null) return null;
    matcher._accumulator = (Variable) subst.get(rulePair.fst().queryRightSide().queryVariable());
    // matcher._accumulator is null if the right-hand side of rulePair.fst() does not occur on
    // the left-hand side
    if (matcher._accumulator == null) return null;

    var translator = new TermSmtTranslator();
    Constraint constraint = translator.translateConstraint(rulePair.snd().queryConstraint())
      .simplify();
    // If the constraint of rulePair.fst() contains any variable that does not occur on the
    // left-hand side of rulePair.fst(), the two are not equal either.
    if (!translator.translateConstraint(rulePair.fst().queryConstraint().substitute(subst))
      .negate().simplify().equals(constraint)) {
      return null;
    }
    if (!matcher.setLoopVariableAndUpperBound(constraint, translator)) return null;

    if (!matcher.setOperatorDefinition(rulePair.snd().queryRightSide())) return null;
    return matcher;
  }

  /**
   * Generates an equation and possibly an extra rewrite rule for rewriting induction.
   */
  public Pair<Equation, Rule> generateEquationAndRule() {
    Type typeOperator = TypeFactory.createArrow(
      TypeFactory.intSort,
      TypeFactory.createArrow(
        _accumulator.queryType(),
        _operatorDefinition.queryType()));
    FunctionSymbol funcTailup = TermFactory.createConstant(
      "_tailup",
      TypeFactory.createArrow(
        typeOperator,
        TypeFactory.createArrow(
          TypeFactory.intSort,
          TypeFactory.createArrow(
            TypeFactory.intSort,
            TypeFactory.createArrow(
              TypeFactory.intSort,
              TypeFactory.createArrow(
                _accumulator.queryType(),
                _leftHandSide.queryType()))))));

    FunctionSymbol f;
    Rule rule;
    if (_operatorDefinition.isFunctionalTerm()
      && _operatorDefinition.numberArguments() == 2
      && _operatorDefinition.queryArgument(1).equals(_loopVariable)
      && _operatorDefinition.queryArgument(2).equals(_accumulator)) {
      f = _operatorDefinition.queryRoot();
      rule = null;
    }
    else {
      f = TermFactory.createConstant("_f", typeOperator);
      rule = TrsFactory.createRule(
        TermFactory.createApp(f, _loopVariable, _accumulator),
        _operatorDefinition);
    }

    Variable x = TermFactory.createVar("_x", TypeFactory.intSort);
    Variable y = TermFactory.createVar("_y", TypeFactory.intSort);
    var equation = new Equation(
      _leftHandSide,
      TermFactory.createApp(funcTailup, List.of(f, _loopVariable, x, y, _accumulator)),
      TheoryFactory.createConjunction(
        TheoryFactory.createConjunction(
          TermFactory.createApp(TheoryFactory.leqSymbol, x, _loopVariable),
          TermFactory.createApp(TheoryFactory.leqSymbol, _loopVariable, y)),
        TheoryFactory.createEquality(y, _upperBound)));
    return new Pair<>(equation, rule);
  }
}
