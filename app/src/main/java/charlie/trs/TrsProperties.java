/**************************************************************************************************
 Copyright 2024 Cynthia Kop

 Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 in compliance with the License.
 You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software distributed under the
 License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 express or implied.
 See the License for the specific language governing permissions and limitations under the License.
 *************************************************************************************************/

package charlie.trs;

/**
 * This class lists the static properties that a TRS may have.
 * Use import charlie.trs.TrsProps.* for easy use in the corresponding functions.
 *
 * Note: DO NOT REORDER THE CONSTANTS IN THESE ENUMS.  The lower values are always the more
 * restrictive ones.
 */
public class TrsProperties {
  /**
   * The "level" of rules indicates the higher-order constructs that may be used in the term
   * formation of their left- and right-hand side (but not constraint, which is automatically
   * limited to first-order terms).
   */
  public enum Level {
    FIRSTORDER,     // only first-order terms
    APPLICATIVE,    // lambda-free terms
    LAMBDA,         // true terms (so potentially with lambda, but no meta-variables)
    META,           // meta-terms (allowing meta-variables)
  }

  /**
   * The "constrained" status of rules indicates whether rules are allowed to have a constraint,
   * and to use theory symbols.
   * This is all or nothing: either all pre-defined theories in Cora are supported, or none.
   */
  public enum Constrained { NO, YES }

  /** The type level of a TRS indicates the type system used for term formation and rules. */
  public enum TypeLevel {
    SIMPLE,         // simple types: built from sorts and the arrow operator
    SIMPLEPRODUCTS  // simple types along with products
  }

  /** The root status of rules gives restrictions on the left-hand sides of the rules. */
  public enum Root {
    FUNCTION,   // lhss are functional terms with a non-theory function symbol as root
    THEORY,     // lhss are functional terms, but their root is allowed to be a theory symbol
    ANY,        // lhss are not required to be functional terms
  }

  /** The pattern status of rules also gives restrictions on the left-hand sides of the rules. */
  public enum Lhs {
    PATTERN,      // the lhs of each rule must be a pattern
    SEMIPATTERN,  // the lhs of each rule must be a semi-pattern
    NONPATTERN,   // the lhs of rules is not required to be a pattern or semi-pattern
  }

  /** Should meta-variables in the rhs of a rule occur also in the left or constraint? */
  public enum FreshRight {
    NONE,   // meta-variables in the right-hand side should also occur in the left
    CVARS,  // meta-variables in the right-hand side should also occur in the left or the constraint
    ANY     // the right-hand side may have meat-variables that do not occur in left or constraint
  }

  /**
   * The constructions of terms permitted in a TRS may differ from the construction of its rules.
   * Hence, we sometimes also track specifically the properties admitted for rules.
   * The "term level" indicates whether terms should be first-order, applicative or true.
   * (Meta-terms are never allowed to occur outside of room formation.)
   */
  public enum TermLevel { FIRSTORDER, APPLICATIVE, LAMBDA }

  /**
   * This returns the level of terms that should be permitted to occur in a TRS with rules of the
   * given level. (This is essentially the same level, except that meta-variables never occur in
   * terms, as they are only meant to be used in matching.)
   */
  public static TermLevel translateRuleToTermLevel(Level level) {
    return switch (level) {
      case Level.FIRSTORDER -> TermLevel.FIRSTORDER;
      case Level.APPLICATIVE -> TermLevel.APPLICATIVE;
      case Level.LAMBDA -> TermLevel.LAMBDA;
      case level.META -> TermLevel.LAMBDA;
    };
  }
}

