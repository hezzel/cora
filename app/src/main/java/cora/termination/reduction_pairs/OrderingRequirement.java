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

package cora.termination.reduction_pairs;

import com.google.common.collect.ImmutableList;
import java.util.List;

import charlie.util.Pair;
import charlie.terms.Term;
import charlie.terms.TermPrinter.Renaming;
import cora.io.OutputModule;

/**
 * An OrderingRequirement is a conditional requirement left R right [constraint], where R is one of
 * ≻, ≽ or "either".  It is particularly used in an OrderingProblem.
 */
public record OrderingRequirement(Term left, Term right, Term constraint, Relation rel) {
  public enum Relation { Strict, Weak, Either }

  /**
   * Prints the current requirement to the given module (within the current paragraph or column;
   * no structural commands are used, so this can safely be added in the middle of a sentence).
   */
  public void printTo(OutputModule module) {
    Renaming naming = module.queryTermPrinter().generateUniqueNaming(left, right, constraint);
    String relation = switch (rel) {
      case Strict -> "%{succ}";
      case Weak -> "%{succeq}";
      case Either -> "%{succ}?";
    };
    Pair<Term,Renaming> l = new Pair<Term,Renaming>(left, naming);
    Pair<Term,Renaming> r = new Pair<Term,Renaming>(right, naming);
    Pair<Term,Renaming> c = new Pair<Term,Renaming>(constraint, naming);
    if (constraint.isValue() && constraint.toValue().getBool()) {
      module.print("%a " + relation + " %a", l, r);
    }
    else module.print("%a " + relation + " %a | %a", l, r, c);
  }
  
  /** Should only be used for debug output (and is deliberately ugly to make that clera) */
  public String toString() {
    return left.toString() + " " + rel + " " + right.toString() + " | " + constraint.toString();
  }
}

