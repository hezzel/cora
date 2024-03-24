/**************************************************************************************************
 Copyright 2023 Cynthia Kop

 Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 in compliance with the License.
 You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software distributed under the
 License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 express or implied.
 See the License for the specific language governing permissions and limitations under the License.
 *************************************************************************************************/

package cora.parser;

import com.google.common.collect.ImmutableList;
import java.util.ArrayList;
import java.util.Stack;
import java.util.TreeMap;
import charlie.exceptions.IllegalArgumentError;
import cora.parser.lib.Token;
import cora.parser.lib.ParsingStatus;
import cora.parser.Parser.ParserTerm;

/**
 * This class is used to translate a chain of the form
 *  <parserterm> <symbol> <parserterm> <symbol> ... <symbol> <parserterm>
 * into a single parserterm, taking associtivity and priorities into account.
 *
 * Note that this class is NOT public, because it is not intended to be used outside the parser
 * package.
 */
class InfixManager {
  private ArrayList<GroupInfo> _groups;
  private TreeMap<String,Integer> _symbols;

  static final int ASSOC_LEFT = 1;
  static final int ASSOC_RIGHT = 2;
  static final int ASSOC_NONE = 3;

  public record OperatorData(Token token, String name) {}
  record GroupInfo(int associativity, int priority) {}

  InfixManager() {
    _groups = new ArrayList<GroupInfo>();
    _symbols = new TreeMap<String,Integer>();
  }

  /**
   * To set up the infix manager, start by including all the groups.
   *
   * Associativity should be one of ASSOC_LEFT, ASSOC_RIGHT or ASSOC_NONE.
   * A higher priority indicates closer binding; e.g., * has higher priority than +.
   * Two opertors should be in the same group if they associate with each other; for example + and
   * - but not /\ and \/.
   */
  void addGroup(int associativity, int priority, String ...operators) {
    int index = _groups.size();
    _groups.add(new GroupInfo(associativity, priority));
    for (String o : operators) _symbols.put(o, index);
  }

  /**
   * This function provides the main functionality of the infix manager.
   * Given a sequence of N+1 terms (say, s{0},...,s{N}) and N operators (say op{1}, ..., op{N}),
   * generates a Parserterm corresponding to s{0} op{1} s{1} op{2} ... op{N-1} s{N-1} op{N} s{N},
   * taking the associativity and priorities of all operators into account.
   * If any of the given operators has a name that is not in one of the declared groups, then an
   * IllegalArgumentError is thrown.  This also happens if the lengths of the respective lists are
   * not as they should be.
   * If the chain does not (unambiguously) define a term (e.g., a /\ b \/ c, or a < b > c), then
   * an appropriate error is stored in the status.  The status is not otherwise used.
   */
  ParserTerm convertChain(ArrayList<ParserTerm> terms, ArrayList<OperatorData> operators,
                          ParsingStatus status) {
    // correctness checking
    if (terms.size() != operators.size() + 1) {
      throw new IllegalArgumentError("InfixManager", "convertChain", "list of terms has length " +
        terms.size() + " while list of operators has size " + operators.size());
    }
    for (int i = 0; i < operators.size(); i++) {
      if (!_symbols.containsKey(operators.get(i).name)) {
        throw new IllegalArgumentError("InfixManager", "convertChain", "unexpected operator: " +
          operators.get(i).token.getText());
      }
    }

    Stack<ParserTerm> tstack = new Stack<ParserTerm>();
    Stack<OperatorData> ostack = new Stack<OperatorData>();
    tstack.add(terms.get(0));

    for (int i = 0; i < operators.size(); i++) {
      OperatorData oi = operators.get(i);
      while (ostack.size() > 0) {
        OperatorData last = ostack.peek();
        int mygroup = _symbols.get(oi.name());
        int lastgroup = _symbols.get(last.name());
        boolean err = false;
        if (_groups.get(mygroup).priority() > _groups.get(lastgroup).priority) break;
        if (_groups.get(mygroup).priority() == _groups.get(lastgroup).priority) {
          if (mygroup == lastgroup) {
            if (_groups.get(mygroup).associativity() == ASSOC_RIGHT) break;
            if (_groups.get(mygroup).associativity() == ASSOC_NONE) {
              err = true;
              status.storeError("Illegal infix sequence: operator " + oi.token.getText() +
                " is not associative, so cannot be used after " + last.token.getText() +
                " (at position " +  last.token.getPosition() + ").", oi.token());
            }
          }
          else {
            err = true;
            status.storeError("Ambiguous infix sequence: operators " + last.token.getText() +
              " (at position " + last.token.getPosition() + ") and " + oi.token.getText() +
              " have the same precedence, but are not in the same group.  Please use brackets " +
              "to disambiguate.",  oi.token());
          }
        }
        applyTop(tstack, ostack);
        if (err) tstack.push(new Parser.PErr(tstack.pop()));
      }
      tstack.push(terms.get(i+1));
      ostack.push(oi);
    }
    while (!ostack.isEmpty()) applyTop(tstack, ostack);
    return tstack.pop();
  }

  /**
   * Helper function for convertchain: pops the top two terms of the term stack, and the top
   * operator from the operator stack, applies the operator to the terms, and pushes the result
   * back to the term stack
   */
  private void applyTop(Stack<ParserTerm> tstack, Stack<OperatorData> ostack) {
    OperatorData o = ostack.pop();
    ParserTerm b = tstack.pop();
    ParserTerm a = tstack.pop();
    ParserTerm head = new Parser.CalcSymbol(o.token(), o.name());
    ParserTerm result = new Parser.Application(a.token(), head, ImmutableList.of(a, b));
    tstack.push(result);
  }
}

