/**************************************************************************************************
 Copyright 2023--2024 Cynthia Kop

 Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 in compliance with the License.
 You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software distributed under the
 License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 express or implied.
 See the License for the specific language governing permissions and limitations under the License.
 *************************************************************************************************/

package charlie.terms;

import java.util.Iterator;
import java.util.NoSuchElementException;

/**
 * VariableEnvironment is an Environment of Variables.  It is based on a ReplaceableList, and
 * essentially lists the Variables occurring in that list.
 */
class VariableEnvironment implements Environment<Variable> {
  private final ReplaceableList _lst;

  /** Constructs an environment for the given list. */
  VariableEnvironment(ReplaceableList lst) {
    _lst = lst;
  }

  /** Returns whether the given Variable occurs in the underlying ReplaceableList. */
  public boolean contains(Variable x) {
    return _lst.contains(x);
  }

  /** Returns the number of elements in the current environment. */
  public int size() {
    int counter = 0;
    for (Variable x : this) { counter++; }
    return counter;
  }

  /** Returns an iterator over all variables in the environment. */
  public Iterator<Variable> iterator() {
    return new Iterator<Variable>() {
      private final Iterator<Replaceable> lstIterator = _lst.iterator();
      private Variable nxt = null;

      private void loadNext() {
        while (nxt == null && lstIterator.hasNext()) {
          Replaceable n = lstIterator.next();
          if (n instanceof Variable) nxt = (Variable)n;
        }
      }

      @Override
      public boolean hasNext() {
        loadNext();
        return nxt != null;
      }

      @Override
      public Variable next() {
        loadNext();
        if (nxt == null) throw new NoSuchElementException();
        Variable ret = nxt;
        nxt = null;
        return ret;
      }

      @Override
      public void remove() {
        throw new UnsupportedOperationException();
      }
    };
  }
}
