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
 * MetaVariableEnvironment is an Environment of MetaVariables.  It is based on a ReplaceableList,
 * and essentially lists the MetaVariables occurring in that list.
 */
class MetaVariableEnvironment implements Environment<MetaVariable> {
  private final ReplaceableList _lst;

  /** Constructs an environment for the given list. */
  MetaVariableEnvironment(ReplaceableList lst) {
    _lst = lst;
  }

  /** Returns whether the given MetaVariable occurs in the underlying ReplaceableList. */
  public boolean contains(MetaVariable x) {
    return _lst.contains(x);
  }

  /** Returns the number of elements in the current environment. */
  public int size() {
    int counter = 0;
    for (MetaVariable x : this) { counter++; }
    return counter;
  }

  /** Returns an iterator over all variables in the environment. */
  public Iterator<MetaVariable> iterator() {
    return new Iterator<MetaVariable>() {
      private final Iterator<Replaceable> lstIterator = _lst.iterator();
      private MetaVariable nxt = null;

      private void loadNext() {
        while (nxt == null && lstIterator.hasNext()) {
          Replaceable n = lstIterator.next();
          if (n instanceof MetaVariable) nxt = (MetaVariable)n;
        }
      }

      @Override
      public boolean hasNext() {
        loadNext();
        return nxt != null;
      }

      @Override
      public MetaVariable next() {
        loadNext();
        if (nxt == null) throw new NoSuchElementException();
        MetaVariable ret = nxt;
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
