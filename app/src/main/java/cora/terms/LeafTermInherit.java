/**************************************************************************************************
 Copyright 2019, 2022 Cynthia Kop

 Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 in compliance with the License.
 You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software distributed under the
 License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 express or implied.
 See the License for the specific language governing permissions and limitations under the License.
 *************************************************************************************************/

package cora.terms;

import java.util.ArrayList;
import java.util.Set;
import charlie.exceptions.*;
import charlie.util.Pair;
import charlie.types.Type;
import cora.terms.position.Position;

/**
 * A "leaf term" is any term that does not have strict subterms, such as variables or constants.
 * This inherit provides default functionality for such terms.
 */
abstract class LeafTermInherit extends TermInherit {
  private Type _type;

  protected LeafTermInherit(Type type) {
    if (type == null) throw new NullInitialisationError(queryMyClassName(), "type");
    _type = type;
  }

  public Type queryType() {
    return _type;
  }

  public boolean isPattern() {
    return true;
  }

  public boolean isSemiPattern() {
    return true;
  }

  /** if the current term is a function symbol, it is added to storage; otherwise nothing is done */
  public void storeFunctionSymbols(Set<FunctionSymbol> storage) {
    if (isFunctionalTerm()) storage.add(queryRoot());
  }

  /** @return a list containing only the current term with the empty Position. */
  public ArrayList<Pair<Term,Position>> querySubterms() {
    ArrayList<Pair<Term,Position>> ret = new ArrayList<Pair<Term,Position>>();
    ret.add(new Pair<Term,Position>(this, Position.empty));
    return ret;
  }

  /** Throws an error, since there are no non-empty positions in a leaf term */
  public Term querySubtermMain(Position pos) {
    throw new IndexingError(queryMyClassName(), "querySubterm", toString(), pos.toString());
  }

  /** Throws an error, since there are no non-empty positions in a leaf term */
  public Term replaceSubtermMain(Position pos, Term replacement) {
    throw new IndexingError(queryMyClassName(), "replaceSubterm", toString(), pos.toString());
  }
}

