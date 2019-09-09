/**************************************************************************************************
 Copyright 2019 Cynthia Kop

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
import cora.interfaces.types.Type;
import cora.interfaces.terms.FunctionSymbol;
import cora.interfaces.terms.Position;
import cora.interfaces.terms.Term;
import cora.interfaces.terms.Variable;
import cora.interfaces.terms.Substitution;
import cora.exceptions.IndexingError;
import cora.exceptions.NullCallError;
import cora.exceptions.NullInitialisationError;
import cora.terms.positions.EmptyPosition;

/**
 * A "leaf term" is any term that does not have strict subterms, such as variables or constants.
 * This inherit provides default functionality for such terms.
 */

abstract class LeafTermInherit extends TermInherit implements Term {
  private Type _type;

  public abstract TermKind queryTermKind();
  public abstract FunctionSymbol queryRoot();
  public abstract Variable queryVariable();
  public abstract Term substitute(Substitution gamma);
  public abstract String toString();

  /** Helper function to return the current classname for use in Errors. */
  private String queryMyClassName() {
    return "TermInherit (" + this.getClass().getSimpleName() + ")";
  }

  protected LeafTermInherit(Type type) {
    if (type == null) throw new NullInitialisationError(queryMyClassName(), "type");
    _type = type;
  }

  public Type queryType() {
    return _type;
  }

  public boolean queryFirstOrder() {
    return _type.queryTypeKind() == Type.TypeKind.BASETYPE;
  }

  /** @return 0, since leaf terms do not have immediate subterms */
  public int numberImmediateSubterms() {
    return 0;
  }
  
  /** @throws IndexingError, as a leaf term does not have immediate subterms */
  public Term queryImmediateSubterm(int i) {
    throw new IndexingError(queryMyClassName(), "queryImmediateSubterm", i); 
  }

  /** @return a list containing only the empty Position. */
  public ArrayList<Position> queryAllPositions() {
    ArrayList<Position> ret = new ArrayList<Position>();
    ret.add(new EmptyPosition());
    return ret;
  }

  /** @return this if the position is empty; otherwise throws an IndexingError */
  public Term querySubterm(Position pos) {
    if (pos.isEmpty()) return this;
    throw new IndexingError(queryMyClassName(), "querySubterm", toString(), pos.toString());
  }

  /** @return the replacement if pos is the empty position; otherwise throws an IndexingError */
  public Term replaceSubterm(Position pos, Term replacement) {
    if (pos.isEmpty()) return replacement;
    throw new IndexingError("Var", "replaceSubterm", toString(), pos.toString());
  }
}

