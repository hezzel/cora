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

import java.util.List;
import java.util.ArrayList;
import cora.exceptions.IndexingError;
import cora.exceptions.NullCallError;
import cora.exceptions.NullInitialisationError;
import cora.exceptions.TypingError;
import cora.types.Type;

/**
 * A "leaf term" is any term that does not have strict subterms, such as variables or constants.
 * This inherit provides default functionality for such terms.
 */

abstract class LeafTermInherit extends TermInherit {
  private Type _type;

  /** Helper function to return the current classname for use in Errors. */
  private String queryMyClassName() {
    return "LeafTermInherit (" + this.getClass().getSimpleName() + ")";
  }

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

  public boolean isApplication() {
    return false;
  }

  public Term queryHead() {
    return this;
  }

  /** @return 0, since leaf terms do not have immediate subterms */
  public int numberArguments() {
    return 0;
  }

  /** @return the empty list, since leaf terms do not have arguments */
  public ArrayList<Term> queryArguments() {
    return new ArrayList<Term>();
  }
  
  /** @throws IndexingError, as a leaf term does not have arguments */
  public Term queryArgument(int i) {
    throw new IndexingError(queryMyClassName(), "queryArgument", i); 
  }

  /** Either returns this (if i == 0) or throws an IndexingError. */
  public Term queryImmediateHeadSubterm(int i) {
    if (i == 0) return this;
    throw new IndexingError(queryMyClassName(), "queryImmediateHeadSubterm", i);
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
    if (pos.isEmpty()) {
      if (!queryType().equals(replacement.queryType())) {
        throw new TypingError(queryMyClassName(), "replaceSubterm", "replacement term " +
          replacement.toString(), replacement.queryType().toString(), queryType().toString());
      }
      return replacement;
    }
    throw new IndexingError(queryMyClassName(), "replaceSubterm", toString(), pos.toString());
  }

  /** Returns the Application this(args). */
  public Term apply(List<Term> args) {
    if (args.size() == 0) return this;
    return new Application(this, args);
  }
}

