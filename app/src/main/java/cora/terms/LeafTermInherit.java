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
import cora.exceptions.*;
import cora.types.Type;

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

  /** @return a list containing only the empty Position. */
  public ArrayList<Path> queryPositions() {
    ArrayList<Path> ret = new ArrayList<Path>();
    ret.add(new EmptyPath(this));
    return ret;
  }

  /** @return an empty list. */
  public ArrayList<Path> queryPositionsForHead(Term top) {
    ArrayList<Path> ret = new ArrayList<Path>();
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

  /** @return the replacement if pos is the empty head position; otherwise throws an IndexingError */
  public Term replaceSubterm(HeadPosition pos, Term replacement) {
    if (pos.isEnd() && pos.queryChopCount() == 0) {
      if (!queryType().equals(replacement.queryType())) {
        throw new TypingError(queryMyClassName(), "replaceSubterm", "replacement term " +
          replacement.toString(), replacement.queryType().toString(), queryType().toString());
      }
      return replacement;
    }
    throw new IndexingError(queryMyClassName(), "replaceSubterm", toString(), pos.toString());
  }
}

