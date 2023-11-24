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

package cora.terms;

import cora.exceptions.*;

/**
 * A MetaPath is a position of the form !i.pos, where i indicates the index of a meta-argument in
 * the corresponding meta-application and pos a position within that meta-argument.  Since it is a
 * path, it keeps track of the terms on the way from the top of the term to the referenced subterm.
 */
class MetaPath implements Path {
  private final int _argPos;
  private final Path _tail;
  private Term _topterm;
  private Term _subterm;

  /** Should only be called by Terms; nothing outside the package. */
  MetaPath(Term myterm, int argumentIndex, Path tail) {
    _argPos = argumentIndex;
    _tail = tail;
    if (tail == null) throw new NullInitialisationError("ArgumentPath", "tail");
    _topterm = myterm;
    if (myterm == null) throw new NullInitialisationError("ArgumentPath", "myterm");
    _subterm = tail.queryCorrespondingSubterm();
    if (!myterm.queryHead().isMetaApplication()) throw new IndexingError("MetaPath", "constructor",
      argumentIndex);
    if (argumentIndex <= 0 || argumentIndex > myterm.numberMetaArguments()) {
      throw new IndexingError("MetaPath", "constructor", argumentIndex, 1,
                              myterm.numberMetaArguments());
    }
    if (myterm.queryMetaArgument(argumentIndex) != tail.queryAssociatedTerm()) {
      throw new IllegalArgumentError("MetaPath", "constructor", "subterm !" + argumentIndex +
        " of " + myterm + " is " + myterm.queryMetaArgument(argumentIndex) +
        ", while tail refers to " + tail.queryAssociatedTerm() + ".");
    }
  }

  public boolean isEmpty() {
    return false;
  }

  public boolean isArgument() {
    return false;
  }

  public boolean isTuple() {
    return false;
  }

  public boolean isLambda() {
    return false;
  }

  public boolean isMeta() {
    return true;
  }

  public Term queryAssociatedTerm() {
    return _topterm;
  }

  public Term queryCorrespondingSubterm() {
    return _subterm;
  }

  public int queryArgumentPosition() {
    throw new InappropriatePatternDataError("MetaPath", "queryArgumentPosition",
      "positions of the form i.tail with i > 0");
  }

  public int queryComponentPosition() {
    throw new InappropriatePatternDataError("MetaPath", "queryComponentPosition",
      "positions of the form i.tail with i > 0");
  }

  public int queryMetaPosition() {
    return _argPos;
  }

  public Path queryTail() {
    return _tail;
  }

  public boolean equals(Position other) {
    return other.isMeta() &&
           other.queryMetaPosition() == _argPos &&
           _tail.equals(other.queryTail());
  }

  public String toString() {
    return "!" + _argPos + "." + _tail.toString();
  }
}
