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
 * A LambdaPath is a position of the form 0.pos, which indicates that we are passing into an
 * abstraction.  Since it is a path, it keeps track of the terms on the way from the top of the
 * term to the referenced subterm.
 */
class LambdaPath implements Path {
  private final Path _tail;
  private Term _topterm;
  private Term _subterm;

  /** Should only be called by Terms; nothing outside the package. */
  LambdaPath(Term myterm, Path tail) {
    _tail = tail;
    if (tail == null) throw new NullInitialisationError("LambdaPath", "tail");
    _topterm = myterm;
    if (myterm == null) throw new NullInitialisationError("LambdaPath", "myterm");
    _subterm = tail.queryCorrespondingSubterm();
    if (!myterm.queryHead().isAbstraction()) {
      throw new IllegalArgumentError("LambdaPath", "constructor",
        "trying to create a lambda-path for non-lambda expression " + myterm);
    }
    if (myterm.queryAbstractionSubterm() != tail.queryAssociatedTerm()) {
      throw new IllegalArgumentError("LambdaPath", "constructor", "immediate subterm of " +
        myterm + " is " + myterm.queryAbstractionSubterm() + ", while tail refers to " +
        tail.queryAssociatedTerm() + ".");
    }
  }

  public boolean isEmpty() {
    return false;
  }

  public boolean isArgument() {
    return false;
  }

  public boolean isLambda() {
    return true;
  }

  public boolean isMeta() {
    return false;
  }

  public Term queryAssociatedTerm() {
    return _topterm;
  }

  public Term queryCorrespondingSubterm() {
    return _subterm;
  }

  public int queryArgumentPosition() {
    throw new InappropriatePatternDataError("LambdaPath", "queryArgumentPosition",
      "positions of the form i.tail with i > 0");
  }

  public int queryMetaPosition() {
    throw new InappropriatePatternDataError("LambdaPath", "queryMetaPosition",
      "positions of the form !i.tail");
  }

  public Path queryTail() {
    return _tail;
  }

  public boolean equals(Position other) {
    return other.isLambda() &&
           _tail.equals(other.queryTail());
  }

  public String toString() {
    return "0." + _tail.toString();
  }
}
