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
import cora.exceptions.ArityError;
import cora.exceptions.IndexingError;
import cora.exceptions.InappropriatePatternDataError;
import cora.exceptions.NullInitialisationError;
import cora.exceptions.TypingError;
import cora.interfaces.types.Type;
import cora.interfaces.terms.*;
import cora.terms.positions.EmptyPosition;
import cora.terms.positions.ArgumentPosition;

/**
 * An ApplicativeTermInherit provides the shared functionality for terms of the form
 * f(s1,...,sn) or x(s1,...,sn).
 */
abstract class ApplicativeTermInherit extends TermInherit implements Term {
  protected ArrayList<Term> _args;
  protected Type _outputType;

  /**
   * This function should create head(newargs), with the same output type.
   * All checks may be bypassed, since newargs will be obtained from args and thus be well-typed
   * and not null; moreover, it should be safe to store newargs in the (immutable!) new term.
   */
  protected abstract Term reconstruct(ArrayList<Term> newargs);

  /** Helper function to return the current classname for use in Errors. */
  private String queryMyClassName() {
    return "ApplicativeTermInherit (" + this.getClass().getSimpleName() + ")";
  }

  /**
   * This helper function handles the functionality for constructors to set up _args and
   * _outputType.
   * The given function symbol and argument list become the property of this applicative term, and
   * the output type is derived from the two given arguments.
   * If there are any problems -- such as the head or an argument being null, or the types not
   * checking out -- an appropriate Error is thrown. However, it *is* assumed that args is not
   * null.
   */
  private void construct(Term head, ArrayList<Term> args) {
    if (head == null) throw new NullInitialisationError(queryMyClassName(), "head");
    Type type = head.queryType();
    for (int i = 0; i < args.size(); i++) {
      Term arg = args.get(i);
      if (arg == null) {
        throw new NullInitialisationError(queryMyClassName(), "passing a null argument to " +
          head.toString() + ".");
      }
      if (!type.isArrowType()) {
        throw new ArityError(queryMyClassName(), "constructor", "symbol " + head.toString() +
          " has maximum arity " + i + " and is given " + args.size() + " arguments.");
      }
      Type input = type.queryArrowInputType();
      if (!input.equals(arg.queryType())) {
        throw new TypingError(queryMyClassName(), "constructor", "arg " + i + " of " +
          head.toString(), arg.queryType() == null ? "null" : arg.queryType().toString(),
          input.toString());
      }
      type = type.queryArrowOutputType();
    }
    _args = args;
    _outputType = type;
  }

  /**
   * Default constructor; the inheriting object should manually set up _args and _outputType if
   * this constructor is used.
   */
  protected ApplicativeTermInherit() {}

  /**
   * This constructor is used to create a term which takes one argument.
   * Throws an error if the head is null or does not have arity 1, or the argument is null.
   */
  protected ApplicativeTermInherit(Term head, Term arg) {
    ArrayList<Term> args = new ArrayList<Term>();
    args.add(arg);
    construct(head, args);
  }

  /**
   * This constructor is used to create a term which takes two arguments.
   * Throws an error if the head does not have arity 2, or one of the arguments is null.
   */
  protected ApplicativeTermInherit(Term head, Term arg1, Term arg2) {
    ArrayList<Term> args = new ArrayList<Term>();
    args.add(arg1);
    args.add(arg2);
    construct(head, args);
  }

  /**
   * This constructor is used to create a term head(s1,...,sn) with n >= 0.
   * Throws an error if n does not match the arity of the head, or if the types of the arguments
   * are not the expected input types of the head.
   */
  protected ApplicativeTermInherit(Term head, ArrayList<Term> args) {
    if (args == null) throw new NullInitialisationError(queryMyClassName(), "argument list");
    construct(head, new ArrayList<Term>(args));
  }

  /** This method returns the output type of the term. */
  public Type queryType() {
    return _outputType;
  }

  /** For a term head(s1,...,sn), this returns n. */
  public int numberImmediateSubterms() {
    return _args.size();
  }

  /** For a term head(s1,...,sn), this returns si if 1 <= i <= n, and throws an error otherwise. */
  public Term queryImmediateSubterm(int i) {
    if (i <= 0 || i > _args.size()) {
      throw new IndexingError(queryMyClassName(), "queryImmediateSubterm", i, 1,
                              _args.size());
    }
    return _args.get(i-1);
  }

  /** Returns the positions in all subterms, from left to right, followed by the empty position. */
  public ArrayList<Position> queryAllPositions() {
    ArrayList<Position> ret = new ArrayList<Position>();
    for (int i = 0; i < _args.size(); i++) {
      ArrayList<Position> subposses = _args.get(i).queryAllPositions();
      for (int j = 0; j < subposses.size(); j++) {
        ret.add(new ArgumentPosition(i+1, subposses.get(j)));
      }
    }
    ret.add(new EmptyPosition());
    return ret;
  }

  /** @return this if the position is empty; otherwise throws an IndexingError */
  public Term querySubterm(Position pos) {
    if (pos.isEmpty()) return this;
    int index = pos.queryArgumentPosition();
    if (index < 1 || index > _args.size()) {
      throw new IndexingError(queryMyClassName(), "querySubterm", toString(), pos.toString());
    }
    return _args.get(index-1).querySubterm(pos.queryTail());
  }

  /**
   * @return a copy of the term with the subterm at the given position replaced by replacement, if
   * such a position exists; otherwise throws an IndexingError
   */
  public Term replaceSubterm(Position pos, Term replacement) {
    if (pos.isEmpty()) {
      if (!queryType().equals(replacement.queryType())) {
        throw new TypingError(queryMyClassName(), "replaceSubterm", "replacement term " +
                    replacement.toString(), replacement.queryType().toString(),
                    queryType().toString());
      }
      return replacement;
    }
    int index = pos.queryArgumentPosition();
    if (index < 1 || index > _args.size()) {
      throw new IndexingError(queryMyClassName(), "replaceSubterm", toString(), pos.toString());
    }
    ArrayList<Term> args = new ArrayList<Term>(_args);
    args.set(index-1, args.get(index-1).replaceSubterm(pos.queryTail(), replacement));
    return reconstruct(args);
  }

  /**
   * This method applies the substitution recursively to the arguments and returns the resulting
   * substituted-arguments list.
   */
  protected ArrayList<Term> substituteArgs(Substitution gamma) {
    ArrayList<Term> args = new ArrayList<Term>(_args);
    for (int i = 0; i < args.size(); i++) {
      Term t = args.get(i).substitute(gamma);
      if (t == null) {
        throw new Error("Substituting " + args.get(i).toString() + " results in null!");
      }
      args.set(i, t);
    }
    return args;
  }
}

