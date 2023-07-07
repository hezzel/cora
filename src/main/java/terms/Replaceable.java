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

import java.lang.Comparable;
import cora.types.Type;

/**
 * Replaceable is a parent class for variables and meta-variables: objects that can be substituted,
 * as well as renamed.
 */
public interface Replaceable extends Comparable<Replaceable> {
  public static int KIND_BINDER = 0;
  public static int KIND_BASEVAR = 1;
  public static int KIND_METAVAR = 2;

  /** @return the kind of Replaceable this is (one of KIND_BINDER, KIND_BASEVAR or KIND_METAVAR) */
  int queryReplaceableKind();

  /**
   * @return a string representation of the replaceable item.
   * Such names are not unique, and Replaceable objects are not identified by their name.
   */
  String queryName();

  /** @return the type of the replaceable object */
  Type queryType();

  /**
   * @return the number of arguments this replaceable object needs to be given
   * (this is necessarily 0 for a binder or base variable)
   */
  int queryArity();

  /** @return equality to another Replaceable (this respects compareTo) */
  boolean equals(Replaceable x);

  /**
   * A replaceable object is uniquely defined by the combination of its kind, type, and ID.
   * This is mostly intended for internal use, to support a total ordering on replaceables.
   */
  int queryIndex();
}

