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

package cora.interfaces;

/**
 * Terms are the main object to be rewritten.  There are various kinds of terms,
 * currently including only functional terms f(s1,...,sk) and variables, but in the future perhaps
 * additional constructions are allowed.
 *
 * Note; all instances of Term must (and can be expected to) be immutable.
 */
public interface Term {
  public enum TermKind { VARTERM, FUNCTIONALTERM };

  /** Returns what kind of Term this is. */
  TermKind queryTermKind();

  /**
   * Returns a string representation of the term (primarily for debugging purposes, as it is not
   * pretty-printed).
   */
  String toString();
}

