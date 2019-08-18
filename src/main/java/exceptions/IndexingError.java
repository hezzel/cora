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

package cora.exceptions;

/**
 * An IndexingError is thrown when argument i is requested of some type/term/whatnot, and i is not
 * in the range 1...numberOfArguments.
 */
public class IndexingError extends Error {
  public IndexingError(String classname, String functionname, int given, int min, int max) {
    super("Called " + classname + "::" + functionname + "(" + given + "), when available " +
      "indexes range from " + min + " to " + max + ".");
  }

  /** Use this constructor when attempting to index an empty list. */
  public IndexingError(String classname, String functionname, int given) {
    super("Called " + classname + "::" + functionname + "(" + given + "), when there are no " +
      "indexes available.");
  }

  /** Use this constructor when attempting to access a position that does not exist. */
  public IndexingError(String classname, String functionname, String term, String position) {
    super("Called " + classname + "::" + functionname + " with position " + position + " in " +
      "term " + term + ".");
  }
}

