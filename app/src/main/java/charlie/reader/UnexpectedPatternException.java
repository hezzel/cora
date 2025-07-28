/**************************************************************************************************
 Copyright 2019--2025 Cynthia Kop

 Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 in compliance with the License.
 You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software distributed under the
 License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 express or implied.
 See the License for the specific language governing permissions and limitations under the License.
 *************************************************************************************************/

package charlie.reader;

/**
 * The parser defines a number of shapes that a term can have, with different formalisms supporting
 * a different subset of these shapes.  The various readers proceed to turn the parser terms into
 * real terms.  However, to do so they must be given parser terms built by the right parser.
 * This exception is thrown if they are given a parser term that is not supported in their format.
 */
public class UnexpectedPatternException extends RuntimeException {
  public UnexpectedPatternException(String classname, String functionname, String expected,
                                    String given) {
    super("Unexpected pattern encountered: calling " + classname + "::" + functionname + " with " +
      given + " while " + expected + " was expected.");
  }
}

