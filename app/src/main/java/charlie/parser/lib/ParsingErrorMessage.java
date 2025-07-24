/**************************************************************************************************
 Copyright 2025 Cynthia Kop

 Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 in compliance with the License.
 You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software distributed under the
 License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 express or implied.
 See the License for the specific language governing permissions and limitations under the License.
 *************************************************************************************************/

package charlie.parser.lib;

import charlie.util.UserException;

/**
 * An error message to be stored during parsing, and eventually to be thrown in a ParsingException.
 *
 * Messages may be marked with a token for the place where the error occurred but don't have to be.
 * Messages may be composed of multiple objects, which catching classes may choose to print in a
 * more sophisticated way than just toString(), but these objects should always be printable in a
 * default way using toString() as well, as this is used to generate the standard error message
 * when the exception is caught.
 */
public class ParsingErrorMessage {
  private Token _token;           // might be null
  private Object[] _components;   // comprises the error messages; hence, should be non-empty

  /**
   * Create a ParsingErrorMessage marked for the given token (and thus, its position in the input
   * file(s)).  It is allows for token to be null.  The "rest" makes up the actual message and
   * could just be a single string, but is also allowed to be a sequence of more complex objects.
   * This is to allow whichever object has to handle the error message to determine for itself how
   * such complex objects should be printed.  For example, a ParsingErrorMessage may include a
   * Type, which should be printed differently based on user settings.
   *
   * Note that the token itself will NOT be printed as part of the error message, but only its
   * position.  So at least one other argument should be given (that is, rest should be non-empty)
   * or the message will look rather odd.
   */
  public ParsingErrorMessage(Token token, Object ...rest) {
    _token = token;
    if (rest.length == 1 && rest[0] instanceof Object[] a) _components = a;
    else _components = rest;
  }

  /**
   * Creates a ParsingErorrMessage that indicates that the given user exception has occurred at the
   * given token position.  It is allowed for the token to be null, in which case this essentially
   * functions as a wrapper for the given exception.
   */
  public ParsingErrorMessage(Token token, UserException e) {
    _token = token;
    _components = e.makeArray();
  }

  /** Returns the token this message is marked for, or null if it is not marked for any token. */
  public Token queryToken() {
    return _token;
  }
  
  /** Returns the total number of components, including a possible component for the position. */
  public int numComponents() {
    return _components.length + (_token == null ? 0 : 1);
  }

  /** Returns the given component, counting from 0 for the token (if any). */
  public Object getComponent(int index) {
    if (_token == null) return _components[index];
    if (index == 0) return _token.getPosition() + ": ";
    return _components[index-1];
  }

  /** Default toString() implementation; should typically not be used other than in testing. */
  public String toString() {
    StringBuilder builder = new StringBuilder();
    for (int i = 0; i < numComponents(); i++) builder.append(getComponent(i));
    return builder.toString();
  }
}

