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

package charlie.util;

/**
 * There are two kinds of Exceptions used in Charlie (and Cora):
 * - Exceptions that really only occur if the programmer screwed up, such as storing null arguments
 * - Exceptions that may -- at least in some cases -- be caused by the user doing something wrong /
 *   unexpected.
 *
 * The latter kind may need to be printed to the user in an elegant way.  For such errors (or: when
 * in doubt), a UserException can be used.  This kind of exception collects not merely a message,
 * but the objects making up the exception, which may be printed in different ways depending on
 * user settings.  For example, an exception might be given a type, which should be printed
 * differently depending on whether the user is expecting ascii output or html output.
 *
 * By default, the message is just the toString() of all arguments combined, but printers might
 * make a different choice.
 */
public class UserException extends RuntimeException {
  private Object[] _components;

  private static String combine(Object[] args) {
    StringBuilder ret = new StringBuilder();
    for (Object arg : args) ret.append(arg.toString());
    return ret.toString();
  }

  public UserException(Object ...args) {
    super(combine(args));
    _components = args;
  }

  public int queryComponentCount() {
    return _components.length;
  }

  public Object queryComponent(int i) {
    return _components[i];
  }

  public Object[] makeArray() {
    return _components.clone();
  }
}

