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

package charlie.terms;

/**
 * Terms are defined by an interface which can have various patterns, which are queried through
 * functions rather than through pattern matching.  Hence, it is possible that someone may call a
 * function that makes no sense for a given pattern; for example queryAbstractionSubterm() on a
 * term that is not an abstraction.
 *
 * In such cases, for recognisability of the issue, an InappropriatePatternDataException will be
 * thrown.  This is not a UserException, since calling the wrong pattern on an instance of an
 * interface is always a programming error.
 */
class InappropriatePatternDataException extends RuntimeException {
  public InappropriatePatternDataException(String classname, String functionname, String expected) {
    super("Inappropriate pattern data request: calling " + classname + "::" + functionname +
      " while this function should only be called on " + expected + ".");
  }
}

