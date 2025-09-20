/**************************************************************************************************
 Copyright 2023--2025 Cynthia Kop

 Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 in compliance with the License.
 You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software distributed under the
 License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 express or implied.
 See the License for the specific language governing permissions and limitations under the License.
 *************************************************************************************************/

package charlie.substitution;

import charlie.util.UserException;
import charlie.terms.Term;

/**
 * A PatternRequiredException is thrown when a function like matching is called on something that
 * is not a pattern, to explain why a (sub-)term is not a pattern or semi-pattern (and thus the
 * function may not be used).
 */
public class PatternRequiredException extends UserException {
  public PatternRequiredException(Term term, String functionality, int argument, String expl) {
    super("Cannot use " + functionality + " on (sub-)term ", term, " since it is not a (semi-)" +
      "pattern: argument " + argument + " " + expl);
  }
}

