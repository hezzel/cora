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

package charlie.terms;

/**
 * An IncorrectStringException is thrown when a user-supplied string is parsed, yet it contains
 * illegal escape sequences or does not have the right shape.
 */
public class IncorrectStringException extends Exception {
  private String _input;
  private String _explanation;

  public IncorrectStringException(String input, String problem) {
    super("Cannot parse string [" + input + "]: " + problem);
    _input = input;
    _explanation = problem;
  }

  public String queryBadInput() { return _input; }
  public String queryExplanation() { return _explanation; }
}

