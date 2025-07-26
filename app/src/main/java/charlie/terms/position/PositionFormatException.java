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

package charlie.terms.position;

/**
 * Rather than using a lexer and parser, positions may be read through a custom parser defined in
 * Position.parse. If a position is malformed, then a PositionFormatException will be thrown by
 * this parsing function.
 *
 * This is not marked as a UserException because while a PositionFormatException is definitely
 * something that may occur as the result of user errors, it is not a RuntimeException: it should
 * be explicitly handled or passed on.
 */
public class PositionFormatException extends Exception {
  private int _pos;
  private String _problem;
  private String _explanation;

  public PositionFormatException(int pos, String positionText, String explanation) {
    super(pos + ": Could not parse position [" + positionText + "]: " + explanation);
    _pos = pos;
    _problem = positionText;
    _explanation = explanation;
  }

  /** The position within the input where the error occurred. */
  public int queryProblemPos() {
    return _pos;
  }

  /** The inputted position that could not be parsed. */
  public String queryProblematicInput() {
    return _problem;
  }

  public String queryExplanation() {
    return _explanation;
  }
}
