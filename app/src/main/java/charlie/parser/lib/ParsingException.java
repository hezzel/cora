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

package charlie.parser.lib;

import java.util.List;
import charlie.util.UserException;

/**
 * A ParsingException consists of one or more lines detailing errors encountered during
 * lexing/parsing.
 */
public class ParsingException extends UserException {
  public ParsingException(List<ParsingErrorMessage> parts) {
    super(makeArray(parts));
  }

  public static ParsingException create(Token token, Object ...parts) {
    return new ParsingException(List.of(new ParsingErrorMessage(token, parts)));
  }

  private static Object[] makeArray(List<ParsingErrorMessage> parts) {
    int size = 0;
    for (ParsingErrorMessage msg : parts) size += msg.numComponents() + 1;
    Object[] ret = new Object[size];
    int total = 0;
    for (ParsingErrorMessage msg : parts) {
      for (int i = 0; i < msg.numComponents(); i++) {
        ret[total++] = msg.getComponent(i);
      }
      ret[total++] = "\n";
    }
    return ret;
  }
}

