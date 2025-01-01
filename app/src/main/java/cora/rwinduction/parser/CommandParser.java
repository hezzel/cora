/**************************************************************************************************
 Copyright 2024 Cynthia Kop

 Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 in compliance with the License.
 You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software distributed under the
 License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 express or implied.
 See the License for the specific language governing permissions and limitations under the License.
 *************************************************************************************************/

package cora.rwinduction.parser;

import charlie.parser.lib.ParsingStatus;
import charlie.parser.CoraTokenData;

public class CommandParser {
  /**
   * Given a parsing status built by the RWParser -- so without ANY error tolerance -- this returns
   * the "command" that it starts with.  This is either an identifier, or COLON identifier.  It may
   * also be empty if no tokens are given.
   */
  public static String parseCommand(ParsingStatus status) {
    if (status.peekNext().isEof() ||
        status.peekNext().getName().equals(RWParser.SEPARATOR)) return "";
    boolean colon = (status.readNextIf(CoraTokenData.COLON) != null);
    String txt = status.expect(CoraTokenData.IDENTIFIER, "command name").getText();
    if (colon) return ":" + txt;
    else return txt;
  }
}

