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

import charlie.exceptions.CustomParserException;
import charlie.parser.lib.Token;
import charlie.parser.lib.ParsingStatus;
import charlie.parser.CoraTokenData;
import cora.rwinduction.engine.EquationPosition;

public class EquationPositionParser {
  /**
   * If the next token is EQPOS or IDENTIFIER, it is read.  If not, null is returned.
   * If the token indeed represents an EquationPosition, this is parsed and returned.
   * Otherwise, a CustomParserException is thrown.
   */
  public static EquationPosition readPosition(ParsingStatus status) throws CustomParserException {
    Token tok = status.readNextIf(CoraTokenData.IDENTIFIER);
    if (tok == null) tok = status.readNextIf(RWParser.EQPOS);
    if (tok == null) return null;
    return EquationPosition.parse(tok.getText());
  }
}

