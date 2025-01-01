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

import charlie.exceptions.ParseException;
import charlie.parser.lib.*;
import charlie.parser.Parser.*;
import charlie.parser.CoraTokenData;
import charlie.parser.CoraParser;
import charlie.terms.*;
import charlie.trs.TRS;
import charlie.reader.CoraInputReader;

public class SubstitutionParser {
  /**
   * This reads a substitution of the form [x1:=term1,...,xn:=termn] from the given string, using
   * the first renaming to look up the keys, and the second renaming to look up the values.  The
   * latter Renaming may be modified, if some value includes fresh (meta-)variables.
   *
   * Note that this may absolutely throw a ParseException.
   */
  public static Substitution parseSubstitution(String str, TRS trs,
                                               Renaming keyNames, Renaming valueNames) {
    ParsingStatus status = RWParser.createStatus(str);
    Substitution ret = parseSubstitution(status, trs, keyNames, valueNames);
    status.expect(Token.EOF, "end of command");
    return ret;
  }

  /**
   * This reads a substitution of the form [x1:=term1,...,xn:=termn] from the given parsing status,
   * using the first renaming to look up the keys, and the second renaming to look up the values.
   * The latter Renaming may be modified, if some value includes fresh (meta-)variables; the former
   * will not be, but if any of the keys is missing from keyNames, a ParseException will be thrown.
   * 
   * The ParsingStatus is advanced until after the substitution.
   * 
   * Note that this function expects a ParsingStatus without error tolerance, or it might hang
   * indefinitely (a ParsingStatus as created by the RWParser suffices).
   *
   * @throws ParseException if any problem occurs, not just missing variable names.
   */
  public static Substitution parseSubstitution(ParsingStatus status, TRS trs,
                                               Renaming keyNames, Renaming valueNames) {
    Substitution ret = TermFactory.createEmptySubstitution();
    status.expect(CoraTokenData.METAOPEN, "substitution opening bracket [");
    boolean first = true;
    while (status.readNextIf(CoraTokenData.METACLOSE) == null) {
      if (first) first = false;
      else status.expect(CoraTokenData.COMMA, "comma");
      Token vartok = status.expect(CoraTokenData.IDENTIFIER, "(meta-)variable name");
      status.expect(RWParser.ASSIGN, ":=");
      ParserTerm pterm = CoraParser.readTerm(status);
      String varname = vartok.getText();
      Replaceable x = keyNames.getReplaceable(varname);
      if (x == null) { status.storeError("No such variable: " + varname, vartok); break; }
      Term term = CoraInputReader.readTerm(pterm, valueNames, true, trs);
      if (!x.queryType().equals(term.queryType())) {
        status.storeError(varname + " has type " + x.queryType().toString() + " but is mapped to " +
          "term " + term.toString() + " of type " + term.queryType().toString() + ".", vartok);
        break;
      }
      ret.extend(x, term);
    }
    return ret;
  }
}

