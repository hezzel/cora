/**************************************************************************************************
 Copyright 2019 Cynthia Kop

 Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 in compliance with the License.
 You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software distributed under the
 License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 express or implied.
 See the License for the specific language governing permissions and limitations under the License.
 *************************************************************************************************/

package cora.parsers;

import java.util.TreeMap;
import cora.exceptions.NullStorageError;
import cora.exceptions.TypingError;
import cora.interfaces.types.Type;
import cora.interfaces.terms.FunctionSymbol;
import cora.interfaces.terms.Variable;
import cora.interfaces.rewriting.Alphabet;
import cora.rewriting.UserDefinedAlphabet;

/**
 * This class maintains information used for parsing (user) input to Cora, such as the alphabet of
 * declared function symbols and the information of infix usage.
 */
public class ParseData {
  private TreeMap<String,FunctionSymbol> _alphabet;   // function symbols
  private TreeMap<String,Variable> _environment;      // variables

  public ParseData() {
    _alphabet = new TreeMap<String,FunctionSymbol>();
    _environment = new TreeMap<String,Variable>();
  }

  /**
   * Save the given function symbol: its name will now uniquely be associated with that symbol (and
   * consequently, with the associated type).
   * Should not be used for function symbols whose type has already been declared (although it is
   * allowed if the function symbols are the same).
   */
  public void addFunctionSymbol(FunctionSymbol symbol) {
    if (symbol == null) throw new NullStorageError("ParseData", "function symbol");
    String name = symbol.queryName();
    Type type = symbol.queryType();
    FunctionSymbol existing = _alphabet.get(name);
    if (existing != null && !symbol.equals(existing)) {
      throw new Error("Duplicate call to ParseData::addFunctionSymbol: trying to overwrite " +
                      "previously declared symbol " + name);
    }
    _alphabet.put(name, symbol);
  }

  /**
   * Save the given variable: its name will now uniquely be associated with that variable.
   * Should not be used for variables that have already been declared, although it is allowed if
   * the variables are equal.
   */
  public void addVariable(Variable variable) {
    if (variable == null) throw new NullStorageError("ParseData", "variable");
    String varname = variable.queryName();
    Type type = variable.queryType();
    Variable existing = _environment.get(varname);
    if (existing != null && !variable.equals(existing)) {
      throw new Error("Duplicate call to ParseData::addVariable: trying to overwrite " +
                      "previously declared variable " + varname);
    }
    _environment.put(varname, variable);
  }

  /** This function removes all variable declarations from the current parse data. */
  public void clearVariables() {
    _environment.clear();
  }

  /** Returns the number of variables declared in the current parser data. */
  public int queryNumberVariables() {
    return _environment.size();
  }

  /** Returns the number of function symbols declared in the current parser data. */
  public int queryNumberFunctionSymbols() {
    return _alphabet.size();
  }

  /** If the given symbol has been declared, this returns its type, otherwise null. */
  public FunctionSymbol lookupFunctionSymbol(String symbol) {
    return _alphabet.get(symbol);
  }

  /** If the given variable has been declared, this returns its type, otherwise null. */
  public Variable lookupVariable(String name) {
    return _environment.get(name);
  }

  /** Returns an Alphabet containing all the currently declared function symbols. */
  public Alphabet queryCurrentAlphabet() {
    return new UserDefinedAlphabet(_alphabet.values());
  }
}

