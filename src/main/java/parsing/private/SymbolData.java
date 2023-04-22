/**************************************************************************************************
 Copyright 2019, 2022, 2023 Cynthia Kop

 Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 in compliance with the License.
 You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software distributed under the
 License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 express or implied.
 See the License for the specific language governing permissions and limitations under the License.
 *************************************************************************************************/

package cora.parsing;

import java.util.TreeMap;
import cora.exceptions.NullStorageError;
import cora.exceptions.TypingError;
import cora.types.Type;
import cora.terms.FunctionSymbol;
import cora.terms.Variable;
import cora.rewriting.Alphabet;
import cora.rewriting.TRS;

/**
 * This class maintains information used for parsing (user) input to Cora, in particular the list
 * of declared function symbols and variables.
 */
class SymbolData {
  private TRS _trs;                                   // TRS for parsing pre-defined symbols
  private TreeMap<String,FunctionSymbol> _alphabet;   // function symbols
  private TreeMap<String,Variable> _environment;      // variables

  SymbolData() {
    _trs = null;
    _alphabet = new TreeMap<String,FunctionSymbol>();
    _environment = new TreeMap<String,Variable>();
  }

  /**
   * When initialising a SymbolData with a TRS, the function symbols in that TRS will be used to
   * recognise function names.  Additional symbols may be declared, but it is not allowed to call
   * queryCurrentAlphabet on a SymbolData created with this constructor.
   */
  SymbolData(TRS trs) {
    _trs = trs;
    _alphabet = new TreeMap<String,FunctionSymbol>();
    _environment = new TreeMap<String,Variable>();
  }

  /**
   * Returns the number of function symbols declared in the current parser data.
   * This ignores any function symbols that are included by including a TRS.
   */
  public int queryNumberFunctionSymbols() {
    return _alphabet.size();
  }

  /** If the given symbol has been declared, this returns it, otherwise null. */
  public FunctionSymbol lookupFunctionSymbol(String symbol) {
    FunctionSymbol ret = _alphabet.get(symbol);
    if (ret == null && _trs != null) ret = _trs.lookupSymbol(symbol);
    return ret;
  }

  /**
   * Save the given function symbol: its name will now uniquely be associated with that symbol (and
   * consequently, with the associated type).
   * Should not be used for function symbols whose type has already been declared (although it is
   * allowed if the function symbols are the same).
   */
  public void addFunctionSymbol(FunctionSymbol symbol) {
    if (symbol == null) throw new NullStorageError("SymbolData", "function symbol");
    String name = symbol.queryName();
    Type type = symbol.queryType();
    FunctionSymbol existing = lookupFunctionSymbol(name);
    if (existing != null && !symbol.equals(existing)) {
      throw new Error("Duplicate call to SymbolData::addFunctionSymbol: trying to overwrite " +
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
    if (variable == null) throw new NullStorageError("SymbolData", "variable");
    String varname = variable.queryName();
    Type type = variable.queryType();
    Variable existing = _environment.get(varname);
    if (existing != null && !variable.equals(existing)) {
      throw new Error("Duplicate call to SymbolData::addVariable: trying to overwrite " +
                      "previously declared variable " + varname);
    }
    _environment.put(varname, variable);
  }

  /** Remove the variable by the given name, if any; and return it in this case. */
  public Variable removeVariable(String name) {
    Variable existing = _environment.get(name);
    _environment.remove(name);
    return existing;
  }

  /** This function removes all variable declarations from the current parse data. */
  public void clearVariables() {
    _environment.clear();
  }

  /** Returns the number of variables declared in the current parser data. */
  public int queryNumberVariables() {
    return _environment.size();
  }

  /** If the given variable has been declared, this returns its type, otherwise null. */
  public Variable lookupVariable(String name) {
    return _environment.get(name);
  }

  /** Returns whether a symbol by the given name exists as a variable or function symbol. */
  public boolean symbolDeclared(String name) {
    return lookupVariable(name) != null || lookupFunctionSymbol(name) != null;
  }

  /** Returns an Alphabet containing all the currently declared function symbols. */
  public Alphabet queryCurrentAlphabet() {
    if (_trs != null) {
      throw new Error("Calling queryCurrentAlphabet for SymbolData constructed with a given TRS!");
    }
    return new Alphabet(_alphabet.values());
  }
}

