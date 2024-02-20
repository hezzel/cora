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

package cora.reader;

import java.util.TreeMap;
import java.util.TreeSet;
import cora.exceptions.NullStorageError;
import cora.types.Type;
import cora.terms.FunctionSymbol;
import cora.terms.Variable;
import cora.terms.MetaVariable;
import cora.trs.Alphabet;
import cora.trs.TRS;

/**
 * This class maintains information used for turning data from the parser into proper Cora
 * structures, in particular the lists of declared function symbols, variables and
 * meta-variables.
 */
class SymbolData {
  private TRS _trs;                                   // TRS for parsing pre-defined symbols
  private TreeMap<String,FunctionSymbol> _alphabet;   // function symbols
  private TreeMap<String,Variable> _variables;        // variables
  private TreeMap<String,MetaVariable> _mvariables;   // meta-variables of arity ≥ 1
  private TreeSet<String> _private;                   // the names of private symbols

  SymbolData() {
    _trs = null;
    _alphabet = new TreeMap<String,FunctionSymbol>();
    _variables = new TreeMap<String,Variable>();
    _mvariables = new TreeMap<String,MetaVariable>();
    _private = new TreeSet<String>();
  }

  /**
   * When initialising a SymbolData with a TRS, the function symbols in that TRS will be used to
   * recognise function names.  Additional symbols may be declared, but it is not allowed to call
   * queryCurrentAlphabet on a SymbolData created with this constructor.
   */
  SymbolData(TRS trs) {
    _trs = trs;
    _alphabet = new TreeMap<String,FunctionSymbol>();
    _variables = new TreeMap<String,Variable>();
    _mvariables = new TreeMap<String,MetaVariable>();
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
    Variable existing = _variables.get(varname);
    if (existing != null && !variable.equals(existing)) {
      throw new Error("Duplicate call to SymbolData::addVariable: trying to overwrite " +
                      "previously declared variable " + varname);
    }
    _variables.put(varname, variable);
  }

  /**
   * Save the given meta-variable: its name will now uniquely be associated with that meta-variable.
   * Should not be used for meta-variables that have already been declared, although it is allowed
   * if the meta-variables are equal.
   * It is not intended to be used for meta-variables that are also variables (store those as
   * variables instead), but this is not blocked.
   */
  public void addMetaVariable(MetaVariable mvar) {
    if (mvar == null) throw new NullStorageError("SymbolData", "mvar");
    String varname = mvar.queryName();
    Type type = mvar.queryType();
    MetaVariable existing = _mvariables.get(varname);
    if (existing != null && !mvar.equals(existing)) {
      throw new Error("Duplicate call to SymbolData::addMetaVariable: trying to overwrite " +
                      "previously declared meta-variable " + varname);
    }
    _mvariables.put(varname, mvar);
  }

  /** This marks the given function symbol as a private symbol. */
  public void setPrivate(FunctionSymbol symbol) {
    if (symbol == null) throw new NullStorageError("SymbolData", "private function symbol");
    _private.add(symbol.queryName());
  }

  /** Remove the variable by the given name, if any; and return it in this case. */
  public Variable removeVariable(String name) {
    Variable existing = _variables.get(name);
    _variables.remove(name);
    return existing;
  }

  /**
   * This function removes all variable and meta-variable declarations from the current parse data.
   */
  public void clearEnvironment() {
    _variables.clear();
    _mvariables.clear();
  }

  /** Returns the number of variables declared in the current parser data. */
  public int queryNumberVariables() {
    return _variables.size();
  }

  /** Returns the number of meta-variables declared in the current parser data. */
  public int queryNumberMetaVariables() {
    return _mvariables.size();
  }

  /** If the given variable has been declared, this returns it, otherwise null. */
  public Variable lookupVariable(String name) {
    return _variables.get(name);
  }

  /** If the given meta-variable has been declared, this returns it, otherwise null. */
  public MetaVariable lookupMetaVariable(String name) {
    return _mvariables.get(name);
  }

  /** Returns whether a symbol by the given name exists as a (meta-)variable or function symbol. */
  public boolean symbolDeclared(String name) {
    return lookupVariable(name) != null || lookupMetaVariable(name) != null ||
           lookupFunctionSymbol(name) != null;
  }

  /** Returns an Alphabet containing all the currently declared function symbols. */
  public Alphabet queryCurrentAlphabet() {
    if (_trs != null) {
      throw new Error("Calling queryCurrentAlphabet for SymbolData constructed with a given TRS!");
    }
    return new Alphabet(_alphabet.values());
  }

  /** This returns the set of private symbols defined in the symbol data. */
  public TreeSet<String> queryPrivateSymbols() {
    return new TreeSet<String>(_private);
  }
}

