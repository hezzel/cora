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

package cora.rewriting;

import java.util.Collection;
import java.util.TreeMap;
import cora.exceptions.NullInitialisationError;
import cora.exceptions.TypingError;
import cora.interfaces.terms.FunctionSymbol;
import cora.interfaces.rewriting.Alphabet;

/** A finite set of user-defined symbols, with no duplicate names. */
public class UserDefinedAlphabet implements Alphabet {
  private TreeMap<String,FunctionSymbol> _symbols;

  /**
   * Create an alphabet with the given symbols.
   * Duplicate occurrences of the same function symbol are removed; duplicate occurrences of the
   * same type that are not the same symbol cause an Error to be produced.
   */
  public UserDefinedAlphabet(Collection<FunctionSymbol> symbols) {
    _symbols = new TreeMap<String,FunctionSymbol>();
    if (symbols == null) throw new NullInitialisationError("UserDefinedAlphabet", "symbols list");
    for (FunctionSymbol f : symbols) {
      if (f == null) throw new NullInitialisationError("UserDefinedAlphabet", "a symbol");
      add(f);
    }
  }

  public UserDefinedAlphabet copy() {
    return this;  // the current implementation is immutable, so we can safely do this;
                  // change to do a deep copy if this alphabet is ever made mutable!
  }

  /**
   * Adds a symbol to the current Alphabet. ONLY to be called from constructors (or otherwise
   * during the setup of a UserDefinedAlphabet), since calling it later would violate immutability.
   */
  private void add(FunctionSymbol symbol) {
    FunctionSymbol existing = _symbols.get(symbol.queryName());
    if (existing == null) _symbols.put(symbol.queryName(), symbol);
    else if (!existing.equals(symbol)) {
      throw new TypingError("UserDefinedAlphabet", "add", "duplicate occurrence of " +
        symbol.queryName(), existing.queryType().toString(), symbol.queryType().toString());
    }
  }

  /** Returns the FunctionSymbol with the given name if it exists, or null otherwise. */
  public FunctionSymbol lookup(String name) {
    return _symbols.get(name);
  }

  /** Returns a pleasan-to-read string representation of the current alphabet. */
  public String toString() {
    String ret = "";
    for (FunctionSymbol symbol : _symbols.values()) {
      ret += symbol.queryName() + " : " + symbol.queryType() + "\n";
    }
    return ret;
  }
}

