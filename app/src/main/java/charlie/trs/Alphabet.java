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

package charlie.trs;

import java.util.Collection;
import charlie.exceptions.NullStorageException;
import charlie.exceptions.TypingException;
import charlie.util.LookupMap;
import charlie.terms.FunctionSymbol;

/** A finite, immutable set of user-defined symbols, with no duplicate names. */
public class Alphabet {
  private final LookupMap<FunctionSymbol> _symbols;

  /** Creates an Alphabet with the given symbols. */
  public Alphabet(LookupMap<FunctionSymbol> symbols) {
    if (symbols == null) throw new NullStorageException("Alphabet", "symbols list");
    _symbols = symbols;
  }

  /**
   * Create an alphabet with the given symbols.
   * Duplicate occurrences of the same function symbol are removed; duplicate occurrences of the
   * same type that are not the same symbol cause a TypingException to be produced.
   */
  public Alphabet(Collection<FunctionSymbol> symbols) {
    LookupMap.Builder<FunctionSymbol> builder = new LookupMap.Builder<FunctionSymbol>();
    if (symbols == null) throw new NullStorageException("Alphabet", "symbols list");
    for (FunctionSymbol f : symbols) {
      if (f == null) throw new NullStorageException("Alphabet", "a symbol");
      if (builder.containsKey(f.queryName())) {
        FunctionSymbol g = builder.get(f.queryName());
        if (!g.equals(f)) {
          throw new TypingException("Alphabet", "add", "duplicate occurrence of " +
            f.queryName(), g.queryType().toString(), f.queryType().toString());
        }
      }
      else builder.put(f.queryName(), f);
    }
    _symbols = builder.build();
  }

  /** Creates a copy of the alphabet, with the given function symbols added. */
  public Alphabet add(Collection<FunctionSymbol> toadd) {
    LookupMap.Builder<FunctionSymbol> builder = new LookupMap.Builder<FunctionSymbol>();
    for (FunctionSymbol f : _symbols.values()) builder.put(f.queryName(), f);
    for (FunctionSymbol f : toadd) {
      if (f == null) throw new NullStorageException("Alphabet", "an extra symbol");
      if (builder.containsKey(f.queryName())) {
        FunctionSymbol g = builder.get(f.queryName());
        if (!g.equals(f)) {
          throw new TypingException("Alphabet", "add", "duplicate occurrence of " +
            f.queryName(), g.queryType().toString(), f.queryType().toString());
        }
      }
      else builder.put(f.queryName(), f);
    }
    return new Alphabet(builder.build());
  }

  /** Returns the FunctionSymbol with the given name if it exists, or null otherwise. */
  public FunctionSymbol lookup(String name) {
    return _symbols.get(name);
  }

  /** Returns the set of all function symbols occurring in the alphabet. */
  public Collection<FunctionSymbol> getSymbols() {
    return _symbols.values();
  }

  /** Returns a pleasant-to-read string representation of the current alphabet. */
  public String toString() {
    StringBuilder ret = new StringBuilder("");
    for (FunctionSymbol symbol : _symbols.values()) {
      ret.append(symbol.queryName());
      ret.append(" : ");
      ret.append(symbol.queryType());
      ret.append("\n");
    }
    return ret.toString();
  }
}
