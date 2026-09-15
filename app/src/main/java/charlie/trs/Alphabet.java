/**************************************************************************************************
 Copyright 2024--2026 Cynthia Kop

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
import java.util.Map;
import java.util.Stack;

import charlie.util.FixedList;
import charlie.util.LookupMap;
import charlie.util.NullStorageException;
import charlie.types.*;
import charlie.terms.FunctionSymbol;
import charlie.terms.TypingException;
import charlie.theory.Theory;
import charlie.trs.TrsProperties.TypeLevel;

/**
 * The alphabet class specifically represents the TERMS alphabet.  It consists of:
 * - a set of sort constructors along with their arities
 * - a set of user-defined (possibly polymorphic) function symbols
 * - it also keeps track of the kinds of types used inside it
 * Both sets are finite and immutable.
 * Theory types and symbols are not included as these would be part of the THEORY alphabet.
 */
public class Alphabet {
  private final LookupMap<Integer> _sorts;
  private final LookupMap<FunctionSymbol> _symbols;
  private final TypeLevel _level; // SIMPLE, MONOMORPHIC or POLYMORPHIC

  /**
   * Creates an Alphabet with the given arities for each sort constructor and the given list of
   * symbols, whose type level is exactly level.  No consistency checks are done, since this is a
   * private constructor that should only be used in ways that keep sorts, symbols and level
   * consistent.
   */
  private Alphabet(LookupMap<Integer> sorts, LookupMap<FunctionSymbol> symbols, TypeLevel level) {
    _sorts = sorts;
    _symbols = symbols;
    _level = level;
  }

  /**
   * Creates an Alphabet with the given arities for each sort constructor, and the given list of
   * symbols.
   * Note that it is required that all sort constructors that occur in the type of any of the
   * symbols are in sorts, with the corresponding arity (with the exception of theory sorts, which
   * do not need to be included in the sorts list).  If this property fails, then an
   * IllegalSymbolException is thrown.
   */
  public Alphabet(LookupMap<Integer> sorts, LookupMap<FunctionSymbol> symbols) {
    if (sorts == null) throw new NullStorageException("Alphabet", "sort constructor mapping");
    if (symbols == null) throw new NullStorageException("Alphabet", "symbols list");
    _sorts = sorts;
    _symbols = symbols;
    // discover the type level of this alphabet
    TypeLevel level = TypeLevel.SIMPLE;
    for (Integer k : sorts.values()) {
      if (k > 0) level = TypeLevel.MONOMORPHIC;
    }
    for (FunctionSymbol f : symbols.values()) {
      if (!f.queryType().isMonomorphic()) {
        level = TypeLevel.POLYMORPHIC;
        break;
      }
    }
    _level = level;
    // check that the sort constructors used in the alphabet are all declared
    for (FunctionSymbol f : symbols.values()) {
      String problem = checkTypeDeclared(f.queryType());
      if (problem != null) {
        throw new IllegalSymbolException(f, "alphabet",
          sorts.containsKey(problem) ? "sort constructor " + problem + " previously occurred " +
            "with " + sorts.get(problem) + " arguments." : "sort constructor " + problem +
            " has not been declared.");
      }
    }
  }

  /**
   * Creates an Alphabet with the given symbols, and all the sort constructors that occur in these
   * symbols (not including the theory sorts).
   * The non-theory sort constructors that occur in the types of the symbols are stored and
   * checked for consistency; if sort arities are not consistent then an InconsistentSortException
   * is thrown.
   */
  public Alphabet(LookupMap<FunctionSymbol> symbols) {
    if (symbols == null) throw new NullStorageException("Alphabet", "symbols list");
    _symbols = symbols;
    LookupMap.Builder<Integer> builder = new LookupMap.Builder<Integer>();
    TypeLevel level = TypeLevel.SIMPLE;
    for (FunctionSymbol f : symbols.values()) {
      level = storeSortConstructorsInType(builder, f, level);
    }
    _level = level;
    _sorts = builder.build();
  }

  /**
   * Create an alphabet with the given sorts and symbols.
   * Duplicate occurrences of the same function symbol are removed; duplicate occurrences of the
   * same name that are not the same symbol cause a TypingException to be produced.
   * The sorts along with the non-theory sort constructors that occur in the types of the symbols
   * are stored and checked for consistency; if sort arities are not consistent then an
   * InconsistentSortException is thrown.
   */
  public Alphabet(Map<String,Integer> sorts, Collection<FunctionSymbol> symbols) {
    LookupMap.Builder<FunctionSymbol> symbolsBuilder = new LookupMap.Builder<FunctionSymbol>();
    LookupMap.Builder<Integer> sortsBuilder = new LookupMap.Builder<Integer>();
    for (String name : sorts.keySet()) sortsBuilder.put(name, sorts.get(name));
    _level = addSymbols(symbolsBuilder, sortsBuilder, symbols, TypeLevel.SIMPLE);
    _symbols = symbolsBuilder.build();
    _sorts = sortsBuilder.build();
  }

  /**
   * Create an alphabet with the given symbols.
   * Duplicate occurrences of the same function symbol are removed; duplicate occurrences of the
   * same name that are not the same symbol cause a TypingException to be produced.
   * The non-theory sort constructors that occur in the types of the symbols are stored and
   * checked for consistency; if sort arities are not consistent then an InconsistentSortException
   * is thrown.
   */
  public Alphabet(Collection<FunctionSymbol> symbols) {
    LookupMap.Builder<FunctionSymbol> symbolsBuilder = new LookupMap.Builder<FunctionSymbol>();
    LookupMap.Builder<Integer> sortsBuilder = new LookupMap.Builder<Integer>();
    _level = addSymbols(symbolsBuilder, sortsBuilder, symbols, TypeLevel.SIMPLE);
    _symbols = symbolsBuilder.build();
    _sorts = sortsBuilder.build();
  }

  /**
   * Creates a copy of the alphabet, with the given function symbols added (along with any new
   * non-theory sort constructors that may occur in them).
   */
  public Alphabet add(Collection<FunctionSymbol> toadd) {
    LookupMap.Builder<FunctionSymbol> symbolsBuilder = new LookupMap.Builder<FunctionSymbol>();
    LookupMap.Builder<Integer> sortsBuilder = new LookupMap.Builder<Integer>();
    for (FunctionSymbol f : _symbols.values()) symbolsBuilder.put(f.queryName(), f);
    for (String sort : _sorts.keySet()) sortsBuilder.put(sort, _sorts.get(sort));
    TypeLevel tlevel = addSymbols(symbolsBuilder, sortsBuilder, toadd, _level);
    return new Alphabet(sortsBuilder.build(), symbolsBuilder.build(), tlevel);
  }

  /**
   * Helper function for the constructors: this stores in builder that the given sort has the given
   * arity, provided there is not already an existing entry with a different arity, and returns
   * arity.
   *
   * If there is an existing entry with a different arity, then the builder is unchanged, and the
   * existing arity is returned.
   */
  private int storeSortConstructor(LookupMap.Builder<Integer> builder, String name, int arity) {
    if (builder.containsKey(name)) return builder.get(name);
    builder.put(name, arity);
    return arity;
  }

  /**
   * Helper function for the constructors: this stores all the sort constructors in the type of f
   * into the given builder, and throws an InconsistentSortException if there is an inconsistency.
   * (Theory sorts are not included.)  Moreover, the lowest type level that is ≥ tlevel and covers
   * all the types used in the type of f is returned.
   */
  private TypeLevel storeSortConstructorsInType(LookupMap.Builder<Integer> builder,
                                                FunctionSymbol f, TypeLevel tlevel) {
    Stack<Type> stack = new Stack<Type>();
    stack.add(f.queryType());
    while (!stack.isEmpty()) {
      int k;
      Type t = stack.pop();
      switch (t) {
        case Base(String name):
          if (Theory.isBaseTheoryType(t)) continue;
          k = storeSortConstructor(builder, name, 0);
          if (k != 0) {
            throw new InconsistentSortException(name, "function symbol " + f.queryName(), k, 0);
          }
          continue;
        case Data(String name, FixedList<Type> args):
          k = storeSortConstructor(builder, name, args.size());
          if (k != args.size()) {
            throw new InconsistentSortException(name, "function symbol " + f.queryName(),
                                                k, args.size());
          }
          for (Type arg : args) stack.push(arg);
          if (tlevel == TypeLevel.SIMPLE) tlevel = TypeLevel.MONOMORPHIC;
          continue;
        case Arrow(Type left, Type right):
          stack.push(left);
          stack.push(right);
          continue;
        case TVar(String name):
          tlevel = TypeLevel.POLYMORPHIC;
          continue;
      }
    }
    return tlevel;
  }

  /**
   * Helper function for one of the constructors, and the add function: this adds all the function
   * symbols in the given collection to the given symbolsBuilder, and the sort constructors
   * occurring in them to the given sortsBuilder.  The return value is the lowest type level
   * ≥ tlevel that covers the types of everything in symbols.
   */
  private TypeLevel addSymbols(LookupMap.Builder<FunctionSymbol> symbolsBuilder,
                               LookupMap.Builder<Integer> sortsBuilder,
                               Collection<FunctionSymbol> symbols, TypeLevel tlevel) {
    for (FunctionSymbol f : symbols) {
      if (f == null) throw new NullStorageException("Alphabet", "a symbol");
      if (symbolsBuilder.containsKey(f.queryName())) {
        FunctionSymbol g = symbolsBuilder.get(f.queryName());
        if (!g.equals(f)) {
          throw new TypingException("Duplicate occurrence of ", f, " in alphabet with different " +
            "types: ", f.queryType(), " and ", g.queryType(), ".");
        }
      }
      else symbolsBuilder.put(f.queryName(), f);
      tlevel = storeSortConstructorsInType(sortsBuilder, f, tlevel);
    }
    return tlevel;
  }

  /**
   * Returns null if all the type constructors in type are either theory sorts, or occur in the
   * alphabet with the used arity.  Returns the name of the illegal sort if not.
   */
  public String checkTypeDeclared(Type type) {
    Stack<Type> stack = new Stack<Type>();
    stack.add(type);
    while (!stack.isEmpty()) {
      Type t = stack.pop();
      switch (t) {
        case Base(String name):
          if (Theory.isBaseTheoryType(t)) continue;
          if (!_sorts.containsKey(name)) return name;
          if (_sorts.get(name) != 0) return name;
          continue;
        case Data(String name, FixedList<Type> args):
          if (!_sorts.containsKey(name)) return name;
          if (_sorts.get(name) != args.size()) return name;
          for (Type arg : args) stack.push(arg);
          continue;
        case Arrow(Type left, Type right):
          stack.push(left);
          stack.push(right);
          continue;
        case TVar(String name):
          continue;
      }
    }
    return null;
  }

  /** Returns the FunctionSymbol with the given name if it exists, or null otherwise. */
  public FunctionSymbol lookup(String name) {
    return _symbols.get(name);
  }

  /** Returns the set of all function symbols occurring in the alphabet. */
  public Collection<FunctionSymbol> getSymbols() {
    return _symbols.values();
  }

  /**
   * Returns the arity of the given sort constructor, or -1 if the sort constructor is not in the
   * current alphabet.
   */
  public int querySortConstructorArity(String name) {
    if (!_sorts.containsKey(name)) return -1;
    return _sorts.get(name);
  }

  /** Returns the names of the sort constructors declared in the alphabet. */
  public Collection<String> getSortConstructors() {
    return _sorts.keySet();
  }

  /** Returns the maximum type level used by any sort used or declared in the alphabet. */
  public TypeLevel queryTypes() {
    return _level;
  }

  /**
   * Returns a pleasant-to-read string representation of the current alphabet.
   * Note that this should only be used for debugging and unit testing: otherwise, alphabets should
   * be printed using an instance of charlie.printer.Printer.
   */
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
