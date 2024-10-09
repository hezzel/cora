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

package cora.termination.dependency_pairs.processors.redpair;

import charlie.util.LookupMap;
import charlie.util.Pair;
import charlie.types.*;
import charlie.terms.*;
import charlie.trs.Alphabet;

import java.util.ArrayList;
import java.util.TreeMap;
import java.util.TreeSet;
import java.util.Map;

/**
 * A helper class for URWrtRedPairProcessor that keeps track of a mapping (f,n) ⇒  f_n, where f_n
 * a first-order function symbol of arity n.  All f_n are chosen with distinct names, and with a
 * sort as output type and for all input types.  The class automatically generates new symbols
 * (f,n) where needed, and can be queried for a resulting alphabet.
 */
class AlphabetMap {
  private TreeMap<FunctionSymbol,TreeMap<Integer,FunctionSymbol>> _translation;
  private TreeSet<String> _used;
  private static final String BULLETSTR = "$";

  /** Creates an empty map */
  AlphabetMap() {
    _translation = new TreeMap<FunctionSymbol,TreeMap<Integer,FunctionSymbol>>();
    _used = new TreeSet<String>();
    _used.add(BULLETSTR);
  }
  
  /**
   * Primary access function: this returns the function symbol for (f,n). 
   * If (f,n) has been requested before, this returns the symbol as then; otherwise it returns a
   * fresh symbol.
   */
  public FunctionSymbol getTranslation(FunctionSymbol f, int n) {
    TreeMap<Integer,FunctionSymbol> map = _translation.get(f);
    if (map == null) {
      map = new TreeMap<Integer,FunctionSymbol>();
      _translation.put(f, map);
    }
    else {
      FunctionSymbol ret = map.get(n);
      if (ret != null) return ret;
    }
    FunctionSymbol g = generateFresh(f, n);
    _used.add(g.queryName());
    map.put(n, g);
    return g;
  }

  /** Returns the Alphabet consisting of all function symbols created in this object */
  public Alphabet generateAlphabet() {
    LookupMap.Builder<FunctionSymbol> builder = new LookupMap.Builder<FunctionSymbol>();
    for (Map.Entry<FunctionSymbol,TreeMap<Integer,FunctionSymbol>> p1 : _translation.entrySet()) {
      for (Map.Entry<Integer,FunctionSymbol> p2 : p1.getValue().entrySet()) {
        FunctionSymbol g = p2.getValue();
        builder.put(g.queryName(), g);
      }
    }
    return new Alphabet(builder.build());
  }

  /** Returns a list of all pairs ( (f,n), f_n ) in the map. */
  public ArrayList<Pair<Pair<FunctionSymbol,Integer>,FunctionSymbol>> getAll() {
    ArrayList<Pair<Pair<FunctionSymbol,Integer>,FunctionSymbol>> ret =
      new ArrayList<Pair<Pair<FunctionSymbol,Integer>,FunctionSymbol>>();
    for (Map.Entry<FunctionSymbol,TreeMap<Integer,FunctionSymbol>> p1 : _translation.entrySet()) {
      FunctionSymbol f = p1.getKey();
      for (Map.Entry<Integer,FunctionSymbol> p2 : p1.getValue().entrySet()) {
        int n = p2.getKey();
        FunctionSymbol g = p2.getValue();
        ret.add(new Pair<Pair<FunctionSymbol,Integer>,FunctionSymbol>(
          new Pair<FunctionSymbol,Integer>(f,n),g));
      }
    }
    return ret;
  }

  /**
   * Generates a new function symbol with a unique name to represent f_n.
   */
  private FunctionSymbol generateFresh(FunctionSymbol f, int n) {
    String name = f.queryName() + n;
    if (_used.contains(name)) {
      name = f.queryName() + "_" + n;
      while (_used.contains(name)) name = name + "'";
    }
    Type type = f.queryType();
    ArrayList<Base> args = new ArrayList<Base>(n);
    for (int i = 1; i <= n; i++) {
      args.add(sortFor(type.subtype(1)));
      type = type.subtype(2);
    }
    Type rettype = TypeFactory.createSortDeclaration(args, sortFor(type));
    FunctionSymbol g = TermFactory.createConstant(name, rettype);
    return g;
  }

  public FunctionSymbol generateBulletSymbol(Type t) {
    return TermFactory.createConstant(BULLETSTR, sortFor(t));
  }

  /** This creates a unique base type for the given type. */
  public Base sortFor(Type type) {
    if (type instanceof Base b) return b;   // so theory sorts stay theory sorts!
    return TypeFactory.createSort("[" + type.toString() + "]");
  }
}

