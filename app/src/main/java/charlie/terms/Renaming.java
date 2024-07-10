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

package charlie.terms;

import java.util.TreeMap;
import java.util.TreeSet;
import java.util.Set;
import charlie.exceptions.NullStorageException;
import charlie.util.Pair;

/**
 * Renamings are used by TermPrinters to give each (meta-)variable in a given term or set of terms
 * a unique name.  They can also be used to look up (meta-)variables by their name.
 */
public class Renaming {
  /** Maps the (meta-)variables in the domain of this renaming to unique names. */
  private TreeMap<Replaceable,String> _varToName;
  /** Maps the names to their corresponding (meta-)variable. */
  private TreeMap<String,Replaceable> _nameToVar;
  /** Names that may not be used in an assignment. */
  private TreeSet<String> _avoid;
  
  /**
   * Creates a renaming that avoids the given set of names.
   * The given set of blocked names is guaranteed to not be altered or saved.
   */
  public Renaming(Set<String> blockedNames) {
    _varToName = new TreeMap<Replaceable,String>();
    _nameToVar = new TreeMap<String,Replaceable>();
    _avoid = new TreeSet<String>(blockedNames);
  }

  /**
   * Adds a name to the list of names that should be avoided (that is, the names that will be
   * blocked in setName, and for which isAvailable should return false).
   *
   * Note that marking a name is avoidable will not remove it from the mapping if there's already
   * a replaceable with that name.
   */
  public void avoid(String name) {
    _avoid.add(name);
  }

  /**
   * This tries to set the name of the given replaceable to the given name.  If this is not
   * possible -- either because the given name is already in use, or because it's blocked -- then
   * false is returned. If it is possible, then the name is set and true is returned.
   *
   * Note that this works both if x already has a name (in which case the name is changed, and the
   * old name becomes available again), and if x is new to the Renaming.
   */
  public boolean setName(Replaceable x, String name) {
    if (x == null || name == null) {
      throw new NullStorageException("Renaming", "replaceable or name");
    }
    if (_avoid.contains(name)) return false;
    Replaceable y = _nameToVar.get(name);
    if (y != null && y != x) return false;
    // we can store it!
    String origName = _varToName.get(x);
    if (origName != null) _nameToVar.remove(origName);
    _varToName.put(x, name);
    _nameToVar.put(name, x);
    return true;
  }

  /**
   * This removes the name of the given replaceable from the mapping, and makes it available for
   * other replaceables again.
   */
  public void unsetName(Replaceable x) {
    String name = _varToName.get(x);
    if (name == null) return;
    _varToName.remove(x);
    _nameToVar.remove(name);
  }
  
  /** Returns the chosen name for the given replaceable, or null if it's not in the domain. */
  public String getName(Replaceable x) {
    return _varToName.get(x);
  }

  /** Returns the replaceable with the given name, if there is one; null if not. */
  public Replaceable getReplaceable(String name) {
    return _nameToVar.get(name);
  }

  /** Returns the replaceables this Renaming gives a name to. */
  public Set<Replaceable> domain() {
    return _varToName.keySet();
  }

  /** Returns the names used in this Renaming. */
  public Set<String> range() {
    return _nameToVar.keySet();
  }

  /**
   * Returns the variable with the given name, if there is one; null if not.
   * Note that if the given name is held by a meta-variable with arity > 0, then null is also
   * returned since there is no _variable_ with the given name.
   */
  public Variable getVariable(String name) {
    Replaceable ret = _nameToVar.get(name);
    if (ret != null && ret instanceof Variable) return (Variable)ret;
    return null;
  }
  
  /**
   * Returns whether the given name is available to be used for further renamings.
   * (The renaming is set up so that any name that is already in use is not available, along
   * with the "avoid" names given in the TermPrinter's constructor, and potentially some other
   * names).
   */
  public boolean isAvailable(String name) {
    return !_avoid.contains(name) && _nameToVar.get(name) == null;
  }

  /** Makes a copy of the current renaming, so one can be changed without affecting the other. */
  public Renaming copy() {
    Renaming ret = new Renaming(_avoid);
    ret._varToName.putAll(_varToName);
    ret._nameToVar.putAll(_nameToVar);
    return ret;
  }

  /**
   * Creates a copy of the current Renaming that has a name only for the replaceables that occur
   * in any of the terms in the given term list.  Replaceables that occur in these terms but do NOT
   * occur in the current Renaming, are put in the set that is the second returned argument.
   */
  public Pair<Renaming,Set<Replaceable>> copyFor(Term ...terms) {
    Renaming ret = new Renaming(_avoid);
    TreeSet<Replaceable> newReplaceables = new TreeSet<Replaceable>();
    for (Term s : terms) {
      for (Replaceable x : s.freeReplaceables()) {
        if (ret._varToName.get(x) != null || newReplaceables.contains(x)) continue;
        if (_varToName.get(x) == null) {
          newReplaceables.add(x);
          continue;
        }
        ret.setName(x, _varToName.get(x));
      }
    }
    return new Pair<Renaming,Set<Replaceable>>(ret, newReplaceables);
  }
}

