/**************************************************************************************************
 Copyright 2024--2025 Cynthia Kop

 Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 in compliance with the License.
 You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software distributed under the
 License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 express or implied.
 See the License for the specific language governing permissions and limitations under the License.
 *************************************************************************************************/

package charlie.terms.replaceable;

import java.util.TreeMap;
import java.util.TreeSet;
import java.util.Set;
import charlie.util.Pair;
import charlie.util.NullStorageException;
import charlie.terms.replaceable.Replaceable;

/**
 * A MutableRenaming is a finite Renaming that can be changed, both with items added and removed.
 * A MutableRenaming also carries a list of "forbidden" names that may not be used, but this is
 * guaranteed to be finite, so users can always iterate to find a suitable name for a new
 * Replaceable that is neither used yet nor forbidden.
 */
public class MutableRenaming implements Renaming {
  /** Maps the (meta-)variables in the domain of this renaming to unique names. */
  private TreeMap<Replaceable,String> _repToName;
  /** Maps the names to their corresponding (meta-)variable. */
  private TreeMap<String,Replaceable> _nameToRep;
  /** Names that may not be used in an assignment. */
  private TreeSet<String> _avoid;
  
  /**
   * Creates a renaming that avoids the given set of names.
   * The given set of blocked names is guaranteed to not be altered, nor will it be saved; we only
   * make a copy for internal use.
   */
  public MutableRenaming(Set<String> blockedNames) {
    _repToName = new TreeMap<Replaceable,String>();
    _nameToRep = new TreeMap<String,Replaceable>();
    _avoid = new TreeSet<String>(blockedNames);
  }

  /**
   * Adds a name to the list of names that should be avoided (that is, the names that will be
   * blocked in setName, and for which isAvailable should return false).
   *
   * Note that marking a name as avoidable will not remove it from the mapping if there's already
   * a Replaceable with that name.
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
    Replaceable y = _nameToRep.get(name);
    if (y != null && y != x) return false;
    // we can store it!
    String origName = _repToName.get(x);
    if (origName != null) _nameToRep.remove(origName);
    _repToName.put(x, name);
    _nameToRep.put(name, x);
    return true;
  }

  /**
   * This removes the name of the given replaceable from the mapping, and makes it available for
   * other replaceables again.
   */
  public void unsetName(Replaceable x) {
    String name = _repToName.get(x);
    if (name == null) return;
    _repToName.remove(x);
    _nameToRep.remove(name);
  }
  
  /** Returns the chosen name for the given replaceable, or null if it's not in the domain. */
  public String getName(Replaceable x) {
    return _repToName.get(x);
  }

  /** Returns the replaceable with the given name, if there is one; null if not. */
  public Replaceable getReplaceable(String name) {
    return _nameToRep.get(name);
  }

  /** Returns the replaceables this Renaming gives a name to. */
  public Set<Replaceable> domain() {
    return _repToName.keySet();
  }

  /** Returns the names used in this Renaming. */
  public Set<String> range() {
    return _nameToRep.keySet();
  }

  /**
   * Returns whether the given name is available to be used for further renamings.
   * (The renaming is set up so that any name that is already in use is not available, along
   * with the "avoid" names given in the TermPrinter's constructor, and potentially some other
   * names).
   */
  public boolean isAvailable(String name) {
    return !_avoid.contains(name) && _nameToRep.get(name) == null;
  }

  /** Makes a copy of the current renaming, so one can be changed without affecting the other. */
  public MutableRenaming copy() {
    MutableRenaming ret = new MutableRenaming(_avoid);
    ret._repToName.putAll(_repToName);
    ret._nameToRep.putAll(_nameToRep);
    return ret;
  }

  /** Puts a wrapper around the current Renaming to make it immutable. */
  public Renaming makeImmutable() {
    return new ImmutableRenaming(this);
  }

  /** Limits the Renaming to only the replaceables that occur in any of the given lists. */
  public void limitDomain(ReplaceableList ...lists) {
    TreeSet<Replaceable> remove = new TreeSet<Replaceable>();
    for (Replaceable r : _repToName.keySet()) {
      boolean ok = false;
      for (ReplaceableList l : lists) {
        if (l.contains(r)) {
          ok = true;
          break;
        }
      }
      if (!ok) remove.add(r);
    }
    for (Replaceable r : remove) unsetName(r);
  }
}

