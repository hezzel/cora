/**************************************************************************************************
 Copyright 2025--2026 Cynthia Kop

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

import java.util.Arrays;
import java.util.Collection;
import java.util.List;
import java.util.TreeMap;
import java.util.TreeSet;
import java.util.function.Predicate;
import charlie.types.Type;
import charlie.terms.replaceable.Replaceable;
import charlie.terms.replaceable.Renaming;
import charlie.terms.replaceable.MutableRenaming;

/**
 * NameGenerators are used to create Renamings by assigning a suitable name for every replaceable
 * in a given set (or: in a given set of terms).
 *
 * NameGenerators are designed to be inherited, so different ways of choosing names can be used for
 * different applications.  They will always avoid a given (finite!) set of names.  This is intended
 * to be used to avoid the names of function symbols, but may also be used for other purposes.
 *
 * (Note that if the alphabet is infinite, it is the responsibility of the programmer to use a
 * NameGenerator that avoids function symbol names.  For example, the default functionality will
 * avoid using integers or strings as variable names, but inheriting classes might make their own
 * choices in this regard.)
 */
public class NameGenerator {
  private TreeSet<String> _blockedNames;  // the names that may not be used as variable names

  /**
   * Generates a NameGenerator that does not avoid any names (unless added by avoidAdditional).
   */
  public NameGenerator() {
    _blockedNames = new TreeSet<String>();
  }

  /**
   * Generates a NameGenerator that avoids the names in the given set (i.e., these will not be used
   * as generated names).  This is intended for instance to be used for the symbols in the alphabet.
   */
  public NameGenerator(Collection<String> avoid) {
    _blockedNames = new TreeSet<String>(avoid);
  }

  /**
   * Adds a single name to the list of names to avoid when generating names.  Note that this does
   * not affect existing renamings that have been created with this NameGenerator, only new ones!
   */
  public final void avoidAdditional(String name) {
    _blockedNames.add(name);
  }

  /**
   * Adds names to the list of strings to avoid when generating variable names.
   * Note that this does not affect existing renamings (even if you have not generated any names
   * with them yet), only ones that will be created after this function was called!
   */
  public final void avoidAdditional(Collection<String> names) {
    _blockedNames.addAll(names);
  }
  
  /**
   * This access function to generateUniqueNaming can be called with an arbitrary number of
   * term arguments.
   */
  public final MutableRenaming generateUniqueNaming(Term ...terms) {
    return generateUniqueNaming(Arrays.asList(terms));
  }

  /**
   * This function generates a renaming for all the free variables and meta-variables in the given
   * set of terms.  This means all distinct replaceables will be given a distinct name in the
   * result, regardless of their default name.
   *
   * Bound variables are not included.  When printing a term, these should be handled separately,
   * but this can be done using the generateBinderName function.
   *
   * The default implementation tries to use the given name of the replacable for every replaceable
   * whose name occurs only once in the given set of terms, and if that name is not available tries
   * the first occurrence of name__index that works (where index ≥ 1).
   *
   * Inheriting classes may override this method to generate names in an alternative way.
   */
  public MutableRenaming generateUniqueNaming(List<Term> terms) {
    MutableRenaming ret = new MutableRenaming(_blockedNames);
    extendPrivate(ret, terms);
    return ret;
  }

  /**
   * This function extends the given renaming by adding names for all the free variables and
   * meta-variables in the given set of terms (which do not already occur in the given renaming).
   *
   * This means that:
   * - all existing replaceables will keep their current name
   * - additional replaceables will be given a new name, distinct from the existing ones and
   *   each other (and choosing only names that are not blocked in the given renaming).
   *
   * Bound variables are not included.  When printing a term, these should be handled separately,
   * but this can be done using the generateBinderName function.
   *
   * The default implementation tries to use the given name of the replacable for every replaceable
   * whose name occurs only once in the given set of terms, and if that name is not available tries
   * the first occurrence of name__index that works (where index ≥ 1).
   *
   * Inheriting classes may override this method to generate names in an alternative way.
   */
  public void extend(MutableRenaming renaming, List<Term> terms) {
    extendPrivate(renaming, terms);
  }

  /** This method implements the default functionality of generateUniqueNaming and extend. */
  private void extendPrivate(MutableRenaming renaming, List<Term> terms) {
    TreeSet<Replaceable> allNewReplaceables = getAllNewReplaceables(terms, renaming);
    // first set names for the ones whom we can give their own name without obvious ambiguity
    for (Replaceable x : getUniqueNames(allNewReplaceables, renaming)) {
      String n = fixName(x.queryName());
      if (renaming.isAvailable(n)) renaming.setName(x, n);
        // no else; if the replaceable is not handled here, it will be done in the next loop
    }
    // now do the remainder!
    TreeMap<String,Integer> next = new TreeMap<String,Integer>();
    for (Replaceable x : allNewReplaceables) {
      if (renaming.getName(x) != null) continue;  // we already handled this one!
      String name = fixName(x.queryName());
      if (!next.containsKey(name)) next.put(name, 1);
      for (int k = next.get(name); ; k++) {
        String n = name + "__" + k;
        if (!renaming.isAvailable(n)) continue;
        renaming.setName(x, n);
        next.put(name, k + 1);
        break;
      }
    }
  }

  /**
   * Helper function: this function returns all replaceables that occur free in the given list of
   * terms which are not already in the renaming. (There are no side effects, and the caller is
   * allowed to use or change the returned set at its leisure.)
   */
  protected final TreeSet<Replaceable> getAllNewReplaceables(List<Term> terms, Renaming renaming) {
    TreeSet<Replaceable> ret = new TreeSet<Replaceable>();
    for (Term t : terms) {
      for (Replaceable x : t.freeReplaceables()) {
        if (renaming.getName(x) == null) ret.add(x);
      }
    }
    return ret;
  }

  /**
   * Helper function: this function returns the subset of replaceables whose name (a) does not
   * occur in the "existing" renaming, and (b) occurs only once in the given set.
   */
  protected final Collection<Replaceable> getUniqueNames(Collection<Replaceable> replaceables,
                                                         Renaming existing) {
    TreeMap<String,Replaceable> uniques = new TreeMap<String,Replaceable>();
    TreeSet<String> bad = new TreeSet<String>();
    for (Replaceable x : replaceables) {
      String n = x.queryName();
      if (existing.getReplaceable(n) != null) continue;
      if (bad.contains(n)) continue;
      if (uniques.containsKey(n)) {
        bad.add(n);
        uniques.remove(n);
      }
      else uniques.put(n, x);
    }
    return uniques.values();
  }

  /**
   * Helper function for the default implementation of generateUniqueNaming and extend: if the given
   * name starts with a character that seems likely to cause confusion (that is, make an identifier
   * not be recognised as a variable), this puts a _ in front of it; the result is returned.
   *
   * This is quite arbitrary, so this is private functionality; if someone wants to override
   * generateName, they can implement their own preferences!
   */
  private String fixName(String name) {
    if (name == null || name.equals("")) return "VAR";
    char c = name.charAt(0);
    if (c == '#' || c == '?') return name;
    if (c >= 'A' && c <= 'Z') return name;
    if (c >= 'a' && c <= 'z') return name;
    if (c >= 128) return name;
    return "_" + name;
  }
}

