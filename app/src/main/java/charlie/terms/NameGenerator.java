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
import charlie.types.Type;
import charlie.terms.replaceable.Replaceable;
import charlie.terms.replaceable.Renaming;
import charlie.terms.replaceable.MutableRenaming;

/**
 * NameGenerators are used to create Renamings by assigning a suitable name for every replaceable
 * in a given set (or: in a given set of terms).
 *
 * While NameGenerators are designed to be inherited, the default NameGenerator is intended to
 * suffice for many practical purposes: it keeps the original name of replaceables where this can
 * be done without ambiguity (so as to keep them in line with user expectations), and if there are
 * multiple replaceables of the same name (or if the variable's original name is blocked for some
 * reason) adds a subscript to this name.  It will also avoid a given (finite!) set of names.  This
 * is primarily intended to be used to avoid the names of function symbols, but may also be used
 * for other purposes.  If a replaceable is renamed then its original name is also marked as
 * "avoid" to prevent confusion.
 *
 * For alternative behaviour, programmers can inherit the NameGenerator and override some of the
 * public or protected functions as needed.  Instructions are provided in the comments.
 *
 * (Note that if the alphabet is infinite, it is the responsibility of the programmer to use a
 * NameGenerator that avoids all function symbol names.  For example, the default functionality
 * will avoid using integers or strings as variable names, but inheriting classes might make their
 * own choices in this regard.)
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
   * Bound variables are not included, as these are handled through the generateBoundName function.
   * If you do want them included, add all the bound variables as separate terms to the list
   * (but note that in that case, they will be named in the same way as free binder variables).
   *
   * The default implementation tries to use the given name of the replacable for every replaceable
   * whose name occurs only once in the given set of terms, and if that name is not available (or
   * there are multiple free replaceables with the same name) it tries the first occurrence of
   * createSubscript(nae, index) that works (where index ≥ 1).  This is altered if the name is
   * prohibited for instance because it's not alpha-numeric, or is an integer.
   *
   * For inheriting classes: the default implementation just creates a new MutableRenaming using
   * the known blocked names, and then calls extendShared.  If an inheriting class wants
   * generateUniqueNaming and extend to behave differently, mask these individual functions;
   * otherwise just mask extendShared!
   */
  public MutableRenaming generateUniqueNaming(List<Term> terms) {
    MutableRenaming ret = new MutableRenaming(_blockedNames);
    extendShared(ret, terms);
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
   * Bound variables are not included, as these are handled through the generateBoundName function.
   * If you do want them included, add all the bound variables as separate terms to the list
   * (but note that in that case, they will be named in the same way as free binder variables).
   *
   * The default implementation tries to use the given name of the replacable for every replaceable
   * whose name occurs only once in the given set of terms, and if that name is not available (or
   * there are multiple new replaceables with that name) it tries the first occurrence of
   * createSubscript(name, index) that works (where index ≥ 1).  This is altered if the name is
   * prohibited for instance because it's not alpha-numeric, or is an integer.
   *
   * For inheriting classes: the default implementation just calls extendShared.  If an inheriting
   * class wants generateUniqueNaming and extend to behave differently, mask these individual
   * functions; otherwise just mask extendShared.
   */
  public void extend(MutableRenaming renaming, List<Term> terms) {
    extendShared(renaming, terms);
  }

  /**
   * This method implements the default functionality of generateUniqueNaming and extend.
   *
   * This works as follows:
   * - first, all names that occur only once, and whose default name is permitted (according to
   *   queryPermittedName()), it is given the name returned by chooseNameForUniqueReplaceable()
   *   so long as this name is available (and the function does not return null)
   * - second, for names that occur only once, but which are not permitted according to
   *   queryPermittedName(), we choose a variant of their name using fixNonPermittedName() and
   *   then assign it the name returned by chooseNameForUniqueReplaceable() so long as this name
   *   is available (and the function does not return null)
   * - third, for all remaining replaceables:
   *   + we let prefix be their default name if this is permitted according to
   *     queryPermittedName(); otherwise we let prefix be a variant chosen by fixNonPermittedName()
   *   + we iterate from 1 upwards, and return the first result of chooseNameForAmbiguousReplaceable
   *     that returns non-null and is available!
   *
   * Moreover, all original names of replaceables which are not used as names are marked as blocked
   * in the renaming.
   *
   * If this default functionality suffices, inheriting classes can simply override
   * queryPermittedName(), fixNonPermittedName(), chooseNameForUniqueReplaceable() and
   * chooseNameForAmbiguousReplaceable().  If it does not, they should override this function and
   * can leave the others alone (as they are only called by this method).
   */
  protected void extendShared(MutableRenaming renaming, List<Term> terms) {
    TreeSet<Replaceable> allNewReplaceables = getAllNewReplaceables(terms, renaming);
    nameUniques(renaming, getUniqueNames(allNewReplaceables, renaming));
    nameRemainder(renaming, allNewReplaceables);
    blockOriginalNames(renaming, allNewReplaceables);
  }

  /**
   * This function will return a suggested name for a bound variable.  This will always be a name
   * that is still available in the given renaming.  The name will be immediately stored in the
   * renaming.
   *
   * By default, this will return the binder's name (or its fixed variant if this name is not
   * permitted) if this is available, otherwise createSubscript(name, index), where index is the
   * first integer so that this subscript-name is still available.
   */
  public String generateBoundName(MutableRenaming renaming, Variable binder) {
    String n = binder.queryName();
    if (!queryPermittedName(n)) n = fixNonPermittedName(binder);
    if (renaming.isAvailable(n)) {
      renaming.setName(binder, n);
      return n;
    }
    for (int index = 1; ; index++) {
      String name = createSubscript(n, index);
      if (renaming.isAvailable(name)) {
        renaming.setName(binder, name);
        return name;
      }
    }
  }

  /**
   * Helper function for extendShared: this stores chooseNameForUniqueReplaceable for each of the
   * replaceables in uniqueReplaceables, either with its own name or with the result of
   * fixNonPermittedName().  This is only done if the name is available (and if
   * chooseNameForUniqueReplaceable returns non-null).
   */
  private void nameUniques(MutableRenaming renaming, Collection<Replaceable> uniqueReplaceables) {
    TreeSet<Replaceable> rest = new TreeSet<Replaceable>();
    for (Replaceable x : uniqueReplaceables) {
      String n = x.queryName();
      if (queryPermittedName(n)) {
        n = chooseNameForUniqueReplaceable(x, n);
        if (n != null && renaming.isAvailable(n)) renaming.setName(x, n);
      }
      else rest.add(x);
    }
    for (Replaceable x : rest) {
      String n = chooseNameForUniqueReplaceable(x, fixNonPermittedName(x));
      if (n != null && renaming.isAvailable(n)) renaming.setName(x, n);
    }
  }

  /**
   * Helper function for extendShared: for all replaceables in replaceables that have not yet been
   * assigned a name, this iterates upwards from 1 and returns the first result of
   * chooseNameForAmbiguousReplaceable that is non-null and available.
   */
  private void nameRemainder(MutableRenaming renaming, TreeSet<Replaceable> replaceables) {
    TreeMap<String,Integer> next = new TreeMap<String,Integer>();
    for (Replaceable x : replaceables) {
      if (renaming.getName(x) != null) continue;  // we already handled this one!
      String name = x.queryName();
      if (!queryPermittedName(name)) name = fixNonPermittedName(x);
      if (!next.containsKey(name)) next.put(name, 1);
      for (int k = next.get(name); ; k++) {
        String n = chooseNameForAmbiguousReplaceable(x, name, k);
        if (!renaming.isAvailable(n)) continue;
        renaming.setName(x, n);
        next.put(name, k + 1);
        break;
      }
    }
  }

  /**
   * Helper function for extendShared: for all given replaceables, if their original or fixed name
   * is still available in the renaming, it is now marked blocked, so future variables will not be
   * given that name.
   */
  private void blockOriginalNames(MutableRenaming renaming, TreeSet<Replaceable> replaceables) {
    for (Replaceable x : replaceables) {
      String n = x.queryName();
      if (renaming.isAvailable(n)) renaming.avoid(n);
      if (!queryPermittedName(n)) {
        n = fixNonPermittedName(x);
        if (renaming.isAvailable(n)) renaming.avoid(n);
      }
    }
  }


  /**
   * Helper function for the default implementation of extendShared.  This checks if it's a good
   * idea to use name unmodified as either a full name for a (meta-)variable or as the "original"
   * name in a call to chooseNameForAmbiguousReplaceable.
   *
   * If you override this, also override fixNonPermittedName to match!
   */
  protected boolean queryPermittedName(String name) {
    if (name == null || name.equals("")) return false;
    char c = name.charAt(0);
    return (c == '#' || c == '?' || c == '_' || c >= 128 ||
             (c >= 'A' && c <= 'Z') ||
             (c >= 'a' && c <= 'z')
           );
  }

  /**
   * Helper function for the default implementation of extendShared.
   *
   * Given that queryPermittedName(r.queryName()) returns false, this function is tasked to come up
   * with a new name for the given replaceable.  This name may be used either directly, or as the
   * "original" name in a call to chooseNameForAmbiguousReplaceable.
   */
  protected String fixNonPermittedName(Replaceable r) {
    String name = r.queryName();
    if (name == null || name.equals("")) return "VAR";
    return "_" + name;
  }

  /**
   * Helper function for the default implementation of extendShared.  This function returns a name
   * for a variable or meta-variable that *could* be given the given name (which is either its own
   * original name or derived from it) without ambiguity, so long as it's available.
   *
   * The default functionality is to simply return this name.  However, overriding classes may wish
   * to do something different (e.g., add extra information).
   */
  protected String chooseNameForUniqueReplaceable(Replaceable r, String name) {
    return name;
  }

  /**
   * Helper function for the default implementation of extendShared.  This function returns a name
   * for a variable or meta-variable that should probably not be given its original name, as it
   * would lead to ambiguity.  Instead, for every increasing index a different name should be
   * returned.
   *
   * The default implementation is just to return createSubscript(name, index).
   *
   * @param r the (meta-)variable to be named
   * @param name the name of the variable, possible altered through fixNonPermittedName
   * @param index a number ≥ 1; this function will be called with increasing indexes until a
   *   string is returned that is available (permissability of the result will not be checked).
   */
  protected String chooseNameForAmbiguousReplaceable(Replaceable r, String name, int index) {
    return createSubscript(name, index);
  }

  /**
   * This function is used both by the default implementation of chooseNameForAmbiguousReplaceable
   * and generateBoundName to create a subscripted name.  By default, this just returns name__index
   * but it can be masked to return something different based on preference (for example, in an
   * HTML printer this could return name + "<sub>" + index + "</sub>").
   */
  protected String createSubscript(String name, int index) {
    return name + "__" + index;
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
}

