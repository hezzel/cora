package charlie.util;

import java.util.*;

/**
 * A Renamer allows its user to construct a bijective mapping between
 * existing names and new names. New names are guaranteed to be
 * different from existing names. Also allows for specifying forbidden
 * names that must not be created as new names from then on.
 * <p>
 * Implementation note: the mapping ceases to be bijective when 2^32 created or
 * forbidden names are stored internally. At present (Oct 2024) memory limits
 * are likely to be exceeded before this occurs.
 */
public class Renamer {
  /** Names that shall from now on not be assigned as new names. */
  private final Set<String> _forbiddenNames;

  private final Map<String, String> _oldToNew;
  private final Map<String, String> _newToOld;

  /**
   * Creates a fresh Renamer without any pre-existing mapping and any
   * forbidden names.
   */
  public Renamer() {
    _forbiddenNames = new LinkedHashSet<>();
    _oldToNew = new LinkedHashMap<>();
    _newToOld = new LinkedHashMap<>();
  }

  /**
   * Adds the method parameter to names that will from now on not be used as
   * new names. However, if an element of the method parameter has already
   * been assigned as a new name, that assignment is not changed.
   *
   * @param name will not be returned as new name in the future
   */
  public void addForbiddenName(String name) {
    _forbiddenNames.add(name);
  }

  /**
   * Adds the content of the method parameter to names that will from now on
   * not be used as new names. However, if an element of the method parameter
   * has already been assigned as a new name, that assignment is not changed.
   *
   * @param names content will not be returned as new names in the future;
   *              will not be altered by this method call
   * @throws NullPointerException if names is null
   */
  public void addForbiddenNames(Collection<String> names) {
    _forbiddenNames.addAll(names);
  }

  /**
   * Assigns a new name to oldName unless one has already been assigned.
   * Returns that new name. No forbidden name will be newly assigned.
   *
   * @param oldName the String for which we would like a new name
   * @return a fresh new name, currently not marked as forbidden, for oldName
   *  if this is the first call of the method on oldName; the previously
   *  returned name otherwise
   */
  public String assignOrGetNewName(String oldName) {
    String newName = _oldToNew.get(oldName);
    if (newName != null) {
      return newName;
    }
    if (_forbiddenNames.contains(oldName)) {
      newName = makeNewName(oldName);
    }
    _oldToNew.put(oldName, newName);
    _newToOld.put(newName, oldName);
    _forbiddenNames.add(oldName);
    _forbiddenNames.add(newName);
    return newName;
  }

  public String getOldName(String newName) {
    return _newToOld.get(newName);
  }

  private String makeNewName(String oldName) {
    int counter = 0;
    String newName;
    do {
      newName = oldName + counter;
      ++counter;
    } while (_forbiddenNames.contains(newName));
    return newName;
  }
}
