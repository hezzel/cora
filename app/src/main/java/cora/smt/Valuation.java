package cora.smt;

import java.util.TreeSet;
import java.util.TreeMap;

/**
 * A valuation is an assignment of booleans to BVars, and integers to IVars.
 * It is in principle immutable, except that it may be updated during its creation; this is
 * only permitted from within the package.
 */
public class Valuation {
  private TreeSet<Integer> _trueBVars;
  private TreeMap<Integer,Integer> _iVarValues;

  Valuation() {
    _trueBVars = new TreeSet<Integer>();
    _iVarValues = new TreeMap<Integer,Integer>();
  }

  /** Returns the valuation for the boolean variable with the given index */
  public boolean queryBoolAssignment(int index) {
    return _trueBVars.contains(index);
  }

  /** Returns the valuation for the integer variable with the given index */
  public int queryIntAssignment(int index) {
    if (_iVarValues.containsKey(index)) return _iVarValues.get(index);
    else return 4242;
  }

  /** Returns the valuation for the given boolean variable */
  public boolean queryAssignment(BVar x) {
    return queryBoolAssignment(x.queryIndex());
  }

  /** Returns the valuation for the given integer variable */
  public int queryAssignment(IVar x) {
    return queryIntAssignment(x.queryIndex());
  }

  /** Default rather than private, so that the SmtSolver can call it during creation. */
  void setBool(int index, boolean value) {
    if (value) _trueBVars.add(index);
    else _trueBVars.remove(index);
  }

  /** Default rather than private, so that the SmtSolver can call it during creation. */
  void setInt(int index, int value) {
    _iVarValues.put(index, value);
  }

  /** Give a human-readable representation of the valuation, for use in debugging. */
  public String toString() {
    StringBuilder ret = new StringBuilder();
    ret.append("True boolean variables:\n");
    for (Integer i : _trueBVars) ret.append("  b" + i.toString() + "\n");
    ret.append("Integer variables:\n");
    for (Integer i : _iVarValues.keySet()) {
      ret.append("  i" + i.toString() + " : " + _iVarValues.get(i).toString() + "\n");
    }
    return ret.toString();
  }
}

