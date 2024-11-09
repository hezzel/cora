/**************************************************************************************************
 Copyright 2023--2024 Cynthia Kop

 Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 in compliance with the License.
 You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software distributed under the
 License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 express or implied.
 See the License for the specific language governing permissions and limitations under the License.
 *************************************************************************************************/

package charlie.smt;

import java.util.TreeSet;
import java.util.TreeMap;

/**
 * A valuation is an assignment of booleans to BVars, integers to IVars, and strings to SVars.
 * A Valuation is in principle mutable, so be careful how you use it! (It needs to be muted to
 * support gradual creation.)
 */
public class Valuation {
  private TreeSet<Integer> _trueBVars;
  private TreeMap<Integer,Integer> _iVarValues;
  private TreeMap<Integer,String> _sVarValues;

  /** Creates a new valuation with all booleans set to false, and no integer/string values set. */
  public Valuation() {
    _trueBVars = new TreeSet<Integer>();
    _iVarValues = new TreeMap<Integer,Integer>();
    _sVarValues = new TreeMap<Integer,String>();
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

  /** Returns the valuation for the string variable with the given index */
  public String queryStringAssignment(int index) {
    if (_sVarValues.containsKey(index)) return _sVarValues.get(index);
    else return "";
  }

  /** Returns the valuation for the given boolean variable */
  public boolean queryAssignment(BVar x) {
    return queryBoolAssignment(x.queryIndex());
  }

  /** Returns the valuation for the given integer variable */
  public int queryAssignment(IVar x) {
    return queryIntAssignment(x.queryIndex());
  }

  /** Returns the valuation for the given String variable */
  public String queryAssignment(SVar x) {
    return queryStringAssignment(x.queryIndex());
  }

  /** Set a boolean variable to the given value. */
  public void setBool(int index, boolean value) {
    if (value) _trueBVars.add(index);
    else _trueBVars.remove(index);
  }

  /** Set an integer variable to the given value. */
  public void setInt(int index, int value) {
    _iVarValues.put(index, value);
  }

  /** Set a String variable to the given value. */
  public void setString(int index, String value) {
    _sVarValues.put(index, value);
  }

  /** Give a human-readable representation of the valuation, for use in debugging. */
  public String toString() {
    StringBuilder ret = new StringBuilder();
    ret.append("True boolean variables:\n");
    for (Integer i : _trueBVars) ret.append("  b" + i.toString() + "\n");
    if (_iVarValues.size() > 0) ret.append("Integer variables:\n");
    for (Integer i : _iVarValues.keySet()) {
      ret.append("  i" + i.toString() + " : " + _iVarValues.get(i).toString() + "\n");
    }
    if (_sVarValues.size() > 0) ret.append("Stirng variables:");
    for (Integer i : _sVarValues.keySet()) {
      ret.append("  s" + i.toString() + " : " + _sVarValues.get(i).toString() + "\n");
    }
    return ret.toString();
  }
}

