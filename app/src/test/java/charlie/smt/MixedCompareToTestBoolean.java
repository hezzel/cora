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

package charlie.smt;

import org.junit.jupiter.api.Test;
import static org.junit.jupiter.api.Assertions.*;
import java.util.ArrayList;

public class MixedCompareToTestBoolean {
  private ArrayList<Constraint> createDifferentConstraints() {
    ArrayList<Constraint> arr = new ArrayList<Constraint>();
    arr.add(new Falsehood());
    arr.add(new Truth());
    arr.add(new BVar(2));
    arr.add(new NBVar(new BVar(2)));
    arr.add(new Is0(new IVar(12)));
    arr.add(new Geq0(new IVar(12)));
    arr.add(new Neq0(new IVar(12)));
    arr.add(new Conjunction(new BVar(2), new NBVar(new BVar(3))));
    arr.add(new Disjunction(new BVar(2), new NBVar(new BVar(3))));
    arr.add(new Iff(new Is0(new IVar(12)), new BVar(5)));
    arr.add(new EqS(new SVar(2), new SValue("test")));
    arr.add(new UneqS(new SValue("test"), new SVar(2)));
    return arr;
  }

  @Test
  public void testOrderBetweenConstraintKindsIsFixed() {
    ArrayList<Constraint> arr = createDifferentConstraints();
    ArrayList<Constraint> arr2 = createDifferentConstraints();
    for (int i = 0; i < arr.size(); i++) {
      Constraint a = arr.get(i);
      assertTrue(a.compareTo(arr2.get(i)) == 0);
      for (int j = i+1; j < arr.size(); j++) {
        Constraint b = arr.get(j);
        int comp = a.compareTo(b);
        assertTrue(comp < 0);
        assertTrue(comp == - b.compareTo(a), "comparing " + a + " and " + b);
      }
    }
  }

  @Test
  public void testDifferentHashCodesForDifferentKinds() {
    ArrayList<Constraint> arr = createDifferentConstraints();
    for (int i = 0; i < arr.size(); i++) {
      Constraint a = arr.get(i);
      for (int j = i+1; j < arr.size(); j++) {
        Constraint b = arr.get(j);
        assertTrue(a.hashCode() != b.hashCode(), "hashcodes for " + a + " and " + b);
      }
    }
  }
}

