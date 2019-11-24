/**************************************************************************************************
 Copyright 2019 Cynthia Kop

 Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 in compliance with the License.
 You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software distributed under the
 License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 express or implied.
 See the License for the specific language governing permissions and limitations under the License.
 *************************************************************************************************/

import org.junit.Test;
import static org.junit.Assert.*;
import java.util.ArrayList;
import cora.exceptions.IllegalTermError;
import cora.interfaces.types.Type;
import cora.interfaces.terms.Variable;
import cora.interfaces.terms.Environment;
import cora.types.*;
import cora.terms.Var;
import cora.terms.Env;
import cora.terms.EnvironmentPair;

public class EnvironmentPairTest {
  @Test
  public void testSingleCreation() {
    Variable x = new Var("x", new Sort("xsort"));
    EnvironmentPair pair = new EnvironmentPair(x);
    assertEquals(pair.freeVars().size(), 1);
    assertEquals(pair.freeVars().size(), 1);
    assertTrue(pair.freeVars().contains(x));
    assertFalse(pair.boundVars().contains(x));
  }

  @Test
  public void testAddContains() {
    EnvironmentPair pair = EnvironmentPair.emptyPair();
    Variable x = new Var("x", new Sort("a"));
    Variable y = new Var("y", new Sort("b"));
    Variable z = new Var("z", new Sort("c"));
    pair = pair.addFreeVar(x);
    pair = pair.addBoundVar(y);
    pair = pair.addFreeVar(z);

    assertTrue(pair.freeVars().contains(x));
    assertTrue(pair.freeVars().contains(z));
    assertTrue(pair.boundVars().contains(y));
    assertFalse(pair.boundVars().contains(x));
    assertFalse(pair.freeVars().contains(y));
  }

  @Test
  public void testAddingTwice() {
    Variable x = new Var("x", new Sort("a"));
    Variable y = new Var("x", new Sort("a"));
    EnvironmentPair pair = EnvironmentPair.emptyPair();
    pair = pair.addFreeVar(x);
    pair = pair.addBoundVar(y);
    pair = pair.addFreeVar(x);

    assertTrue(pair.freeVars().contains(x));
    assertTrue(pair.boundVars().contains(y));
    assertTrue(pair.freeVars().size() == 1);
    assertTrue(pair.boundVars().size() == 1);
  }

  @Test(expected = IllegalTermError.class)
  public void testAddingVariableToBothFreeAndBoundEnvironments() {
    EnvironmentPair pair = EnvironmentPair.emptyPair();
    Variable x = new Var("x", new Sort("a"));
    pair = pair.addFreeVar(x);
    pair = pair.addBoundVar(x);
  }

  @Test
  public void testMoveVariableFromFreeToBound() {
    Variable x = new Var("x", new Sort("a"));
    Variable y = new Var("y", new Sort("a"));
    Variable z = new Var("z", new Sort("a"));
    ArrayList<Variable> lst = new ArrayList<Variable>();
    lst.add(x);
    lst.add(y);
    lst.add(x);
    Env fenv = new Env(lst);

    Variable u = new Var("u", new Sort("b"));
    Variable v = new Var("v", new Sort("b"));
    lst = new ArrayList<Variable>();
    lst.add(u);
    lst.add(v);
    Env benv = new Env(lst);

    EnvironmentPair pair = new EnvironmentPair(fenv, benv);

    pair = pair.markFreeVarAsBound(z);
    assertTrue(pair.boundVars().contains(z));
    assertFalse(pair.freeVars().contains(z));
    assertTrue(pair.freeVars().size() == 2);
    assertTrue(pair.boundVars().size() == 3);
  }

  @Test
  public void testMoveVariableIntoBoundThatWasNotThere() {
    EnvironmentPair pair = EnvironmentPair.emptyPair();
    Variable x = new Var("x", new Sort("a"));
    pair = pair.markFreeVarAsBound(x);
    assertTrue(pair.freeVars().size() == 0);
    assertTrue(pair.boundVars().contains(x));
  }

  @Test(expected = IllegalTermError.class)
  public void testMoveBoundVariableToBound() {
    Variable x = new Var("x", new Sort("a"));
    Variable y = new Var("y", new Sort("b"));
    EnvironmentPair pair = new EnvironmentPair(y);
    pair = pair.addBoundVar(x);
    pair.markFreeVarAsBound(x);
  }

  @Test
  public void testStraightforwardMerge() {
    ArrayList<Variable> lst;
    Variable x = new Var("x", new Sort("a"));
    Variable y = new Var("y", new Sort("a"));
    Variable z = new Var("z", new Sort("a"));
    Variable u = new Var("u", new Sort("b"));
    Variable v = new Var("v", new Sort("b"));
    Variable w = new Var("w", new Sort("c"));

    EnvironmentPair pair1 = EnvironmentPair.emptyPair();    // ({}, {})
    EnvironmentPair pair2 = new EnvironmentPair(y);    // ({y}, {})
    
    lst = new ArrayList<Variable>();
    lst.add(y);
    lst.add(z);
    Env fenv1 = new Env(lst);
    Env benv1 = new Env(u);
    EnvironmentPair pair3 = new EnvironmentPair(fenv1, benv1);    // ({y,z}, {u})

    lst = new ArrayList<Variable>();
    lst.add(v);
    lst.add(w);
    Env fenv2 = new Env(x);
    Env benv2 = new Env(lst);
    EnvironmentPair pair4 = new EnvironmentPair(fenv2, benv2);    // ({x}, {v,w})

    ArrayList<EnvironmentPair> pairs = new ArrayList<EnvironmentPair>();
    pairs.add(pair1);
    pairs.add(pair2);
    pairs.add(pair3);
    pairs.add(pair4);

    EnvironmentPair combination = EnvironmentPair.mergeAll(pairs);

    assertTrue(combination.freeVars().size() == 3);
    assertTrue(combination.boundVars().size() == 3);
    assertTrue(combination.freeVars().contains(x));
    assertTrue(combination.freeVars().contains(y));
    assertTrue(combination.freeVars().contains(z));
    assertTrue(combination.boundVars().contains(u));
    assertTrue(combination.boundVars().contains(v));
    assertTrue(combination.boundVars().contains(w));
  }

  @Test(expected = IllegalTermError.class)
  public void testMergeInconsistentEnvironments() {
    Variable x = new Var("x", new Sort("a"));
    Variable y = new Var("y", new Sort("a"));
    Variable z = new Var("z", new Sort("a"));
    Env fenv1 = new Env(x);
    Env benv1 = new Env(y);
    Env fenv2 = new Env(y);
    Env benv2 = new Env(z);

    EnvironmentPair pair1 = new EnvironmentPair(fenv1, benv1);
    EnvironmentPair pair2 = new EnvironmentPair(fenv2, benv2);

    ArrayList<EnvironmentPair> pairs = new ArrayList<EnvironmentPair>();
    pairs.add(pair1);
    pairs.add(pair2);
    EnvironmentPair combination = EnvironmentPair.mergeAll(pairs);
  }

  @Test
  public void testMergeSelectSpecificArgument() {
    Variable x = new Var("x", new Sort("a"));
    Variable y = new Var("y", new Sort("a"));
    Variable z = new Var("z", new Sort("a"));

    Env fenv1 = new Env(x);
    Env benv1 = new Env(y);
    EnvironmentPair pair1 = new EnvironmentPair(fenv1, benv1);

    Environment fenv2 = fenv1.extend(z);
    EnvironmentPair pair2 = new EnvironmentPair(fenv2, benv1);

    ArrayList<EnvironmentPair> pairs = new ArrayList<EnvironmentPair>();
    pairs.add(pair1);
    pairs.add(pair2);
    EnvironmentPair combination = EnvironmentPair.mergeAll(pairs);

    assertTrue(combination == pair2);
  }

  @Test
  public void testMergeSelectSpecificFreeAndBound() {
    Variable x = new Var("x", new Sort("a"));
    Variable y = new Var("y", new Sort("a"));
    Variable z = new Var("z", new Sort("a"));
    Variable u = new Var("u", new Sort("b"));
    Environment fenv1 = new Env(x);
    Environment benv1 = new Env(y);
    Environment fenv2 = fenv1.extend(z);
    Environment benv2 = benv1.extend(u);

    EnvironmentPair pair1 = new EnvironmentPair(fenv1, benv2);  // ( {x}, {y,u} )
    EnvironmentPair pair2 = new EnvironmentPair(fenv2, benv1);  // ( {x,z}, {y} )

    ArrayList<EnvironmentPair> pairs = new ArrayList<EnvironmentPair>();
    pairs.add(pair1);
    pairs.add(pair2);
    EnvironmentPair combination = EnvironmentPair.mergeAll(pairs);

    assertTrue(combination.freeVars() == fenv2);
    assertTrue(combination.boundVars() == benv2);
  }
}
