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
import java.lang.Error;
import java.util.Set;
import java.util.ArrayList;
import cora.interfaces.types.Type;
import cora.interfaces.terms.Variable;
import cora.interfaces.terms.Term;
import cora.interfaces.terms.Substitution;
import cora.exceptions.NullStorageError;
import cora.exceptions.TypingError;
import cora.types.Sort;
import cora.terms.*;

public class SubstitutionTest {
  private Type baseType(String name) {
    return new Sort(name);
  }

  private Term constantTerm(String name, Type type) {
    return new UserDefinedSymbol(name, type);
  }

  @Test(expected = NullStorageError.class)
  public void testNullKeyCreation() {
    Substitution gamma = new Subst(null, constantTerm("37", baseType("Int")));
  }

  @Test(expected = NullStorageError.class)
  public void testNullValueCreation() {
    Substitution gamma = new Subst(new Var("x", baseType("Int")), null);
  }

  @Test(expected = TypingError.class)
  public void testIlltypedCreation() {
    Variable x = new Var("x", baseType("Int"));
    Term xterm = constantTerm("false", baseType("Bool"));
    Substitution gamma = new Subst(x, xterm);
  }

  @Test(expected = NullStorageError.class)
  public void testNullKeyExtension() {
    Substitution gamma = new Subst();
    Variable x = new Var("x", baseType("o"));
    gamma.extend(null, x);
  }

  @Test(expected = NullStorageError.class)
  public void testNullValueExtension() {
    Substitution gamma = new Subst();
    Variable x = new Var("x", baseType("o"));
    gamma.extend(x, null);
  }

  @Test(expected = TypingError.class)
  public void testIllTypedExtension() {
    Variable x = new Var("x", baseType("Int"));
    Term xterm = constantTerm("37", baseType("Int"));
    Substitution gamma = new Subst(x, xterm);
    gamma.extend(new Var("y", baseType("Int")), constantTerm("false", baseType("Bool")));
  }

  @Test(expected = NullStorageError.class)
  public void testNullKeyReplacement() {
    Variable x = new Var("x", baseType("Int"));
    Term xterm = constantTerm("37", baseType("Int"));
    Substitution gamma = new Subst(x, xterm);
    gamma.replace(null, xterm);
  }
  
  @Test(expected = NullStorageError.class)
  public void testNullValueReplacement1() {
    Variable x = new Var("x", baseType("Int"));
    Term xterm = constantTerm("37", baseType("Int"));
    Substitution gamma = new Subst(x, xterm);
    gamma.replace(x, null);
  }

  @Test(expected = TypingError.class)
  public void testIllTypedReplacement() {
    Variable x = new Var("x", baseType("Int"));
    Term xterm = constantTerm("37", baseType("Int"));
    Substitution gamma = new Subst(x, xterm);
    gamma.extend(x, constantTerm("false", baseType("Bool")));
  }
 
  @Test
  public void testEmptySubstitutionBasics() {
    Substitution gamma = new Subst();
    Variable x = new Var("x", baseType("o"));
    assertTrue(gamma.get(x) == null);
    assertTrue(gamma.getReplacement(x).equals(x));
  }

  @Test
  public void testExtendingWithNewKey() {
    Variable x = new Var("x", baseType("Int"));
    Variable y = new Var("y", baseType("o"));
    Variable z = new Var("z", baseType("o"));
    Term xterm = constantTerm("37", baseType("Int"));
    Term yterm = z;

    Substitution gamma = new Subst(x, xterm);
    assertTrue(gamma.extend(y, yterm));
    assertTrue(gamma.get(x).equals(xterm));
    assertTrue(gamma.get(y).equals(yterm));
    assertTrue(gamma.getReplacement(z).equals(z));
  }

  @Test
  public void testExtendingWithExistingKey() {
    Variable x = new Var("x", baseType("Int"));
    Term xterm = constantTerm("37", baseType("Int"));
    Term xxterm = constantTerm("42", baseType("Int"));

    Substitution gamma = new Subst(x, xterm);

    assertFalse(gamma.extend(x, xxterm));
    assertTrue(gamma.getReplacement(x).equals(xterm));
  }

  @Test
  public void testReplacingWithNewKey() {
    Variable x = new Var("x", baseType("Int"));
    Variable y = new Var("y", baseType("o"));
    Variable z = new Var("z", baseType("o"));
    Term xterm = constantTerm("37", baseType("Int"));
    Term yterm = z;

    Substitution gamma = new Subst(x, xterm);
    assertFalse(gamma.replace(y, yterm));
    assertTrue(gamma.get(x).equals(xterm));
    assertTrue(gamma.get(y).equals(yterm));
    assertTrue(gamma.getReplacement(z).equals(z));
  }

  @Test
  public void testReplacingWithExistingKey() {
    Variable x = new Var("x", baseType("Int"));
    Term xterm = constantTerm("37", baseType("Int"));
    Term xxterm = constantTerm("42", baseType("Int"));

    Substitution gamma = new Subst(x, xterm);

    assertTrue(gamma.replace(x, xxterm));
    assertTrue(gamma.get(x).equals(xxterm));
  }

  @Test
  public void testRemoving() {
    Variable x = new Var("x", baseType("Int"));
    Variable y = new Var("y", baseType("o"));
    Variable z = new Var("z", baseType("o"));

    Term xterm = constantTerm("37", baseType("Int"));
    Term yterm = z;

    Substitution gamma = new Subst();
    assertTrue(gamma.extend(x, xterm));
    assertTrue(gamma.extend(y, yterm));
    gamma.delete(y);
    gamma.delete(z);
    assertTrue(gamma.getReplacement(x).equals(xterm));
    assertTrue(gamma.getReplacement(y).equals(y));
    assertTrue(gamma.get(y) == null);
    assertTrue(gamma.getReplacement(z).equals(z));
  }

  @Test
  public void testDomain() {
    Variable x = new Var("x", baseType("Int"));
    Variable y = new Var("y", baseType("o"));
    Variable z = new Var("z", baseType("o"));

    Term xterm = constantTerm("37", baseType("Int"));
    Term yterm = z;

    Substitution gamma = new Subst();
    gamma.extend(x, xterm);
    gamma.extend(y, yterm);
    Set<Variable> domain = gamma.domain();

    assertTrue(domain.contains(x));
    assertTrue(domain.contains(y));
    assertTrue(domain.size() == 2);

    assertTrue(gamma.replace(y, y));
    domain = gamma.domain();
    assertTrue(domain.contains(x));
    assertTrue(domain.contains(y));
    assertTrue(domain.size() == 2);
    
    gamma.delete(x);
    domain = gamma.domain();
    assertTrue(domain.size() == 1);
  }
}

