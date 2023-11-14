/**************************************************************************************************
 Copyright 2019, 2022, 2023 Cynthia Kop

 Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 in compliance with the License.
 You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software distributed under the
 License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 express or implied.
 See the License for the specific language governing permissions and limitations under the License.
 *************************************************************************************************/

package cora.terms;

import org.junit.Test;
import static org.junit.Assert.*;
import java.lang.Error;
import java.util.Set;
import java.util.ArrayList;
import cora.exceptions.ArityError;
import cora.exceptions.NullStorageError;
import cora.exceptions.TypingError;
import cora.types.Type;
import cora.types.TypeFactory;

public class SubstitutionTest {
  private Type baseType(String name) {
    return TypeFactory.createSort(name);
  }
  
  private Type arrowType(String left, String right) {
    return TypeFactory.createArrow(baseType(left), baseType(right));
  }

  private Term constantTerm(String name, Type type) {
    return new Constant(name, type);
  }

  @Test(expected = NullStorageError.class)
  public void testNullKeyCreation() {
    Substitution gamma = new Subst(null, constantTerm("37", baseType("Int")));
  }

  @Test(expected = NullStorageError.class)
  public void testNullValueCreation() {
    Substitution gamma = new Subst(TermFactory.createVar("x", baseType("Int")), null);
  }

  @Test(expected = TypingError.class)
  public void testIlltypedCreation() {
    Variable x = TermFactory.createVar("x", baseType("Int"));
    Term xterm = constantTerm("false", baseType("Bool"));
    Substitution gamma = new Subst(x, xterm);
  }

  @Test(expected = ArityError.class)
  public void testIncorrectArityInCreation() {
    MetaVariable x = TermFactory.createMetaVar("x", arrowType("o", "o"), 1);
    Term xterm = constantTerm("a", arrowType("o", "o"));
    Substitution gamma = new Subst(x, xterm);
  }
 
   @Test(expected = NullStorageError.class)
  public void testNullKeyExtension() {
    Substitution gamma = new Subst();
    Variable x = TermFactory.createVar("x", baseType("o"));
    gamma.extend(null, x);
  }

  @Test(expected = NullStorageError.class)
  public void testNullValueExtension() {
    Substitution gamma = new Subst();
    Variable x = TermFactory.createVar("x", baseType("o"));
    gamma.extend(x, null);
  }

  @Test(expected = ArityError.class)
  public void testIncorrectArityExtension() {
    MetaVariable z = TermFactory.createMetaVar("z", arrowType("o", "o"), 0);
    Term zterm = constantTerm("a", arrowType("o", "o"));
    Substitution gamma = new Subst(z, zterm);
    MetaVariable y = TermFactory.createMetaVar("y", arrowType("o", "o"), 1);
    gamma.extend(y, zterm);
  }

  @Test(expected = TypingError.class)
  public void testIllTypedExtension() {
    Variable x = TermFactory.createVar("x", baseType("Int"));
    Term xterm = constantTerm("37", baseType("Int"));
    Substitution gamma = new Subst(x, xterm);
    gamma.extend(TermFactory.createVar("y", baseType("Int")), constantTerm("false", baseType("Bool")));
  }

  @Test(expected = NullStorageError.class)
  public void testNullKeyReplacement() {
    Variable x = TermFactory.createVar("x", baseType("Int"));
    Term xterm = constantTerm("37", baseType("Int"));
    Substitution gamma = new Subst(x, xterm);
    gamma.replace(null, xterm);
  }
  
  @Test(expected = NullStorageError.class)
  public void testNullValueReplacement1() {
    Variable x = TermFactory.createVar("x", baseType("Int"));
    Term xterm = constantTerm("37", baseType("Int"));
    Substitution gamma = new Subst(x, xterm);
    gamma.replace(x, null);
  }

  @Test(expected = TypingError.class)
  public void testIllTypedReplacement() {
    Variable x = TermFactory.createVar("x", baseType("Int"));
    Term xterm = constantTerm("37", baseType("Int"));
    Substitution gamma = new Subst(x, xterm);
    gamma.replace(x, constantTerm("false", baseType("Bool")));
  }

  @Test(expected = ArityError.class)
  public void testIncorrectArityReplacement() {
    MetaVariable z = TermFactory.createMetaVar("z", arrowType("o", "o"), 1);
    Variable x = TermFactory.createBinder("x", baseType("o"));
    Term zterm = TermFactory.createAbstraction(x, x);
    Substitution gamma = new Subst(z, zterm);
    gamma.replace(z, constantTerm("37", zterm.queryType()));
  }

 @Test
  public void testEmptySubstitutionBasics() {
    Substitution gamma = new Subst();
    Variable x = TermFactory.createVar("x", baseType("o"));
    assertTrue(gamma.get(x) == null);
    assertTrue(gamma.getReplacement(x).equals(x));
  }

  @Test
  public void testExtendingWithNewKey() {
    Variable x = TermFactory.createVar("x", baseType("Int"));
    Variable y = TermFactory.createVar("y", baseType("o"));
    Variable z = TermFactory.createVar("z", baseType("o"));
    Term xterm = constantTerm("37", baseType("Int"));
    Term yterm = z;

    Substitution gamma = new Subst(x, xterm);
    assertTrue(gamma.extend(y, yterm));
    assertTrue(gamma.get(x).equals(xterm));
    assertTrue(gamma.get(y).equals(yterm));
    assertTrue(gamma.getReplacement(z).equals(z));
  }

  @Test
  public void testExtendingWithMetavariable() {
    MetaVariable z = TermFactory.createMetaVar("z", arrowType("o", "o"), 1);
    Variable x = TermFactory.createBinder("x", baseType("o"));
    Term zterm = TermFactory.createAbstraction(x, x);
    Substitution gamma = new Subst(z, zterm);
    MetaVariable y = TermFactory.createMetaVar("y", arrowType("o", "o"), 1);
    assertTrue(gamma.get(z).equals(zterm));
    assertTrue(gamma.get(y) == null);
    assertTrue(gamma.extend(y, zterm));
  }

  @Test
  public void testExtendingWithExistingKey() {
    Variable x = TermFactory.createVar("x", baseType("Int"));
    Term xterm = constantTerm("37", baseType("Int"));
    Term xxterm = constantTerm("42", baseType("Int"));

    Substitution gamma = new Subst(x, xterm);

    assertFalse(gamma.extend(x, xxterm));
    assertTrue(gamma.getReplacement(x).equals(xterm));
  }

  @Test
  public void testReplacingWithNewKey() {
    Variable x = TermFactory.createVar("x", baseType("Int"));
    Variable y = TermFactory.createVar("y", baseType("o"));
    Variable z = TermFactory.createVar("z", baseType("o"));
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
    Variable x = TermFactory.createVar("x", baseType("Int"));
    Term xterm = constantTerm("37", baseType("Int"));
    Term xxterm = constantTerm("42", baseType("Int"));

    Substitution gamma = new Subst(x, xterm);

    assertTrue(gamma.replace(x, xxterm));
    assertTrue(gamma.get(x).equals(xxterm));
  }

  @Test
  public void testRemoving() {
    Variable x = TermFactory.createVar("x", baseType("Int"));
    Variable y = TermFactory.createVar("y", baseType("o"));
    Variable z = TermFactory.createVar("z", baseType("o"));

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
    Variable x = TermFactory.createVar("x", baseType("Int"));
    Variable y = TermFactory.createVar("y", baseType("o"));
    Variable z = TermFactory.createVar("z", baseType("o"));

    Term xterm = constantTerm("37", baseType("Int"));
    Term yterm = z;

    Substitution gamma = new Subst();
    gamma.extend(x, xterm);
    gamma.extend(y, yterm);
    Set<Replaceable> domain = gamma.domain();

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

