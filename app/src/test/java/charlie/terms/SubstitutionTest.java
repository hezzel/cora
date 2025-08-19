/**************************************************************************************************
 Copyright 2019--2025 Cynthia Kop

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

import org.junit.jupiter.api.Test;
import static org.junit.jupiter.api.Assertions.*;
import java.util.Set;
import charlie.util.NullStorageException;
import charlie.types.Type;
import charlie.types.TypeFactory;
import charlie.terms.replaceable.Replaceable;

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

  @Test
  public void testNullKeyCreation() {
    assertThrows(NullStorageException.class, () ->
      new Subst(null, constantTerm("37", baseType("Int"))));
  }

  @Test
  public void testNullValueCreation() {
    assertThrows(NullStorageException.class, () ->
      new Subst(TermFactory.createVar("x", baseType("Int")), null));
  }

  @Test
  public void testIlltypedCreation() {
    Variable x = TermFactory.createVar("x", baseType("Int"));
    Term xterm = constantTerm("false", baseType("Bool"));
    assertThrows(TypingException.class, () -> new Subst(x, xterm));
  }

  @Test
  public void testIncorrectArityInCreation() {
    MetaVariable x = TermFactory.createMetaVar("x", arrowType("o", "o"), 1);
    Term xterm = constantTerm("a", arrowType("o", "o"));
    assertThrows(TypingException.class, () -> new Subst(x, xterm));
  }
 
  @Test
  public void testNullKeyExtension() {
    Substitution gamma = new Subst();
    Variable x = TermFactory.createVar("x", baseType("o"));
    assertThrows(NullStorageException.class, () -> gamma.extend(null, x));
  }

  @Test
  public void testNullValueExtension() {
    Substitution gamma = new Subst();
    Variable x = TermFactory.createVar("x", baseType("o"));
    assertThrows(NullStorageException.class, () -> gamma.extend(x, null));
  }

  @Test
  public void testIncorrectArityExtension() {
    MetaVariable z = TermFactory.createMetaVar("z", arrowType("o", "o"), 0);
    Term zterm = constantTerm("a", arrowType("o", "o"));
    Substitution gamma = new Subst(z, zterm);
    MetaVariable y = TermFactory.createMetaVar("y", arrowType("o", "o"), 1);
    assertThrows(TypingException.class, () -> gamma.extend(y, zterm));
  }

  @Test
  public void testIllTypedExtension() {
    Variable x = TermFactory.createVar("x", baseType("Int"));
    Term xterm = constantTerm("37", baseType("Int"));
    Substitution gamma = new Subst(x, xterm);
    assertThrows(TypingException.class, () -> gamma.extend(
      TermFactory.createVar("y", baseType("Int")), constantTerm("false", baseType("Bool"))));
  }

  @Test
  public void testNullKeyReplacement() {
    Variable x = TermFactory.createVar("x", baseType("Int"));
    Term xterm = constantTerm("37", baseType("Int"));
    Substitution gamma = new Subst(x, xterm);
    assertThrows(NullStorageException.class, () -> gamma.replace(null, xterm));
  }
  
  @Test
  public void testNullValueReplacement1() {
    Variable x = TermFactory.createVar("x", baseType("Int"));
    Term xterm = constantTerm("37", baseType("Int"));
    Substitution gamma = new Subst(x, xterm);
    assertThrows(NullStorageException.class, () -> gamma.replace(x, null));
  }

  @Test
  public void testIllTypedReplacement() {
    Variable x = TermFactory.createVar("x", baseType("Int"));
    Term xterm = constantTerm("37", baseType("Int"));
    Substitution gamma = new Subst(x, xterm);
    assertThrows(TypingException.class, () ->
      gamma.replace(x, constantTerm("false", baseType("Bool"))));
  }

  @Test
  public void testIncorrectArityReplacement() {
    MetaVariable z = TermFactory.createMetaVar("z", arrowType("o", "o"), 1);
    Variable x = TermFactory.createBinder("x", baseType("o"));
    Term zterm = TermFactory.createAbstraction(x, x);
    Substitution gamma = new Subst(z, zterm);
    assertThrows(TypingException.class, () ->
      gamma.replace(z, constantTerm("37", zterm.queryType())));
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
  public void testCopy() {
    Variable x = TermFactory.createVar("x", baseType("Int"));
    Term xterm = constantTerm("37", baseType("Int"));
    Substitution gamma = new Subst(x, xterm);
    Substitution delta = gamma.copy();
    Variable y = TermFactory.createVar("y", baseType("o"));
    Term yterm = TermFactory.createVar("z", baseType("o"));
    delta.extend(y, yterm);
    assertTrue(gamma.get(x) == xterm);
    assertTrue(gamma.get(y) == null);
    assertTrue(delta.get(x) == xterm);
    assertTrue(delta.get(y) == yterm);
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

