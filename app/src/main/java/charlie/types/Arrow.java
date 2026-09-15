/**************************************************************************************************
 Copyright 2023--2026 Cynthia Kop

 Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 in compliance with the License.
 You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software distributed under the
 License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 express or implied.
 See the License for the specific language governing permissions and limitations under the License.
 *************************************************************************************************/

package charlie.types;

import java.util.Objects;
import java.util.Set;
import charlie.util.NullStorageException;

/**
 * The arrow constructor is the primary way to build higher types: σ → τ represents a function from
 * the domain σ to the domain τ.  In practice, we typically consider the arrow right-associative,
 * denoting σ1 → ... → σn → τ for a function that takes n arguments and returns τ.
 */
public record Arrow(Type left, Type right) implements Type {
  public Arrow {
    if (left == null || right == null) throw new NullStorageException("Arrow", "type");
  }

  @Override
  public boolean isArrowType() {
    return true;
  }

  @Override
  public boolean isSort() {
    return false;
  }

  @Override
  public boolean isSimple() {
    return this.left.isSimple() && this.right.isSimple();
  }

  @Override
  public boolean isZeroSort() {
    return false;
  }

  @Override
  public boolean isMonomorphic() {
    return this.left.isMonomorphic() && this.right.isMonomorphic();
  }

  /** For σ1 → ,,, → σm → τ, returns m. */
  @Override
  public int queryArity() {
    return 1 + this.right.queryArity();
  }

  @Override
  public int queryNumberSubtypes() {
    return 2;
  }

  @Override
  public Type querySubtype(int index) {
    if (index == 1) return this.left;
    if (index == 2) return this.right;
    throw new IndexOutOfBoundsException("Arrow::querySubtype given " + index + " (expected 1-2).");
  }

  /** For σ1 → ,,, → σm → τ, returns τ. */
  @Override
  public Type queryOutputType() {
    return this.right.queryOutputType();
  }

  @Override
  public int queryTypeOrder() {
    int l = this.left.queryTypeOrder();
    if (l == Integer.MAX_VALUE) return l;
    return Math.max(1 + l, this.right.queryTypeOrder());
  }

  @Override
  public void storeTypeVariables(Set<TVar> storage) {
    this.left.storeTypeVariables(storage);
    this.right.storeTypeVariables(storage);
  }

  @Override
  public Type substitute(ISubstitution typeSubst) {
    return new Arrow(this.left.substitute(typeSubst), this.right.substitute(typeSubst));
  }

  @Override
  public boolean match(Type other, MSubstitution typeSubstitution) {
    if (other instanceof Arrow(Type l, Type r)) {
      return this.left.match(l, typeSubstitution) && this.right.match(r, typeSubstitution);
    }
    return false;
  }

  @Override
  public int compareTo(Type other) {
    return switch(other) {
      case Base(String name) -> 1;
      case TVar(String name) -> 1;
      case Arrow(Type l, Type r) -> {
        int k = this.right.compareTo(r);
        if (k == 0) yield this.left.compareTo(l);
        else yield k;
      }
      default -> -1;
    };
  }

  @Override
  public String toString() {
    return TypePrinter.DEBUGPRINTER.print(this);
  }

  @Override
  public int hashCode() {
    return Objects.hash(left, right);
  }

  @Override
  public boolean equals(Type type) {
    if (type instanceof Arrow(Type l, Type r)) {
      return this.left.equals(l) && this.right.equals(r);
    }
    return false;
  }

  @Override
  public boolean equals(Object other) {
    return other instanceof Type t && equals(t);
  }
}
