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

package charlie.types;

import charlie.exceptions.NullStorageException;
import charlie.exceptions.IndexingException;

public record Arrow(Type left, Type right) implements Type {
  public Arrow(Type left, Type right) {
    if (left == null || right == null) throw new NullStorageException("Arrow", "type");
    this.left = left;
    this.right = right;
  }

  @Override
  public boolean isArrowType() { return true; }

  @Override
  public String toString() {
    return (new TypePrinter()).print(this);
  }

  /** Returns true if all sorts in the type are theory sorts. */
  @Override
  public boolean isTheoryType() { return this.left.isTheoryType() && this.right.isTheoryType(); }

  /** Returns true if some product type occurs as a subtype of this type. */
  @Override
  public boolean hasProducts() { return this.left.hasProducts() || this.right.hasProducts(); }

  @Override
  public boolean equals(Type type) {
    return switch (type) {
      case Arrow(Type l, Type r) -> this.left.equals(l) && this.right.equals(r);
      default -> false;
    };
  }

  /** For σ1 → ,,, → σm → τ, returns m. */
  @Override
  public int queryArity() { return 1 + this.right.queryArity(); }

  /** For σ1 → ,,, → σm → τ, returns τ */
  @Override
  public Type queryOutputType() { return this.right.queryOutputType(); }

  @Override
  public int queryTypeOrder() {
    return Math.max(1 + this.left.queryTypeOrder(), this.right.queryTypeOrder());
  }

  @Override
  public int numberSubtypes() {
    return 2;
  }

  @Override
  public Type subtype(int index) {
    if (index == 1) return this.left;
    if (index == 2) return this.right;
    throw new IndexingException("Arrow", "subtype", index, 1, 2);
  }
}
