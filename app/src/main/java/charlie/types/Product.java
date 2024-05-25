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

import com.google.common.collect.ImmutableList;

import charlie.exceptions.IndexingError;
import charlie.exceptions.NullInitialisationError;

public record Product(ImmutableList<Type> types) implements Type {
  public Product {
    if (types == null) throw new NullInitialisationError("Product", "product list");
    if (types.size() < 2) throw new IllegalArgumentException("product list has size " +
      types.size() + "; should be at least 2");
  }

  @Override
  public boolean isProductType() { return true; }

  /** 
   * Returns true if the only base types sorts occurring in this type are theory sorts --
   * that is, the sorts specifically created as theory sorts by the TypeFactory.
   */
  @Override
  public boolean isTheoryType() {
    return types.stream().allMatch(Type::isTheoryType);
  }

  /** @return true */
  @Override
  public boolean hasProducts() {
    return true;
  }

  @Override
  public String toString(){
    return (new TypePrinter()).print(this);
  }

  @Override
  public boolean equals(Type type) {
    switch (type) {
      case Product(ImmutableList<Type> componentTypes):
        if (this.types.size() != componentTypes.size()) return false;
        for (int i = 0; i < this.types.size(); i++) {
          if (!this.types.get(i).equals(componentTypes.get(i))) return false;
        }
        return true;
      default: return false;
    }
  }

  /** For σ1 → ,,, → σm → τ, returns τ; so this returns itself. */
  @Override
  public Type queryOutputType() {
    return this;
  }

  /** Returns the type order of the current type. */
  @Override
  public int queryTypeOrder() {
    return types
      .stream()
      .map(Type::queryTypeOrder)
      .reduce(0, (n,m) -> Math.max(n,m));
  }

  @Override
  public int numberSubtypes() {
    return this.types.size();
  }

  @Override
  public Type subtype(int index) {
    if (index <= 0 || index > this.types.size()) {
      throw new IndexingError("Product", "subtype", index, 1, this.types.size());
    }
    return this.types.get(index-1);
  }
}
