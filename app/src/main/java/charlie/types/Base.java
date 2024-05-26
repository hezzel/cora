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

import charlie.exceptions.IndexingException;
import charlie.exceptions.NullStorageException;

public record Base(String name) implements Type {
  public Base {
    if (name == null) {
      throw new NullStorageException("Base", "name");
    }
  }

  @Override
  public boolean isBaseType() {
    return true;
  }

  /** Returns true if the type is one of the internally-registered theory sorts. */
  @Override
  public boolean isTheoryType() {
    return UniqueTypes.isTheoryType(this);
  }

  @Override
  public boolean hasProducts() {
    return false;
  }

  @Override
  public String toString() {
    return this.name;
  }

  @Override
  public int numberSubtypes() {
    return 0;
  }

  @Override
  public Type subtype(int index) {
    throw new IndexingException("Base", "subtype", index);
  }

  @Override
  public boolean equals(Type type) {
    return switch (type) {
      case Base(String x) -> this.name.equals(x);
      default -> false;
    };
  }

  @Override
  public Type queryOutputType() {
    return this;
  }

  @Override
  public int queryTypeOrder() {
    return 0;
  }
}
