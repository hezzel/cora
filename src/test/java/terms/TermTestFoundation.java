/**************************************************************************************************
 Copyright 2022 Cynthia Kop

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

import cora.types.Type;
import cora.types.TypeFactory;

public class TermTestFoundation {
  protected Type baseType(String name) {
    return TypeFactory.createSort(name);
  }

  protected Type arrowType(Type left, Type right) {
    return TypeFactory.createArrow(left, right);
  }

  protected Type arrowType(String name1, String name2) {
    return TypeFactory.createArrow(baseType(name1), baseType(name2));
  }

  protected Term constantTerm(String name, Type type) {
    return new Constant(name, type);
  }

  protected Term unaryTerm(String name, Type output, Term arg) {
    Type arrtype = TypeFactory.createArrow(arg.queryType(), output);
    FunctionSymbol f = new Constant(name, arrtype);
    return new FunctionalTerm(f, arg);
  }

  protected Term twoArgVarTerm() {
    Type type = TypeFactory.createArrow(baseType("a"), arrowType("b", "a"));
    Variable x = TermFactory.createVar("x", type);
    Term arg1 = constantTerm("c", baseType("a"));
    Term arg2 = unaryTerm("g", baseType("b"), TermFactory.createVar("y", baseType("b")));
    return new VarTerm(x, arg1, arg2);
  }

  protected Term twoArgFuncTerm() {
    Type type = TypeFactory.createArrow(baseType("a"), arrowType("b", "a"));
    FunctionSymbol f = new Constant("f", type);
    Term arg1 = constantTerm("c", baseType("a"));
    Term arg2 = unaryTerm("g", baseType("b"), constantTerm("d", baseType("b")));
    return new FunctionalTerm(f, arg1, arg2);
  }
}

