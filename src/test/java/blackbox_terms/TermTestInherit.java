/**************************************************************************************************
 Copyright 2020 Cynthia Kop

 Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 in compliance with the License.
 You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software distributed under the
 License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 express or implied.
 See the License for the specific language governing permissions and limitations under the License.
 *************************************************************************************************/

import cora.interfaces.types.Type;
import cora.interfaces.terms.*;
import cora.types.*;
import cora.terms.*;

/** This class offers basic functionality used by all the test classes in this directory. */
public class TermTestInherit {
  protected Type baseType(String name) {
    return new Sort(name);
  }

  protected Type arrowType(String name1, String name2) {
    return new ArrowType(baseType(name1), baseType(name2));
  }

  protected Variable freeVariable(String name, Type type) {
    return new Var(name, type);
  }

  protected Variable binderVariable(String name, Type type) {
    return new BinderVariable(name, type);
  }

  protected Term constantTerm(String name, Type type) {
    return new Constant(name, type);
  }

  protected Term unaryTerm(String name, Type output, Term arg) {
    Type arrtype = new ArrowType(arg.queryType(), output);
    FunctionSymbol f = new Constant(name, arrtype);
    return new FunctionalTerm(f, arg);
  }

  protected Term binaryTerm(String name, Type output, Term arg1, Term arg2) {
    Type arrtype = new ArrowType(arg1.queryType(), new ArrowType(arg2.queryType(), output));
    FunctionSymbol f = new Constant(name, arrtype);
    return new FunctionalTerm(f, arg1, arg2);
  }
}

