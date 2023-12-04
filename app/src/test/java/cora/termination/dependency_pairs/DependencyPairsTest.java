package cora.termination.dependency_pairs;

import cora.terms.TermFactory;
import cora.terms.Variable;
import cora.types.Type;
import cora.types.TypeFactory;
import org.junit.jupiter.api.Test;
import cora.terms.Term;

import cora.termination.dependency_pairs.DependencyPairs;

import java.util.List;

import static org.junit.jupiter.api.Assertions.*;

class DependencyPairsTest {

  @Test
  void testNotArrowTypeGivesEmptyList() {
    Type ty = TypeFactory.createSort("a");
    assertTrue(DependencyPairs.generateVars(ty).isEmpty());
  }

  @Test
  void testGenerateVarsArrow() {
    // (int => int) => int => int
    Type ty = TypeFactory.createArrow(
      TypeFactory.createArrow(
        TypeFactory.intSort,
        TypeFactory.intSort
      ),
      TypeFactory.createArrow(
        TypeFactory.boolSort,
        TypeFactory.boolSort
      )
    );

    List<Term> dpVars = DependencyPairs.generateVars(ty);

    assertEquals(2,dpVars.size());

    //generateVars correctly creates variables of arrow types
    assertEquals(
      dpVars.get(0).queryType(),
      TypeFactory.createArrow(
        TypeFactory.intSort,
        TypeFactory.intSort
      )
    );
    //and of other types
    assertEquals(
      dpVars.get(1).queryType(),
      TypeFactory.boolSort
    );
  }

  @Test
  void testGenerateSharpFn() {
    Term x = TermFactory.createVar(TypeFactory.boolSort);
    Term f = TermFactory.createConstant("f", TypeFactory.createArrow(TypeFactory.boolSort,
      TypeFactory.intSort));
    Term fx = f.apply(x);

    System.out.println(fx.queryHead());

    DependencyPairs dp = new DependencyPairs();

    System.out.println(dp.generateSharpFn(f));

  }

  @Test
  void testFakeEta(){
    Type arr = TypeFactory.createArrow(
      TypeFactory.stringSort,
      TypeFactory.createArrow(
        TypeFactory.intSort,
        TypeFactory.createArrow(
          TypeFactory.createArrow(
            TypeFactory.intSort,
            TypeFactory.intSort
          ),
          TypeFactory.intSort
        )
      )
    );
    Term f = TermFactory.createConstant("f",arr);
    Term x = TermFactory.createVar(TypeFactory.boolSort);

    System.out.println(DependencyPairs.fakeEta(x));


  }

}
