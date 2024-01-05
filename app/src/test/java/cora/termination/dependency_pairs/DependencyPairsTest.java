package cora.termination.dependency_pairs;

import cora.parsing.CoraInputReader;
import cora.terms.TermFactory;
import cora.terms.Variable;
import cora.types.Type;
import cora.types.TypeFactory;
import org.junit.jupiter.api.Test;
import cora.terms.Term;

import cora.termination.dependency_pairs.DependencyPairs;

import java.beans.DefaultPersistenceDelegate;
import java.util.List;

import static org.junit.jupiter.api.Assertions.*;
import static org.junit.jupiter.api.Assumptions.assumingThat;

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
  void testToDependencyPairType() {
    Type ty =
      CoraInputReader.readTypeFromString("Bool");
    Type depTy = DependencyPairs.toDependencyPairType(ty);

    assumingThat(ty.isBaseType() || ty.isProductType(),  () -> {
      assertTrue(DependencyPairs.dpSort.equals(depTy));
    });

    assumingThat(ty.isArrowType(), () -> {
//      System.out.println("do more tests here");
    });

  }

  @Test
  void testGenerateSharpFn() {
    Term x = TermFactory.createVar(TypeFactory.boolSort);
    Term f = TermFactory.
      createConstant("f",
        CoraInputReader.readTypeFromString("Bool -> Int")
      );
    Term fx = f.apply(x);

//    System.out.println(
//      fx.queryHead() + ":" + f.queryType()
//    );

    DependencyPairs dp = new DependencyPairs();

    Term fSharp = dp.generateSharpFn(f);

//    System.out.println(fSharp + ":" + fSharp.queryType());

  }

  @Test
  void testFakeEta(){
    Type arr =
      CoraInputReader.readTypeFromString(
        "Bool -> b -> c -> d -> e"
      );
    Term f = TermFactory.createConstant("f",arr);
    Term x = TermFactory.createVar(TypeFactory.boolSort);

//    System.out.println(f + ":" + f.queryType());

//    System.out.println("fake eta result");

//    System.out.println(DependencyPairs.fakeEta(f.apply(x)));
  }

  @Test
  void testGenLeftSharpRule() {
    Type arr =
      CoraInputReader.readTypeFromString(
        "Bool -> b -> c -> d -> e"
      );
    Term f = TermFactory.createConstant("f",arr);
//    System.out.println("Normal lhs: " + f + ":" + f.queryType());
//    System.out.println("DP lhs: " + DependencyPairs.genLeftSharpRule(f));
//    System.out.println("With f : " + DependencyPairs.genLeftSharpRule(f).queryRoot().queryType());
  }

  @Test
  void testGenRightCandidates() {
    Term f = TermFactory.createConstant("f",
      CoraInputReader.readTypeFromString("a -> b"));
    Term etaF = DependencyPairs.fakeEta(f);
//    System.out.println(etaF);
//    System.out.println(DependencyPairs.genRightCandidates(etaF));

  }

}
