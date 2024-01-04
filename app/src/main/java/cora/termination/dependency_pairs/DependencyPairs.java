package cora.termination.dependency_pairs;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.Streams;
import cora.exceptions.InappropriatePatternDataError;
import cora.terms.FunctionSymbol;
import cora.terms.Term;
import cora.terms.TermFactory;
import cora.types.*;

import org.checkerframework.checker.units.qual.N;
import org.jetbrains.annotations.Contract;
import org.jetbrains.annotations.NotNull;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.Objects;
import java.util.stream.Stream;

/** */
public class DependencyPairs {

  /**
   * This static property sets the output sort used in the DP method for marked symbols.
   */
  public static Type dpSort = TypeFactory.createSort("DP_SORT");
  List<Term> sharpSymbols = new ArrayList<>();

  /**
   * Given a type A1 => ... => An => B this method returns a list of variables X1, ..., Xn
   * such that each variable Xi is of type Ai.
   * <p>If the given type is not an arrow type then the returned list is empty.</p>
   */
  @Contract(pure = true)
  static @NotNull List<Term> generateVars(Type ty) {
    Objects.requireNonNull(ty, "Null argument given to DependencyPairs::generateVars.");

    List<Term> acc = new ArrayList<>();
    // Notice that this while_ty starts with ty, and then we mutate it to the right hand side
    // of the arrow. Eventually we will get to a sort or product, which guarantees that
    // the whole recursion will be terminated.
    Type while_ty = ty;

    while(while_ty instanceof Arrow(Type left, Type right)) {
      acc.add(TermFactory.createVar(left));
      while_ty = right;
    }
    return acc;
  }

  /**
   * Given a type A1 => ... => An => B with b a sort or product type.
   * This method returns the type A1 => ... => An => dpSort.
   * Where dpSort is a static sort used in the
   * Dependency Pairs framework.
   */
  @Contract(pure = true)
  public static Type toDependencyPairType(@NotNull Type ty) {
    return switch (ty) {
      case Base(_), Product(_) -> dpSort;
      case Arrow(Type left, Type right) ->
        TypeFactory.createArrow(left, toDependencyPairType(right));
    };
  }

  /**
   * Given a function symbol f : A1 => ... An => B or an application term
   * @param tm
   * @return
   * @throws InappropriatePatternDataError whenever the provided term is not a function symbol
   */
  @Contract(pure = true)
  static @NotNull Term generateSharpFn(@NotNull Term tm) {
    if (tm.isConstant() || tm.isApplication()) {
      return TermFactory.createConstant(
        tm.queryHead().toString().concat("#"),
        DependencyPairs.toDependencyPairType(tm.queryHead().queryType())
      );
    } else {
      throw new InappropriatePatternDataError(
        "DependencyPairs",
        "generateSharpFn",
        "an application term"
      );
    }
  }

  /**
   *
   * @param tm
   * @return
   */
  @Contract(pure = true)
  static @NotNull Term fakeEta(@NotNull Term tm) {
    Type tmTy = tm.queryType();
    List<Term> newVars = DependencyPairs.generateVars(tmTy);
    return tm.apply(newVars);
  }

  /**
   *
   * @param lhs
   * @return
   */
  static @NotNull Term genLeftSharpRule(Term lhs) {
    Term fSharp = DependencyPairs.generateSharpFn(lhs.queryRoot());
    return DependencyPairs.fakeEta(fSharp.apply(lhs.queryArguments()));
  }

  static @NotNull boolean isConstructor(Term tm) {
    return false;
  }
  static @NotNull boolean isDefined(FunctionSymbol tm) { return  false; }

  static @NotNull List<Term> genRightCandidates(Term rhs) {
    // In all cases below we will have to recursively compute the
    // U_{i = 1}^k genRightCandidates(si), so we compute it beforehand.
      List<Term> argsCandidateApp = rhs.queryArguments()
      .stream()
      .map(t -> DependencyPairs.genRightCandidates(t).stream())
      .reduce(Stream.empty(), Stream::concat)
      .toList();

    // Case for: x (s1 ... sn)
    if (rhs.isApplication() && rhs.queryHead().isVariable()){
      return argsCandidateApp;
    }
    // Case for: c (s1, ..., sn)
    else if (rhs.isApplication() && isConstructor(rhs.queryHead())) {
      return argsCandidateApp;
    }
    // Case for: (| s1, ..., sn |)
    else if (rhs.isTuple()) {
      List<Term> argsTuple = rhs.queryTupleArguments()
        .stream()
        .map(t -> DependencyPairs.genRightCandidates(t).stream())
        .reduce(Stream.empty(), Stream::concat)
        .toList();
      return argsTuple;
    }
    // Case for: g(s1, ..., sn) with g a defined symbol
    else if (rhs.isApplication() && isDefined(rhs.queryRoot())) {
     List<Term> ret = Stream.concat(
       argsCandidateApp.stream(),
       Stream.of(DependencyPairs.genLeftSharpRule(rhs))).toList();
      return ret;
    }

    // If none of the cases above is true, we return an empty list.
    return List.of();
  }

}
