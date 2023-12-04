package cora.termination.dependency_pairs;

import cora.exceptions.InappropriatePatternDataError;
import cora.terms.FunctionSymbol;
import cora.terms.Term;
import cora.terms.TermFactory;
import cora.terms.Variable;
import cora.types.*;
import cora.utils.Lam;
import cora.utils.Pair;
import cora.utils.VoidLam;
import org.jetbrains.annotations.NotNull;

import java.util.ArrayList;
import java.util.List;
import java.util.Objects;
import java.util.function.Function;

/** */
public class DependencyPairs {

  Type dpSort = TypeFactory.createSort("dp_sort");
  List<Term> sharpSymbols = new ArrayList<>();

  static @NotNull List<Term> generateVars(Type ty) {
    List<Term> acc = new ArrayList<>();
    Type while_ty = ty;

    while(while_ty instanceof Arrow(Type left, Type right)) {
      acc.add(TermFactory.createVar(left));
      while_ty = right;
    }
    return acc;
  }

  public @NotNull Term generateSharpFn(Term tm) {
    if (tm.isConstant() || tm.isApplication()) {
      String sharpSymbolName = tm.queryHead().toString().concat("#");
      return TermFactory.createConstant(sharpSymbolName, tm.queryHead().queryType());
    } else {
      throw new InappropriatePatternDataError(
        "DependencyPairs",
        "generateSharpFn",
        "an application term"
      );
    }
  }

  static @NotNull Term fakeEta(Term tm) {
    Type tmTy = tm.queryType();
    List<Term> newVars = DependencyPairs.generateVars(tmTy);
    return tm.apply(newVars);
  }


}
