package cora.rwinduction.engine;

import cora.io.OutputModule;
import cora.rwinduction.engine.data.ProverContext;

import java.util.Objects;

public class Prover {

  private final ProverContext _ctx;

  public Prover(ProverContext proverContext) {
    Objects.requireNonNull(proverContext);

    _ctx = proverContext;
  }

  public ProverContext getProverContext() { return _ctx; }

}
