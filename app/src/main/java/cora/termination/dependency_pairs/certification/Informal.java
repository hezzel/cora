package cora.termination.dependency_pairs.certification;

import org.jetbrains.annotations.NotNull;

import java.security.cert.Certificate;

public class Informal {
  private static final StringBuilder _proof = new StringBuilder();

  private static Informal _certificate;

  private Informal() {
    initialProofString();
  }

  private void initialProofString() {
    _proof.append("d").append("\n");
  }

  public static @NotNull Informal getInstance() {
    if (_certificate == null) {
      _certificate = new Informal();
    }
    return _certificate;
  }

  public void addProofStep(String proofStep) {
    _proof.append(proofStep).append("\n");
  }

  public String getInformalProof() {
    return _proof.toString();
  }
}
