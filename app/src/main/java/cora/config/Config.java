package cora.config;

import cora.termination.Prover.Technique;
import org.jetbrains.annotations.Contract;
import org.jetbrains.annotations.NotNull;

public class Config {

  private static Config _appConfig;

  private Technique _termTech = Technique.NONE;

  private Config() { }

  private Config(Technique t) {
    setTechnique(t);
  }

  public void setTechnique (Technique t) {
    _termTech = t;
  }

  public Technique getTechnique() { return _termTech; }

  @Contract(value = " -> new", pure = true)
  public static @NotNull Config getInstance() {
    if (_appConfig == null) {
      return new Config();
    } else {
      return _appConfig;
    }
  }

}
