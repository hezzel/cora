package cora.termination;

public class Request {

  private Technique _requestedTechnique;

  public enum Technique { NONE, HORPO, DP }

  public Technique get_requestedTechnique() {
    return _requestedTechnique;
  }

  public Request(Technique technique) {
    _requestedTechnique = technique;
  }

}
