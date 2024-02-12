package cora.termination;

import cora.rewriting.TRS;

public class Request {

  private final Technique _requestedTechnique;
  private final TRS _trs;

  public enum Technique { NONE, HORPO, DP }

  public Technique getRequestedTechnique() {
    return _requestedTechnique;
  }

  public TRS getTRS() {
    return _trs;
  }

  public Request(TRS trs, Technique technique) {
    _trs = trs;
    _requestedTechnique = technique;
  }

  @Override
  public String toString() {
    return STR."RequestObject: [\ntrs:{\n\{ _trs }} \n termination_technique: { \{ this._requestedTechnique } }\n]";
  }
}
