package cora.exceptions;

public class ProdTypeConstructionError extends Error {
  public ProdTypeConstructionError(){
    super("Trying to construct a product type with less than two types.");
  }
}
