package cora.parsing;

/**
 * A lexer produces Tokens from some kind of source.  When the source ends, the lexer keeps
 * producing the EOF token indefinitely.
 *
 * Lexers are designed to be used compositionally; for example, we could construct one lexer
 * which takes another lexer as argument and mostly passes on its tokens, except that it
 * filters out all occurrences of a WHITESPACE token.
 */
public interface Lexer {
  /** The EOF token is returned for the end of input. */
  public static String EOF        = "EOF";
  /** The CATCHALL token is returned when none of the user-defined tokens match, and is always a
      single character. */
  public static String CATCHALL   = "CATCHALL";

  /**
   * Returns the next token to be handled, or EOF if all tokens from the source have already been
   * returned.
   */
  public Token nextToken();
}
