/**************************************************************************************************
 Copyright 2023 Cynthia Kop

 Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 in compliance with the License.
 You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software distributed under the
 License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 express or implied.
 See the License for the specific language governing permissions and limitations under the License.
 *************************************************************************************************/

package cora.parser.lib;

import cora.exceptions.ParseError;

/**
 * A ParsingStatus object is used to keep track of progress and errors during parsing.  This is
 * intended to take over a large part of the administration when creating a parser.
 */
public class ParsingStatus {
  private TokenQueue _tqueue;
  private ErrorCollector _errors;
  private Token _lastErrorToken;

  /**
   * Set up a basic parser status to begin parsing with the given tokens.  If maxErrors is greater
   * than 1, this indicates that the parser should try to recover after an error, until maxErrors
   * have been reached.  While parsing should still fail (the parser should call
   * throwCollectedErrors() before returning), this may give more helpful error messages -- if the
   * parser is set up to support error recovery.
   */
  public ParsingStatus(TokenQueue queue, int maxErrors) {
    _tqueue = queue;
    _errors = new ErrorCollector(maxErrors);
    _lastErrorToken = null;
  }

  /**
   * Set up a basic parser status to begin parsing with the given tokens.  The given error collector
   * is used to store errors we encounter along the way.
   */
  public ParsingStatus(TokenQueue queue, ErrorCollector collector) {
    _tqueue = queue;
    _errors = collector;
    _lastErrorToken = null;
  }

  /**
   * If at least one error has been encountered, this throws a ParseError indicating all the
   * error messages that have been collected.
   * If not, nothing is done.
   */
  public void throwCollectedErrors() {
    if (_errors.queryErrorCount() > 0) throw new ParseError(_errors.queryCollectedMessages());
  }

  /** Once we have encountered too many errors, we immediately abort by throwing the ParseError. */
  private void checkTooManyErrors() {
    if (_errors.queryFull()) throwCollectedErrors();
  }

  /**
   * This stores the given error message, marked to the position of the given token.  If you do not
   * want the message to include a position, provide a null argument for token instead.
   *
   * If the token is given, and is the same as the token for the last error that was added, then
   * the error is not in fact added.  This is to avoid multiple errors for the same location, which
   * is usually a duplicate.
   *
   * If too many errors have already been stored, this will immediately throw a ParseError
   * indicating the collected problems.  If no error is thrown, then the parser should proceed with
   * error recovery and try to continue parsing.
   */
  public void storeError(String message, Token token) {
    if (token == null) _errors.addError(message);
    else if (token == _lastErrorToken) return;
    else _errors.addError(token.getPosition() + ": " + message);
    _lastErrorToken = token;
    checkTooManyErrors();
  }

  /**
   * This stores the given error message at a given position, as returned at some point by
   * queryErrorPosition().  That is, it stores a message to be printed *before* all the errors that
   * were added after the corresponding call to queryErrorPosition().
   * Note that this bypasses the "do not store duplicate errors on the same token" code, so this
   * message will be printd whether or not the previous error stored was for the same token.
   */
  public void storeError(String message, Token token, int pos) {
    if (token != null) message = token.getPosition() + ": " + message;
    _errors.addErrorBefore(pos, message);
    checkTooManyErrors();
  }

  /**
   * This returns a position in the error collector, to be used by a potential call to storeError
   * later (so that a message can be printed before any errors stored after the current call).
   */
  public int queryErrorPosition() {
    return _errors.queryErrorCount();
  }

  /**
   * This stores the given error message, marked to the position of the given token, and then
   * throws a ParseError with all the collected error messages (including this one).
   * If you do not want the message to include a position, provide a null argument for token/
   */
  public void abort(String message, Token token) {
    if (token == null) _errors.addError(message);
    else _errors.addError(token.getPosition() + ": " + message);
    throw new ParseError(_errors.queryCollectedMessages());
  }

  /**
   * Reads the next token from the input.  If tokenising causes an exception, this quietly stores
   * the exception, and only throws a ParseError once too many problems have been encountered.
   */
  public Token nextToken() {
    while (true) {
      try { return _tqueue.nextToken(); }
      catch (LexerException e) {
        _errors.addError(e.getMessage());
        checkTooManyErrors();
      }
    }
  }

  /**
   * Returns the next token from the input without actually reading it, so nextToken() will still
   * return it.
   */
  public Token peekNext() {
    Token token = nextToken();
    _tqueue.push(token);
    return token;
  }

  /**
   * This peeks at the next token, to verify that it is a certain kind (token.getName()).  The
   * token is not yet read, so doing this will not affect the result of nextToken().
   */
  public boolean nextTokenIs(String kind) {
    return peekNext().getName().equals(kind);
  }

  /**
   * This peeks at the upcoming tokens, to verify that they are a certain kind (token.getName()).
   * The tokens are not yet read, so doing this will not affect the result of nextToken().
   */
  public boolean nextTokensAre(String[] kinds) {
    Token toks[] = new Token[kinds.length];
    boolean ok = true;
    int i = 0;
    for (; i < kinds.length && ok; i++) {
      toks[i] = nextToken();
      if (!toks[i].getName().equals(kinds[i])) ok = false;
    }
    for (; i > 0; i--) _tqueue.push(toks[i-1]);
    return ok;
  }

  /**
   * This peeks at the next token, to verify that it is a certain kind (token.getName()).  If it
   * is, then the next token is read and returned.  If it is not the case, then null is returned
   * and nothing is read.
   */
  public Token readNextIf(String kind) {
    Token token = nextToken();
    if (token.getName().equals(kind)) return token;
    _tqueue.push(token);
    return null;
  }

  /**
   * This peeks at the next token, to verify that it is a certain kind (token.getName()).  If it
   * is, then the next token is read and returned.  If it is not the case, then an error is stored
   * indicating that the given description was expected; in this case, nothing is read.
   * The description may be left null, in which case the kind is used in the error message instead.
   */
  public Token expect(String kind, String description) {
    Token token = nextToken();
    if (token.getName().equals(kind)) return token;
    _tqueue.push(token);
    if (description == null) description = kind;
    storeError("Expected " + description + " but got " + (token.isEof() ? "end of input" :
      token.getName() + " (" + token.getText() + ")") + ".", token);
    return null;
  }

  /**
   * After having read a token, this pushes it back so that it can be read, peeked at etc again.
   */
  public void pushBack(Token token) {
    _tqueue.push(token);
  }
}

