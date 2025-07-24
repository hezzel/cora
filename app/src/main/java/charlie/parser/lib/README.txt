The parser library provides classes to create a custom lexer and parser.  The library offers the
following public classes for lexing:

* Token.java
  This class represents a single token in an input file or string.  It has a position, a token name
  (e.g., "WHITESPACE", "IDENTIFIER" -- the user classes can define what acceptable names are), and
  a text (the actual text at the given position in the input file, which this token represents).

* Lexer.java
  This interface represents a Lexer: a source of tokens.  In its essence, this is simply a class
  that can be asked for the next token, and once the input has been fully returned (as tokens), only
  the special EOF token is returned.

* TokenQueue.java
  This interface extends Lexer to allow for a token to be pushed back.  This token will then be the
  next to be returned.  An arbitrary number of tokens can be pushed back.

* LexerFactory.java
  To actually create Lexers and TokenQueues, the LexerFactory should be used.

  At its core, you can choose to create a lexer that generates tokens from a string, and a lexer
  that generates tokens from a file.

  Moreover, it is intended that the user can add additional features to a lexer essentially through
  the Decorator pattern: a number of extending classes is defined, which take a Lexer as argument
  and themselves implement the interface.  To gereate a token, they will use the underlying lexer,
  but may alter or discard the resulting token.  For example, they may omit tokens until they get
  one that is not whitespace, or combine strings together.  The LexerFactory can be used to create
  a number of such combinations, and users can also add their own features.
  
  The factory can also be used to create a TokenQueue from a given Lexer.

* LexerException.java
  This exception may be thrown by nextToken if something went wrong while tokenising.  This could
  be a file reading error, or it could be something custom; for example, a lexer could choose to
  throw an error if specific tokens are encountered.  This exception should be handled when using
  Lexer::nextToken().

In addition, it offers the following two classes for parsing:
  
* ErrorCollector.java
  This class is used to keep track of errors as they occur during parsing.  This is useful to allow
  for parsers with some level of error recovery,  The ErrorCollector can be set up to accept a fixed
  number of errors; if more are reported, they are not stored.  This is to avoid excessively pages
  upon pages of errors when the parser fails.

* ParsingStatus.java
  This is the core class for the parser.  It keeps track of a TokenQueue, and can be used to look
  ahead, and both generate and store errors.  If too many errors arise, it will throw a
  ParsingException, and can also be prompted to do so if any errors have occurred.

For more detailed information and examples, see the wiki page about parsing.

