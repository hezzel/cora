// Generated from /Users/deividvale/Documents/cora-updated-build/lib/src/main/antlr/CoraLexer.g4 by ANTLR 4.9.2

// package cora.lib.parsers;

import java.util.ArrayList;

import org.antlr.v4.runtime.Lexer;
import org.antlr.v4.runtime.CharStream;
import org.antlr.v4.runtime.Token;
import org.antlr.v4.runtime.TokenStream;
import org.antlr.v4.runtime.*;
import org.antlr.v4.runtime.atn.*;
import org.antlr.v4.runtime.dfa.DFA;
import org.antlr.v4.runtime.misc.*;

@SuppressWarnings({"all", "warnings", "unchecked", "unused", "cast"})
public class CoraLexer extends Lexer {
	static { RuntimeMetaData.checkVersion("4.9.2", RuntimeMetaData.VERSION); }

	protected static final DFA[] _decisionToDFA;
	protected static final PredictionContextCache _sharedContextCache =
		new PredictionContextCache();
	public static final int
		WHITESPACE=1, COMMENT=2, ERRORStrayEndCom=3, BRACEOPEN=4, BRACECLOSE=5, 
		BRACKETOPEN=6, BRACKETCLOSE=7, SQUAREOPEN=8, SQUARECLOSE=9, COMMA=10, 
		COLON=11, DECLARE=12, LAMBDA=13, DOT=14, ARROW=15, TYPEARROW=16, INCLUDE=17, 
		SORT=18, OPERATOR=19, THEORY=20, ALIAS=21, TRANSLATE=22, DISPLAY=23, CHAIN=24, 
		IDENTIFIER=25, ERRORIdEndCom=26, IDENTIFIERWITHCOM=27, QUOTE=28, CLOSE=29, 
		OPEN=30, ERROREofInCom=31, STRING=32, STRINGCONTENT=33, ESCAPEDNEWLINE=34, 
		ESCAPEDESCAPE=35, ESCAPEDQUOTE=36, ERRORStringEof=37, ERRORstringNewline=38, 
		ERROREscape=39;
	public static final int
		INCOMMENT=1, INSTRING=2;
	public static String[] channelNames = {
		"DEFAULT_TOKEN_CHANNEL", "HIDDEN"
	};

	public static String[] modeNames = {
		"DEFAULT_MODE", "INCOMMENT", "INSTRING"
	};

	private static String[] makeRuleNames() {
		return new String[] {
			"IDCHAR", "IDPART", "A", "C", "D", "E", "H", "I", "L", "N", "O", "P", 
			"S", "R", "T", "U", "Y", "WHITESPACE", "COMMENT", "ERRORStrayEndCom", 
			"BRACEOPEN", "BRACECLOSE", "BRACKETOPEN", "BRACKETCLOSE", "SQUAREOPEN", 
			"SQUARECLOSE", "COMMA", "COLON", "DECLARE", "LAMBDA", "DOT", "ARROW", 
			"TYPEARROW", "INCLUDE", "SORT", "OPERATOR", "THEORY", "ALIAS", "TRANSLATE", 
			"DISPLAY", "CHAIN", "IDENTIFIER", "ERRORIdEndCom", "IDENTIFIERWITHCOM", 
			"QUOTE", "CLOSE", "OPEN", "ANYTHINGELSE", "ERROREofInCom", "STRING", 
			"STRINGCONTENT", "ESCAPEDNEWLINE", "ESCAPEDESCAPE", "ESCAPEDQUOTE", "ERRORStringEof", 
			"ERRORstringNewline", "ERROREscape"
		};
	}
	public static final String[] ruleNames = makeRuleNames();

	private static String[] makeLiteralNames() {
		return new String[] {
			null, null, null, null, "'{'", "'}'", "'('", "')'", "'['", "']'", "','", 
			"':'", "'::'", null, "'.'", null, null, null, null, null, null, null, 
			null, null, null, null, null, null, null, null, null, null, null, null, 
			null, null, null, null, null, "'\\'"
		};
	}
	private static final String[] _LITERAL_NAMES = makeLiteralNames();
	private static String[] makeSymbolicNames() {
		return new String[] {
			null, "WHITESPACE", "COMMENT", "ERRORStrayEndCom", "BRACEOPEN", "BRACECLOSE", 
			"BRACKETOPEN", "BRACKETCLOSE", "SQUAREOPEN", "SQUARECLOSE", "COMMA", 
			"COLON", "DECLARE", "LAMBDA", "DOT", "ARROW", "TYPEARROW", "INCLUDE", 
			"SORT", "OPERATOR", "THEORY", "ALIAS", "TRANSLATE", "DISPLAY", "CHAIN", 
			"IDENTIFIER", "ERRORIdEndCom", "IDENTIFIERWITHCOM", "QUOTE", "CLOSE", 
			"OPEN", "ERROREofInCom", "STRING", "STRINGCONTENT", "ESCAPEDNEWLINE", 
			"ESCAPEDESCAPE", "ESCAPEDQUOTE", "ERRORStringEof", "ERRORstringNewline", 
			"ERROREscape"
		};
	}
	private static final String[] _SYMBOLIC_NAMES = makeSymbolicNames();
	public static final Vocabulary VOCABULARY = new VocabularyImpl(_LITERAL_NAMES, _SYMBOLIC_NAMES);

	/**
	 * @deprecated Use {@link #VOCABULARY} instead.
	 */
	@Deprecated
	public static final String[] tokenNames;
	static {
		tokenNames = new String[_SYMBOLIC_NAMES.length];
		for (int i = 0; i < tokenNames.length; i++) {
			tokenNames[i] = VOCABULARY.getLiteralName(i);
			if (tokenNames[i] == null) {
				tokenNames[i] = VOCABULARY.getSymbolicName(i);
			}

			if (tokenNames[i] == null) {
				tokenNames[i] = "<INVALID>";
			}
		}
	}

	@Override
	@Deprecated
	public String[] getTokenNames() {
		return tokenNames;
	}

	@Override

	public Vocabulary getVocabulary() {
		return VOCABULARY;
	}


	  private int comment_depth = 0;
	  private String comment_start = "";
	  private String string_start = "";
	  private String string_so_far = "";

	  private ArrayList<String> warnings = new ArrayList<String>();

	  private String positionText(int pos) { return "" + getLine() + ":" + (pos+1); }

	  private void reportError(int pos, String txt) {
	    warnings.add(positionText(pos) + ": " + txt);
	  }

	  public ArrayList<String> queryWarnings() {
	    return warnings;
	  }


	public CoraLexer(CharStream input) {
		super(input);
		_interp = new LexerATNSimulator(this,_ATN,_decisionToDFA,_sharedContextCache);
	}

	@Override
	public String getGrammarFileName() { return "CoraLexer.g4"; }

	@Override
	public String[] getRuleNames() { return ruleNames; }

	@Override
	public String getSerializedATN() { return _serializedATN; }

	@Override
	public String[] getChannelNames() { return channelNames; }

	@Override
	public String[] getModeNames() { return modeNames; }

	@Override
	public ATN getATN() { return _ATN; }

	@Override
	public void action(RuleContext _localctx, int ruleIndex, int actionIndex) {
		switch (ruleIndex) {
		case 18:
			COMMENT_action((RuleContext)_localctx, actionIndex);
			break;
		case 19:
			ERRORStrayEndCom_action((RuleContext)_localctx, actionIndex);
			break;
		case 42:
			ERRORIdEndCom_action((RuleContext)_localctx, actionIndex);
			break;
		case 43:
			IDENTIFIERWITHCOM_action((RuleContext)_localctx, actionIndex);
			break;
		case 44:
			QUOTE_action((RuleContext)_localctx, actionIndex);
			break;
		case 45:
			CLOSE_action((RuleContext)_localctx, actionIndex);
			break;
		case 46:
			OPEN_action((RuleContext)_localctx, actionIndex);
			break;
		case 48:
			ERROREofInCom_action((RuleContext)_localctx, actionIndex);
			break;
		case 49:
			STRING_action((RuleContext)_localctx, actionIndex);
			break;
		case 50:
			STRINGCONTENT_action((RuleContext)_localctx, actionIndex);
			break;
		case 51:
			ESCAPEDNEWLINE_action((RuleContext)_localctx, actionIndex);
			break;
		case 52:
			ESCAPEDESCAPE_action((RuleContext)_localctx, actionIndex);
			break;
		case 53:
			ESCAPEDQUOTE_action((RuleContext)_localctx, actionIndex);
			break;
		case 54:
			ERRORStringEof_action((RuleContext)_localctx, actionIndex);
			break;
		case 55:
			ERRORstringNewline_action((RuleContext)_localctx, actionIndex);
			break;
		case 56:
			ERROREscape_action((RuleContext)_localctx, actionIndex);
			break;
		}
	}
	private void COMMENT_action(RuleContext _localctx, int actionIndex) {
		switch (actionIndex) {
		case 0:
			 comment_depth = 1;
			                      comment_start = positionText(getCharPositionInLine()-2);
			                      pushMode(INCOMMENT);
			                      more();
			                    
			break;
		}
	}
	private void ERRORStrayEndCom_action(RuleContext _localctx, int actionIndex) {
		switch (actionIndex) {
		case 1:
			 reportError(getCharPositionInLine()-2, "Unexpected closing comment */.");
			                      skip();
			                    
			break;
		}
	}
	private void ERRORIdEndCom_action(RuleContext _localctx, int actionIndex) {
		switch (actionIndex) {
		case 2:
			 String ident = getText().substring(0, getText().length()-2);
			                      reportError(getCharPositionInLine()-2, "Unexpected closing comment */ " +
			                                                             "following identifier " + ident + ".");
			                      setType(IDENTIFIER);
			                      setText(ident);
			                    
			break;
		}
	}
	private void IDENTIFIERWITHCOM_action(RuleContext _localctx, int actionIndex) {
		switch (actionIndex) {
		case 3:
			 setType(IDENTIFIER);
			                      String text = getText();
			                      setText(text.substring(0,text.length()-2));
			                      comment_depth = 1;
			                      comment_start = positionText(getCharPositionInLine()-2);
			                      pushMode(INCOMMENT);
			                    
			break;
		}
	}
	private void QUOTE_action(RuleContext _localctx, int actionIndex) {
		switch (actionIndex) {
		case 4:
			 string_start = positionText(getCharPositionInLine()-1);
			                      pushMode(INSTRING);
			                      more();
			                    
			break;
		}
	}
	private void CLOSE_action(RuleContext _localctx, int actionIndex) {
		switch (actionIndex) {
		case 5:
			 comment_depth--;
			                      if (comment_depth == 0) {
			                        popMode();
			                        skip();
			                      }
			                      else more();
			                    
			break;
		}
	}
	private void OPEN_action(RuleContext _localctx, int actionIndex) {
		switch (actionIndex) {
		case 6:
			 comment_depth++;
			                      more();
			                    
			break;
		}
	}
	private void ERROREofInCom_action(RuleContext _localctx, int actionIndex) {
		switch (actionIndex) {
		case 7:
			 popMode() ;
			                      warnings.add(comment_start + ": Unterminated comment.");
			                      skip();
			                    
			break;
		}
	}
	private void STRING_action(RuleContext _localctx, int actionIndex) {
		switch (actionIndex) {
		case 8:
			 setText(string_so_far);
			                      string_so_far = "";
			                      popMode();
			                    
			break;
		}
	}
	private void STRINGCONTENT_action(RuleContext _localctx, int actionIndex) {
		switch (actionIndex) {
		case 9:
			 string_so_far += getText();
			                      more();
			                    
			break;
		}
	}
	private void ESCAPEDNEWLINE_action(RuleContext _localctx, int actionIndex) {
		switch (actionIndex) {
		case 10:
			 string_so_far += "\n";
			                      more();
			                    
			break;
		}
	}
	private void ESCAPEDESCAPE_action(RuleContext _localctx, int actionIndex) {
		switch (actionIndex) {
		case 11:
			 string_so_far += "\\";
			                      more();
			                    
			break;
		}
	}
	private void ESCAPEDQUOTE_action(RuleContext _localctx, int actionIndex) {
		switch (actionIndex) {
		case 12:
			 string_so_far += "\"";
			                      more();
			                    
			break;
		}
	}
	private void ERRORStringEof_action(RuleContext _localctx, int actionIndex) {
		switch (actionIndex) {
		case 13:
			 setType(STRING);
			                      setText(string_so_far);
			                      string_so_far = "";
			                      warnings.add(string_start + ": String constant terminated by end of file.");
			                      popMode();
			                    
			break;
		}
	}
	private void ERRORstringNewline_action(RuleContext _localctx, int actionIndex) {
		switch (actionIndex) {
		case 14:
			 setType(STRING);
			                      setText(string_so_far);
			                      string_so_far = "";
			                      warnings.add(string_start + ": String constant terminated by end of line.");
			                      popMode();
			                    
			break;
		}
	}
	private void ERROREscape_action(RuleContext _localctx, int actionIndex) {
		switch (actionIndex) {
		case 15:
			 reportError(getCharPositionInLine()-1, "Unexpected escape in string.");
			                      more();
			                    
			break;
		}
	}

	public static final String _serializedATN =
		"\3\u608b\ua72a\u8133\ub9ed\u417c\u3be7\u7786\u5964\2)\u018f\b\1\b\1\b"+
		"\1\4\2\t\2\4\3\t\3\4\4\t\4\4\5\t\5\4\6\t\6\4\7\t\7\4\b\t\b\4\t\t\t\4\n"+
		"\t\n\4\13\t\13\4\f\t\f\4\r\t\r\4\16\t\16\4\17\t\17\4\20\t\20\4\21\t\21"+
		"\4\22\t\22\4\23\t\23\4\24\t\24\4\25\t\25\4\26\t\26\4\27\t\27\4\30\t\30"+
		"\4\31\t\31\4\32\t\32\4\33\t\33\4\34\t\34\4\35\t\35\4\36\t\36\4\37\t\37"+
		"\4 \t \4!\t!\4\"\t\"\4#\t#\4$\t$\4%\t%\4&\t&\4\'\t\'\4(\t(\4)\t)\4*\t"+
		"*\4+\t+\4,\t,\4-\t-\4.\t.\4/\t/\4\60\t\60\4\61\t\61\4\62\t\62\4\63\t\63"+
		"\4\64\t\64\4\65\t\65\4\66\t\66\4\67\t\67\48\t8\49\t9\4:\t:\3\2\3\2\3\3"+
		"\3\3\6\3|\n\3\r\3\16\3}\3\3\3\3\6\3\u0082\n\3\r\3\16\3\u0083\3\3\5\3\u0087"+
		"\n\3\3\4\3\4\3\5\3\5\3\6\3\6\3\7\3\7\3\b\3\b\3\t\3\t\3\n\3\n\3\13\3\13"+
		"\3\f\3\f\3\r\3\r\3\16\3\16\3\17\3\17\3\20\3\20\3\21\3\21\3\22\3\22\3\23"+
		"\6\23\u00a8\n\23\r\23\16\23\u00a9\3\23\3\23\3\24\3\24\3\24\3\24\3\24\3"+
		"\25\3\25\3\25\3\25\3\25\3\26\3\26\3\27\3\27\3\30\3\30\3\31\3\31\3\32\3"+
		"\32\3\33\3\33\3\34\3\34\3\35\3\35\3\36\3\36\3\36\3\37\3\37\3 \3 \3!\3"+
		"!\3!\5!\u00d2\n!\3\"\3\"\3\"\5\"\u00d7\n\"\3#\3#\3#\3#\3#\3#\3#\3#\3$"+
		"\3$\3$\3$\3$\3%\3%\3%\3%\3%\3%\3%\3%\3%\3&\3&\3&\3&\3&\3&\3&\3\'\3\'\3"+
		"\'\3\'\3\'\3\'\3(\3(\3(\3(\3(\3(\3(\3(\3(\3(\3)\3)\3)\3)\3)\3)\3)\3)\3"+
		"*\3*\3*\3*\3*\3*\3+\6+\u0115\n+\r+\16+\u0116\3+\7+\u011a\n+\f+\16+\u011d"+
		"\13+\3+\6+\u0120\n+\r+\16+\u0121\3+\6+\u0125\n+\r+\16+\u0126\3+\6+\u012a"+
		"\n+\r+\16+\u012b\3+\6+\u012f\n+\r+\16+\u0130\5+\u0133\n+\3,\7,\u0136\n"+
		",\f,\16,\u0139\13,\3,\6,\u013c\n,\r,\16,\u013d\3,\3,\3,\3-\7-\u0144\n"+
		"-\f-\16-\u0147\13-\3-\6-\u014a\n-\r-\16-\u014b\3-\3-\3-\3.\3.\3.\3/\3"+
		"/\3/\3/\3/\3\60\3\60\3\60\3\60\3\60\3\61\3\61\3\61\3\61\3\62\3\62\3\62"+
		"\3\63\3\63\3\63\3\64\6\64\u0169\n\64\r\64\16\64\u016a\3\64\3\64\3\65\3"+
		"\65\3\65\3\65\3\65\3\65\5\65\u0175\n\65\3\65\3\65\3\66\3\66\3\66\3\66"+
		"\3\66\3\67\3\67\3\67\3\67\3\67\38\38\38\58\u0186\n8\38\38\39\39\39\3:"+
		"\3:\3:\2\2;\5\2\7\2\t\2\13\2\r\2\17\2\21\2\23\2\25\2\27\2\31\2\33\2\35"+
		"\2\37\2!\2#\2%\2\'\3)\4+\5-\6/\7\61\b\63\t\65\n\67\139\f;\r=\16?\17A\20"+
		"C\21E\22G\23I\24K\25M\26O\27Q\30S\31U\32W\33Y\34[\35]\36_\37a c\2e!g\""+
		"i#k$m%o&q\'s(u)\5\2\3\4\26\16\2\13\f\17\17\"\"$$*,..\60\61<<]_}}\177\177"+
		"\u03bd\u03bd\4\2CCcc\4\2EEee\4\2FFff\4\2GGgg\4\2JJjj\4\2KKkk\4\2NNnn\4"+
		"\2PPpp\4\2QQqq\4\2RRrr\4\2UUuu\4\2TTtt\4\2VVvv\4\2WWww\4\2[[{{\5\2\13"+
		"\f\17\17\"\"\4\2^^\u03bd\u03bd\6\2\f\f\17\17$$^^\4\2\f\f\17\17\2\u0192"+
		"\2\'\3\2\2\2\2)\3\2\2\2\2+\3\2\2\2\2-\3\2\2\2\2/\3\2\2\2\2\61\3\2\2\2"+
		"\2\63\3\2\2\2\2\65\3\2\2\2\2\67\3\2\2\2\29\3\2\2\2\2;\3\2\2\2\2=\3\2\2"+
		"\2\2?\3\2\2\2\2A\3\2\2\2\2C\3\2\2\2\2E\3\2\2\2\2G\3\2\2\2\2I\3\2\2\2\2"+
		"K\3\2\2\2\2M\3\2\2\2\2O\3\2\2\2\2Q\3\2\2\2\2S\3\2\2\2\2U\3\2\2\2\2W\3"+
		"\2\2\2\2Y\3\2\2\2\2[\3\2\2\2\2]\3\2\2\2\3_\3\2\2\2\3a\3\2\2\2\3c\3\2\2"+
		"\2\3e\3\2\2\2\4g\3\2\2\2\4i\3\2\2\2\4k\3\2\2\2\4m\3\2\2\2\4o\3\2\2\2\4"+
		"q\3\2\2\2\4s\3\2\2\2\4u\3\2\2\2\5w\3\2\2\2\7\u0086\3\2\2\2\t\u0088\3\2"+
		"\2\2\13\u008a\3\2\2\2\r\u008c\3\2\2\2\17\u008e\3\2\2\2\21\u0090\3\2\2"+
		"\2\23\u0092\3\2\2\2\25\u0094\3\2\2\2\27\u0096\3\2\2\2\31\u0098\3\2\2\2"+
		"\33\u009a\3\2\2\2\35\u009c\3\2\2\2\37\u009e\3\2\2\2!\u00a0\3\2\2\2#\u00a2"+
		"\3\2\2\2%\u00a4\3\2\2\2\'\u00a7\3\2\2\2)\u00ad\3\2\2\2+\u00b2\3\2\2\2"+
		"-\u00b7\3\2\2\2/\u00b9\3\2\2\2\61\u00bb\3\2\2\2\63\u00bd\3\2\2\2\65\u00bf"+
		"\3\2\2\2\67\u00c1\3\2\2\29\u00c3\3\2\2\2;\u00c5\3\2\2\2=\u00c7\3\2\2\2"+
		"?\u00ca\3\2\2\2A\u00cc\3\2\2\2C\u00d1\3\2\2\2E\u00d6\3\2\2\2G\u00d8\3"+
		"\2\2\2I\u00e0\3\2\2\2K\u00e5\3\2\2\2M\u00ee\3\2\2\2O\u00f5\3\2\2\2Q\u00fb"+
		"\3\2\2\2S\u0105\3\2\2\2U\u010d\3\2\2\2W\u0132\3\2\2\2Y\u0137\3\2\2\2["+
		"\u0145\3\2\2\2]\u0150\3\2\2\2_\u0153\3\2\2\2a\u0158\3\2\2\2c\u015d\3\2"+
		"\2\2e\u0161\3\2\2\2g\u0164\3\2\2\2i\u0168\3\2\2\2k\u0174\3\2\2\2m\u0178"+
		"\3\2\2\2o\u017d\3\2\2\2q\u0185\3\2\2\2s\u0189\3\2\2\2u\u018c\3\2\2\2w"+
		"x\n\2\2\2x\6\3\2\2\2y\u0087\5\5\2\2z|\7\61\2\2{z\3\2\2\2|}\3\2\2\2}{\3"+
		"\2\2\2}~\3\2\2\2~\177\3\2\2\2\177\u0087\5\5\2\2\u0080\u0082\7,\2\2\u0081"+
		"\u0080\3\2\2\2\u0082\u0083\3\2\2\2\u0083\u0081\3\2\2\2\u0083\u0084\3\2"+
		"\2\2\u0084\u0085\3\2\2\2\u0085\u0087\5\5\2\2\u0086y\3\2\2\2\u0086{\3\2"+
		"\2\2\u0086\u0081\3\2\2\2\u0087\b\3\2\2\2\u0088\u0089\t\3\2\2\u0089\n\3"+
		"\2\2\2\u008a\u008b\t\4\2\2\u008b\f\3\2\2\2\u008c\u008d\t\5\2\2\u008d\16"+
		"\3\2\2\2\u008e\u008f\t\6\2\2\u008f\20\3\2\2\2\u0090\u0091\t\7\2\2\u0091"+
		"\22\3\2\2\2\u0092\u0093\t\b\2\2\u0093\24\3\2\2\2\u0094\u0095\t\t\2\2\u0095"+
		"\26\3\2\2\2\u0096\u0097\t\n\2\2\u0097\30\3\2\2\2\u0098\u0099\t\13\2\2"+
		"\u0099\32\3\2\2\2\u009a\u009b\t\f\2\2\u009b\34\3\2\2\2\u009c\u009d\t\r"+
		"\2\2\u009d\36\3\2\2\2\u009e\u009f\t\16\2\2\u009f \3\2\2\2\u00a0\u00a1"+
		"\t\17\2\2\u00a1\"\3\2\2\2\u00a2\u00a3\t\20\2\2\u00a3$\3\2\2\2\u00a4\u00a5"+
		"\t\21\2\2\u00a5&\3\2\2\2\u00a6\u00a8\t\22\2\2\u00a7\u00a6\3\2\2\2\u00a8"+
		"\u00a9\3\2\2\2\u00a9\u00a7\3\2\2\2\u00a9\u00aa\3\2\2\2\u00aa\u00ab\3\2"+
		"\2\2\u00ab\u00ac\b\23\2\2\u00ac(\3\2\2\2\u00ad\u00ae\7\61\2\2\u00ae\u00af"+
		"\7,\2\2\u00af\u00b0\3\2\2\2\u00b0\u00b1\b\24\3\2\u00b1*\3\2\2\2\u00b2"+
		"\u00b3\7,\2\2\u00b3\u00b4\7\61\2\2\u00b4\u00b5\3\2\2\2\u00b5\u00b6\b\25"+
		"\4\2\u00b6,\3\2\2\2\u00b7\u00b8\7}\2\2\u00b8.\3\2\2\2\u00b9\u00ba\7\177"+
		"\2\2\u00ba\60\3\2\2\2\u00bb\u00bc\7*\2\2\u00bc\62\3\2\2\2\u00bd\u00be"+
		"\7+\2\2\u00be\64\3\2\2\2\u00bf\u00c0\7]\2\2\u00c0\66\3\2\2\2\u00c1\u00c2"+
		"\7_\2\2\u00c28\3\2\2\2\u00c3\u00c4\7.\2\2\u00c4:\3\2\2\2\u00c5\u00c6\7"+
		"<\2\2\u00c6<\3\2\2\2\u00c7\u00c8\7<\2\2\u00c8\u00c9\7<\2\2\u00c9>\3\2"+
		"\2\2\u00ca\u00cb\t\23\2\2\u00cb@\3\2\2\2\u00cc\u00cd\7\60\2\2\u00cdB\3"+
		"\2\2\2\u00ce\u00cf\7/\2\2\u00cf\u00d2\7@\2\2\u00d0\u00d2\7\u2194\2\2\u00d1"+
		"\u00ce\3\2\2\2\u00d1\u00d0\3\2\2\2\u00d2D\3\2\2\2\u00d3\u00d4\7?\2\2\u00d4"+
		"\u00d7\7@\2\2\u00d5\u00d7\7\u21d4\2\2\u00d6\u00d3\3\2\2\2\u00d6\u00d5"+
		"\3\2\2\2\u00d7F\3\2\2\2\u00d8\u00d9\5\23\t\2\u00d9\u00da\5\27\13\2\u00da"+
		"\u00db\5\13\5\2\u00db\u00dc\5\25\n\2\u00dc\u00dd\5#\21\2\u00dd\u00de\5"+
		"\r\6\2\u00de\u00df\5\17\7\2\u00dfH\3\2\2\2\u00e0\u00e1\5\35\16\2\u00e1"+
		"\u00e2\5\31\f\2\u00e2\u00e3\5\37\17\2\u00e3\u00e4\5!\20\2\u00e4J\3\2\2"+
		"\2\u00e5\u00e6\5\31\f\2\u00e6\u00e7\5\33\r\2\u00e7\u00e8\5\17\7\2\u00e8"+
		"\u00e9\5\37\17\2\u00e9\u00ea\5\t\4\2\u00ea\u00eb\5!\20\2\u00eb\u00ec\5"+
		"\31\f\2\u00ec\u00ed\5\37\17\2\u00edL\3\2\2\2\u00ee\u00ef\5!\20\2\u00ef"+
		"\u00f0\5\21\b\2\u00f0\u00f1\5\17\7\2\u00f1\u00f2\5\31\f\2\u00f2\u00f3"+
		"\5\37\17\2\u00f3\u00f4\5%\22\2\u00f4N\3\2\2\2\u00f5\u00f6\5\t\4\2\u00f6"+
		"\u00f7\5\25\n\2\u00f7\u00f8\5\23\t\2\u00f8\u00f9\5\t\4\2\u00f9\u00fa\5"+
		"\35\16\2\u00faP\3\2\2\2\u00fb\u00fc\5!\20\2\u00fc\u00fd\5\37\17\2\u00fd"+
		"\u00fe\5\t\4\2\u00fe\u00ff\5\27\13\2\u00ff\u0100\5\35\16\2\u0100\u0101"+
		"\5\25\n\2\u0101\u0102\5\t\4\2\u0102\u0103\5!\20\2\u0103\u0104\5\17\7\2"+
		"\u0104R\3\2\2\2\u0105\u0106\5\r\6\2\u0106\u0107\5\23\t\2\u0107\u0108\5"+
		"\35\16\2\u0108\u0109\5\33\r\2\u0109\u010a\5\25\n\2\u010a\u010b\5\t\4\2"+
		"\u010b\u010c\5%\22\2\u010cT\3\2\2\2\u010d\u010e\5\13\5\2\u010e\u010f\5"+
		"\21\b\2\u010f\u0110\5\t\4\2\u0110\u0111\5\23\t\2\u0111\u0112\5\27\13\2"+
		"\u0112V\3\2\2\2\u0113\u0115\5\7\3\2\u0114\u0113\3\2\2\2\u0115\u0116\3"+
		"\2\2\2\u0116\u0114\3\2\2\2\u0116\u0117\3\2\2\2\u0117\u011b\3\2\2\2\u0118"+
		"\u011a\7\61\2\2\u0119\u0118\3\2\2\2\u011a\u011d\3\2\2\2\u011b\u0119\3"+
		"\2\2\2\u011b\u011c\3\2\2\2\u011c\u0133\3\2\2\2\u011d\u011b\3\2\2\2\u011e"+
		"\u0120\5\7\3\2\u011f\u011e\3\2\2\2\u0120\u0121\3\2\2\2\u0121\u011f\3\2"+
		"\2\2\u0121\u0122\3\2\2\2\u0122\u0124\3\2\2\2\u0123\u0125\7,\2\2\u0124"+
		"\u0123\3\2\2\2\u0125\u0126\3\2\2\2\u0126\u0124\3\2\2\2\u0126\u0127\3\2"+
		"\2\2\u0127\u0133\3\2\2\2\u0128\u012a\7\61\2\2\u0129\u0128\3\2\2\2\u012a"+
		"\u012b\3\2\2\2\u012b\u0129\3\2\2\2\u012b\u012c\3\2\2\2\u012c\u0133\3\2"+
		"\2\2\u012d\u012f\7,\2\2\u012e\u012d\3\2\2\2\u012f\u0130\3\2\2\2\u0130"+
		"\u012e\3\2\2\2\u0130\u0131\3\2\2\2\u0131\u0133\3\2\2\2\u0132\u0114\3\2"+
		"\2\2\u0132\u011f\3\2\2\2\u0132\u0129\3\2\2\2\u0132\u012e\3\2\2\2\u0133"+
		"X\3\2\2\2\u0134\u0136\5\7\3\2\u0135\u0134\3\2\2\2\u0136\u0139\3\2\2\2"+
		"\u0137\u0135\3\2\2\2\u0137\u0138\3\2\2\2\u0138\u013b\3\2\2\2\u0139\u0137"+
		"\3\2\2\2\u013a\u013c\7,\2\2\u013b\u013a\3\2\2\2\u013c\u013d\3\2\2\2\u013d"+
		"\u013b\3\2\2\2\u013d\u013e\3\2\2\2\u013e\u013f\3\2\2\2\u013f\u0140\7\61"+
		"\2\2\u0140\u0141\b,\5\2\u0141Z\3\2\2\2\u0142\u0144\5\7\3\2\u0143\u0142"+
		"\3\2\2\2\u0144\u0147\3\2\2\2\u0145\u0143\3\2\2\2\u0145\u0146\3\2\2\2\u0146"+
		"\u0149\3\2\2\2\u0147\u0145\3\2\2\2\u0148\u014a\7\61\2\2\u0149\u0148\3"+
		"\2\2\2\u014a\u014b\3\2\2\2\u014b\u0149\3\2\2\2\u014b\u014c\3\2\2\2\u014c"+
		"\u014d\3\2\2\2\u014d\u014e\7,\2\2\u014e\u014f\b-\6\2\u014f\\\3\2\2\2\u0150"+
		"\u0151\7$\2\2\u0151\u0152\b.\7\2\u0152^\3\2\2\2\u0153\u0154\7,\2\2\u0154"+
		"\u0155\7\61\2\2\u0155\u0156\3\2\2\2\u0156\u0157\b/\b\2\u0157`\3\2\2\2"+
		"\u0158\u0159\7\61\2\2\u0159\u015a\7,\2\2\u015a\u015b\3\2\2\2\u015b\u015c"+
		"\b\60\t\2\u015cb\3\2\2\2\u015d\u015e\13\2\2\2\u015e\u015f\3\2\2\2\u015f"+
		"\u0160\b\61\n\2\u0160d\3\2\2\2\u0161\u0162\7\2\2\3\u0162\u0163\b\62\13"+
		"\2\u0163f\3\2\2\2\u0164\u0165\7$\2\2\u0165\u0166\b\63\f\2\u0166h\3\2\2"+
		"\2\u0167\u0169\n\24\2\2\u0168\u0167\3\2\2\2\u0169\u016a\3\2\2\2\u016a"+
		"\u0168\3\2\2\2\u016a\u016b\3\2\2\2\u016b\u016c\3\2\2\2\u016c\u016d\b\64"+
		"\r\2\u016dj\3\2\2\2\u016e\u016f\7^\2\2\u016f\u0170\7\f\2\2\u0170\u0175"+
		"\7\17\2\2\u0171\u0172\7^\2\2\u0172\u0173\7\17\2\2\u0173\u0175\7\f\2\2"+
		"\u0174\u016e\3\2\2\2\u0174\u0171\3\2\2\2\u0175\u0176\3\2\2\2\u0176\u0177"+
		"\b\65\16\2\u0177l\3\2\2\2\u0178\u0179\7^\2\2\u0179\u017a\7^\2\2\u017a"+
		"\u017b\3\2\2\2\u017b\u017c\b\66\17\2\u017cn\3\2\2\2\u017d\u017e\7^\2\2"+
		"\u017e\u017f\7$\2\2\u017f\u0180\3\2\2\2\u0180\u0181\b\67\20\2\u0181p\3"+
		"\2\2\2\u0182\u0186\7\2\2\3\u0183\u0184\7^\2\2\u0184\u0186\7\2\2\3\u0185"+
		"\u0182\3\2\2\2\u0185\u0183\3\2\2\2\u0186\u0187\3\2\2\2\u0187\u0188\b8"+
		"\21\2\u0188r\3\2\2\2\u0189\u018a\t\25\2\2\u018a\u018b\b9\22\2\u018bt\3"+
		"\2\2\2\u018c\u018d\7^\2\2\u018d\u018e\b:\23\2\u018ev\3\2\2\2\31\2\3\4"+
		"}\u0083\u0086\u00a9\u00d1\u00d6\u0116\u011b\u0121\u0126\u012b\u0130\u0132"+
		"\u0137\u013d\u0145\u014b\u016a\u0174\u0185\24\b\2\2\3\24\2\3\25\3\3,\4"+
		"\3-\5\3.\6\3/\7\3\60\b\5\2\2\3\62\t\3\63\n\3\64\13\3\65\f\3\66\r\3\67"+
		"\16\38\17\39\20\3:\21";
	public static final ATN _ATN =
		new ATNDeserializer().deserialize(_serializedATN.toCharArray());
	static {
		_decisionToDFA = new DFA[_ATN.getNumberOfDecisions()];
		for (int i = 0; i < _ATN.getNumberOfDecisions(); i++) {
			_decisionToDFA[i] = new DFA(_ATN.getDecisionState(i), i);
		}
	}
}