// Generated from /Users/deividvale/Documents/cora-updated-build/lib/src/main/antlr/TrsLexer.g4 by ANTLR 4.9.2

// package cora.lib.parsers;

import org.antlr.v4.runtime.Lexer;
import org.antlr.v4.runtime.CharStream;
import org.antlr.v4.runtime.Token;
import org.antlr.v4.runtime.TokenStream;
import org.antlr.v4.runtime.*;
import org.antlr.v4.runtime.atn.*;
import org.antlr.v4.runtime.dfa.DFA;
import org.antlr.v4.runtime.misc.*;

@SuppressWarnings({"all", "warnings", "unchecked", "unused", "cast"})
public class TrsLexer extends Lexer {
	static { RuntimeMetaData.checkVersion("4.9.2", RuntimeMetaData.VERSION); }

	protected static final DFA[] _decisionToDFA;
	protected static final PredictionContextCache _sharedContextCache =
		new PredictionContextCache();
	public static final int
		WHITESPACE=1, ARROW=2, EQUALITY=3, COMMA=4, IDENTIFIER=5, BRACKETOPEN=6, 
		BRACKETCLOSE=7, VARSDECSTART=8, SIGSTART=9, RULESDECSTART=10, COMMENT=11;
	public static String[] channelNames = {
		"DEFAULT_TOKEN_CHANNEL", "HIDDEN"
	};

	public static String[] modeNames = {
		"DEFAULT_MODE"
	};

	private static String[] makeRuleNames() {
		return new String[] {
			"WHITESPACE", "ARROW", "EQUALITY", "COMMA", "IDENTIFIER", "BRACKETOPEN", 
			"BRACKETCLOSE", "VARSDECSTART", "SIGSTART", "RULESDECSTART", "COMMENT"
		};
	}
	public static final String[] ruleNames = makeRuleNames();

	private static String[] makeLiteralNames() {
		return new String[] {
			null, null, null, null, "','", null, "'('", "')'"
		};
	}
	private static final String[] _LITERAL_NAMES = makeLiteralNames();
	private static String[] makeSymbolicNames() {
		return new String[] {
			null, "WHITESPACE", "ARROW", "EQUALITY", "COMMA", "IDENTIFIER", "BRACKETOPEN", 
			"BRACKETCLOSE", "VARSDECSTART", "SIGSTART", "RULESDECSTART", "COMMENT"
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


	public TrsLexer(CharStream input) {
		super(input);
		_interp = new LexerATNSimulator(this,_ATN,_decisionToDFA,_sharedContextCache);
	}

	@Override
	public String getGrammarFileName() { return "TrsLexer.g4"; }

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
	public boolean sempred(RuleContext _localctx, int ruleIndex, int predIndex) {
		switch (ruleIndex) {
		case 4:
			return IDENTIFIER_sempred((RuleContext)_localctx, predIndex);
		}
		return true;
	}
	private boolean IDENTIFIER_sempred(RuleContext _localctx, int predIndex) {
		switch (predIndex) {
		case 0:
			return _input.LA(1) != '>';
		case 1:
			return _input.LA(1) != '=';
		}
		return true;
	}

	public static final String _serializedATN =
		"\3\u608b\ua72a\u8133\ub9ed\u417c\u3be7\u7786\u5964\2\rX\b\1\4\2\t\2\4"+
		"\3\t\3\4\4\t\4\4\5\t\5\4\6\t\6\4\7\t\7\4\b\t\b\4\t\t\t\4\n\t\n\4\13\t"+
		"\13\4\f\t\f\3\2\6\2\33\n\2\r\2\16\2\34\3\2\3\2\3\3\3\3\3\3\3\4\3\4\3\4"+
		"\3\5\3\5\3\6\3\6\3\6\3\6\3\6\6\6.\n\6\r\6\16\6/\3\7\3\7\3\b\3\b\3\t\3"+
		"\t\3\t\3\t\3\t\3\n\3\n\3\n\3\n\3\n\3\13\3\13\3\13\3\13\3\13\3\13\3\13"+
		"\3\f\3\f\3\f\3\f\3\f\3\f\3\f\3\f\3\f\7\fP\n\f\f\f\16\fS\13\f\3\f\3\f\3"+
		"\f\3\f\3Q\2\r\3\3\5\4\7\5\t\6\13\7\r\b\17\t\21\n\23\13\25\f\27\r\3\2\4"+
		"\5\2\13\f\17\17\"\"\13\2\13\f\17\17\"\"$$*+./??^^~~\2\\\2\3\3\2\2\2\2"+
		"\5\3\2\2\2\2\7\3\2\2\2\2\t\3\2\2\2\2\13\3\2\2\2\2\r\3\2\2\2\2\17\3\2\2"+
		"\2\2\21\3\2\2\2\2\23\3\2\2\2\2\25\3\2\2\2\2\27\3\2\2\2\3\32\3\2\2\2\5"+
		" \3\2\2\2\7#\3\2\2\2\t&\3\2\2\2\13-\3\2\2\2\r\61\3\2\2\2\17\63\3\2\2\2"+
		"\21\65\3\2\2\2\23:\3\2\2\2\25?\3\2\2\2\27F\3\2\2\2\31\33\t\2\2\2\32\31"+
		"\3\2\2\2\33\34\3\2\2\2\34\32\3\2\2\2\34\35\3\2\2\2\35\36\3\2\2\2\36\37"+
		"\b\2\2\2\37\4\3\2\2\2 !\7/\2\2!\"\7@\2\2\"\6\3\2\2\2#$\7?\2\2$%\7?\2\2"+
		"%\b\3\2\2\2&\'\7.\2\2\'\n\3\2\2\2(.\n\3\2\2)*\7/\2\2*.\6\6\2\2+,\7?\2"+
		"\2,.\6\6\3\2-(\3\2\2\2-)\3\2\2\2-+\3\2\2\2./\3\2\2\2/-\3\2\2\2/\60\3\2"+
		"\2\2\60\f\3\2\2\2\61\62\7*\2\2\62\16\3\2\2\2\63\64\7+\2\2\64\20\3\2\2"+
		"\2\65\66\7*\2\2\66\67\7X\2\2\678\7C\2\289\7T\2\29\22\3\2\2\2:;\7*\2\2"+
		";<\7U\2\2<=\7K\2\2=>\7I\2\2>\24\3\2\2\2?@\7*\2\2@A\7T\2\2AB\7W\2\2BC\7"+
		"N\2\2CD\7G\2\2DE\7U\2\2E\26\3\2\2\2FG\7*\2\2GH\7E\2\2HI\7Q\2\2IJ\7O\2"+
		"\2JK\7O\2\2KL\7G\2\2LM\7P\2\2MQ\7V\2\2NP\13\2\2\2ON\3\2\2\2PS\3\2\2\2"+
		"QR\3\2\2\2QO\3\2\2\2RT\3\2\2\2SQ\3\2\2\2TU\7+\2\2UV\3\2\2\2VW\b\f\2\2"+
		"W\30\3\2\2\2\7\2\34-/Q\3\b\2\2";
	public static final ATN _ATN =
		new ATNDeserializer().deserialize(_serializedATN.toCharArray());
	static {
		_decisionToDFA = new DFA[_ATN.getNumberOfDecisions()];
		for (int i = 0; i < _ATN.getNumberOfDecisions(); i++) {
			_decisionToDFA[i] = new DFA(_ATN.getDecisionState(i), i);
		}
	}
}