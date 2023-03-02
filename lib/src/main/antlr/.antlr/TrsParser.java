// Generated from /Users/deividvale/Documents/cora-updated-build/lib/src/main/antlr/TrsParser.g4 by ANTLR 4.9.2

  // package cora.lib.parsers;

import org.antlr.v4.runtime.atn.*;
import org.antlr.v4.runtime.dfa.DFA;
import org.antlr.v4.runtime.*;
import org.antlr.v4.runtime.misc.*;
import org.antlr.v4.runtime.tree.*;
import java.util.List;
import java.util.Iterator;
import java.util.ArrayList;

@SuppressWarnings({"all", "warnings", "unchecked", "unused", "cast"})
public class TrsParser extends Parser {
	static { RuntimeMetaData.checkVersion("4.9.2", RuntimeMetaData.VERSION); }

	protected static final DFA[] _decisionToDFA;
	protected static final PredictionContextCache _sharedContextCache =
		new PredictionContextCache();
	public static final int
		WHITESPACE=1, ARROW=2, EQUALITY=3, COMMA=4, IDENTIFIER=5, BRACKETOPEN=6, 
		BRACKETCLOSE=7, VARSDECSTART=8, SIGSTART=9, RULESDECSTART=10, COMMENT=11;
	public static final int
		RULE_typeorarity = 0, RULE_fundec = 1, RULE_term = 2, RULE_termlist = 3, 
		RULE_trsrule = 4, RULE_trs = 5, RULE_varlist = 6, RULE_siglist = 7, RULE_ruleslist = 8;
	private static String[] makeRuleNames() {
		return new String[] {
			"typeorarity", "fundec", "term", "termlist", "trsrule", "trs", "varlist", 
			"siglist", "ruleslist"
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

	@Override
	public String getGrammarFileName() { return "TrsParser.g4"; }

	@Override
	public String[] getRuleNames() { return ruleNames; }

	@Override
	public String getSerializedATN() { return _serializedATN; }

	@Override
	public ATN getATN() { return _ATN; }

	public TrsParser(TokenStream input) {
		super(input);
		_interp = new ParserATNSimulator(this,_ATN,_decisionToDFA,_sharedContextCache);
	}

	public static class TypeorarityContext extends ParserRuleContext {
		public List<TerminalNode> IDENTIFIER() { return getTokens(TrsParser.IDENTIFIER); }
		public TerminalNode IDENTIFIER(int i) {
			return getToken(TrsParser.IDENTIFIER, i);
		}
		public TerminalNode ARROW() { return getToken(TrsParser.ARROW, 0); }
		public TypeorarityContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_typeorarity; }
	}

	public final TypeorarityContext typeorarity() throws RecognitionException {
		TypeorarityContext _localctx = new TypeorarityContext(_ctx, getState());
		enterRule(_localctx, 0, RULE_typeorarity);
		int _la;
		try {
			setState(27);
			_errHandler.sync(this);
			switch ( getInterpreter().adaptivePredict(_input,1,_ctx) ) {
			case 1:
				enterOuterAlt(_localctx, 1);
				{
				setState(18);
				match(IDENTIFIER);
				}
				break;
			case 2:
				enterOuterAlt(_localctx, 2);
				{
				setState(22);
				_errHandler.sync(this);
				_la = _input.LA(1);
				while (_la==IDENTIFIER) {
					{
					{
					setState(19);
					match(IDENTIFIER);
					}
					}
					setState(24);
					_errHandler.sync(this);
					_la = _input.LA(1);
				}
				setState(25);
				match(ARROW);
				setState(26);
				match(IDENTIFIER);
				}
				break;
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class FundecContext extends ParserRuleContext {
		public TerminalNode BRACKETOPEN() { return getToken(TrsParser.BRACKETOPEN, 0); }
		public TerminalNode IDENTIFIER() { return getToken(TrsParser.IDENTIFIER, 0); }
		public TypeorarityContext typeorarity() {
			return getRuleContext(TypeorarityContext.class,0);
		}
		public TerminalNode BRACKETCLOSE() { return getToken(TrsParser.BRACKETCLOSE, 0); }
		public FundecContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_fundec; }
	}

	public final FundecContext fundec() throws RecognitionException {
		FundecContext _localctx = new FundecContext(_ctx, getState());
		enterRule(_localctx, 2, RULE_fundec);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(29);
			match(BRACKETOPEN);
			setState(30);
			match(IDENTIFIER);
			setState(31);
			typeorarity();
			setState(32);
			match(BRACKETCLOSE);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class TermContext extends ParserRuleContext {
		public TerminalNode IDENTIFIER() { return getToken(TrsParser.IDENTIFIER, 0); }
		public TerminalNode BRACKETOPEN() { return getToken(TrsParser.BRACKETOPEN, 0); }
		public TerminalNode BRACKETCLOSE() { return getToken(TrsParser.BRACKETCLOSE, 0); }
		public TermlistContext termlist() {
			return getRuleContext(TermlistContext.class,0);
		}
		public TermContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_term; }
	}

	public final TermContext term() throws RecognitionException {
		TermContext _localctx = new TermContext(_ctx, getState());
		enterRule(_localctx, 4, RULE_term);
		try {
			setState(43);
			_errHandler.sync(this);
			switch ( getInterpreter().adaptivePredict(_input,2,_ctx) ) {
			case 1:
				enterOuterAlt(_localctx, 1);
				{
				setState(34);
				match(IDENTIFIER);
				}
				break;
			case 2:
				enterOuterAlt(_localctx, 2);
				{
				setState(35);
				match(IDENTIFIER);
				setState(36);
				match(BRACKETOPEN);
				setState(37);
				match(BRACKETCLOSE);
				}
				break;
			case 3:
				enterOuterAlt(_localctx, 3);
				{
				setState(38);
				match(IDENTIFIER);
				setState(39);
				match(BRACKETOPEN);
				setState(40);
				termlist();
				setState(41);
				match(BRACKETCLOSE);
				}
				break;
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class TermlistContext extends ParserRuleContext {
		public TermContext term() {
			return getRuleContext(TermContext.class,0);
		}
		public TerminalNode COMMA() { return getToken(TrsParser.COMMA, 0); }
		public TermlistContext termlist() {
			return getRuleContext(TermlistContext.class,0);
		}
		public TermlistContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_termlist; }
	}

	public final TermlistContext termlist() throws RecognitionException {
		TermlistContext _localctx = new TermlistContext(_ctx, getState());
		enterRule(_localctx, 6, RULE_termlist);
		try {
			setState(50);
			_errHandler.sync(this);
			switch ( getInterpreter().adaptivePredict(_input,3,_ctx) ) {
			case 1:
				enterOuterAlt(_localctx, 1);
				{
				setState(45);
				term();
				}
				break;
			case 2:
				enterOuterAlt(_localctx, 2);
				{
				setState(46);
				term();
				setState(47);
				match(COMMA);
				setState(48);
				termlist();
				}
				break;
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class TrsruleContext extends ParserRuleContext {
		public List<TermContext> term() {
			return getRuleContexts(TermContext.class);
		}
		public TermContext term(int i) {
			return getRuleContext(TermContext.class,i);
		}
		public TerminalNode ARROW() { return getToken(TrsParser.ARROW, 0); }
		public TrsruleContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_trsrule; }
	}

	public final TrsruleContext trsrule() throws RecognitionException {
		TrsruleContext _localctx = new TrsruleContext(_ctx, getState());
		enterRule(_localctx, 8, RULE_trsrule);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(52);
			term();
			setState(53);
			match(ARROW);
			setState(54);
			term();
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class TrsContext extends ParserRuleContext {
		public RuleslistContext ruleslist() {
			return getRuleContext(RuleslistContext.class,0);
		}
		public TerminalNode EOF() { return getToken(TrsParser.EOF, 0); }
		public VarlistContext varlist() {
			return getRuleContext(VarlistContext.class,0);
		}
		public SiglistContext siglist() {
			return getRuleContext(SiglistContext.class,0);
		}
		public TrsContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_trs; }
	}

	public final TrsContext trs() throws RecognitionException {
		TrsContext _localctx = new TrsContext(_ctx, getState());
		enterRule(_localctx, 10, RULE_trs);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(57);
			_errHandler.sync(this);
			_la = _input.LA(1);
			if (_la==VARSDECSTART) {
				{
				setState(56);
				varlist();
				}
			}

			setState(60);
			_errHandler.sync(this);
			_la = _input.LA(1);
			if (_la==SIGSTART) {
				{
				setState(59);
				siglist();
				}
			}

			setState(62);
			ruleslist();
			setState(63);
			match(EOF);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class VarlistContext extends ParserRuleContext {
		public TerminalNode VARSDECSTART() { return getToken(TrsParser.VARSDECSTART, 0); }
		public TerminalNode BRACKETCLOSE() { return getToken(TrsParser.BRACKETCLOSE, 0); }
		public List<TerminalNode> IDENTIFIER() { return getTokens(TrsParser.IDENTIFIER); }
		public TerminalNode IDENTIFIER(int i) {
			return getToken(TrsParser.IDENTIFIER, i);
		}
		public VarlistContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_varlist; }
	}

	public final VarlistContext varlist() throws RecognitionException {
		VarlistContext _localctx = new VarlistContext(_ctx, getState());
		enterRule(_localctx, 12, RULE_varlist);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(65);
			match(VARSDECSTART);
			setState(69);
			_errHandler.sync(this);
			_la = _input.LA(1);
			while (_la==IDENTIFIER) {
				{
				{
				setState(66);
				match(IDENTIFIER);
				}
				}
				setState(71);
				_errHandler.sync(this);
				_la = _input.LA(1);
			}
			setState(72);
			match(BRACKETCLOSE);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class SiglistContext extends ParserRuleContext {
		public TerminalNode SIGSTART() { return getToken(TrsParser.SIGSTART, 0); }
		public TerminalNode BRACKETCLOSE() { return getToken(TrsParser.BRACKETCLOSE, 0); }
		public List<FundecContext> fundec() {
			return getRuleContexts(FundecContext.class);
		}
		public FundecContext fundec(int i) {
			return getRuleContext(FundecContext.class,i);
		}
		public SiglistContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_siglist; }
	}

	public final SiglistContext siglist() throws RecognitionException {
		SiglistContext _localctx = new SiglistContext(_ctx, getState());
		enterRule(_localctx, 14, RULE_siglist);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(74);
			match(SIGSTART);
			setState(78);
			_errHandler.sync(this);
			_la = _input.LA(1);
			while (_la==BRACKETOPEN) {
				{
				{
				setState(75);
				fundec();
				}
				}
				setState(80);
				_errHandler.sync(this);
				_la = _input.LA(1);
			}
			setState(81);
			match(BRACKETCLOSE);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class RuleslistContext extends ParserRuleContext {
		public TerminalNode RULESDECSTART() { return getToken(TrsParser.RULESDECSTART, 0); }
		public TerminalNode BRACKETCLOSE() { return getToken(TrsParser.BRACKETCLOSE, 0); }
		public List<TrsruleContext> trsrule() {
			return getRuleContexts(TrsruleContext.class);
		}
		public TrsruleContext trsrule(int i) {
			return getRuleContext(TrsruleContext.class,i);
		}
		public RuleslistContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_ruleslist; }
	}

	public final RuleslistContext ruleslist() throws RecognitionException {
		RuleslistContext _localctx = new RuleslistContext(_ctx, getState());
		enterRule(_localctx, 16, RULE_ruleslist);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(83);
			match(RULESDECSTART);
			setState(87);
			_errHandler.sync(this);
			_la = _input.LA(1);
			while (_la==IDENTIFIER) {
				{
				{
				setState(84);
				trsrule();
				}
				}
				setState(89);
				_errHandler.sync(this);
				_la = _input.LA(1);
			}
			setState(90);
			match(BRACKETCLOSE);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static final String _serializedATN =
		"\3\u608b\ua72a\u8133\ub9ed\u417c\u3be7\u7786\u5964\3\r_\4\2\t\2\4\3\t"+
		"\3\4\4\t\4\4\5\t\5\4\6\t\6\4\7\t\7\4\b\t\b\4\t\t\t\4\n\t\n\3\2\3\2\7\2"+
		"\27\n\2\f\2\16\2\32\13\2\3\2\3\2\5\2\36\n\2\3\3\3\3\3\3\3\3\3\3\3\4\3"+
		"\4\3\4\3\4\3\4\3\4\3\4\3\4\3\4\5\4.\n\4\3\5\3\5\3\5\3\5\3\5\5\5\65\n\5"+
		"\3\6\3\6\3\6\3\6\3\7\5\7<\n\7\3\7\5\7?\n\7\3\7\3\7\3\7\3\b\3\b\7\bF\n"+
		"\b\f\b\16\bI\13\b\3\b\3\b\3\t\3\t\7\tO\n\t\f\t\16\tR\13\t\3\t\3\t\3\n"+
		"\3\n\7\nX\n\n\f\n\16\n[\13\n\3\n\3\n\3\n\2\2\13\2\4\6\b\n\f\16\20\22\2"+
		"\2\2_\2\35\3\2\2\2\4\37\3\2\2\2\6-\3\2\2\2\b\64\3\2\2\2\n\66\3\2\2\2\f"+
		";\3\2\2\2\16C\3\2\2\2\20L\3\2\2\2\22U\3\2\2\2\24\36\7\7\2\2\25\27\7\7"+
		"\2\2\26\25\3\2\2\2\27\32\3\2\2\2\30\26\3\2\2\2\30\31\3\2\2\2\31\33\3\2"+
		"\2\2\32\30\3\2\2\2\33\34\7\4\2\2\34\36\7\7\2\2\35\24\3\2\2\2\35\30\3\2"+
		"\2\2\36\3\3\2\2\2\37 \7\b\2\2 !\7\7\2\2!\"\5\2\2\2\"#\7\t\2\2#\5\3\2\2"+
		"\2$.\7\7\2\2%&\7\7\2\2&\'\7\b\2\2\'.\7\t\2\2()\7\7\2\2)*\7\b\2\2*+\5\b"+
		"\5\2+,\7\t\2\2,.\3\2\2\2-$\3\2\2\2-%\3\2\2\2-(\3\2\2\2.\7\3\2\2\2/\65"+
		"\5\6\4\2\60\61\5\6\4\2\61\62\7\6\2\2\62\63\5\b\5\2\63\65\3\2\2\2\64/\3"+
		"\2\2\2\64\60\3\2\2\2\65\t\3\2\2\2\66\67\5\6\4\2\678\7\4\2\289\5\6\4\2"+
		"9\13\3\2\2\2:<\5\16\b\2;:\3\2\2\2;<\3\2\2\2<>\3\2\2\2=?\5\20\t\2>=\3\2"+
		"\2\2>?\3\2\2\2?@\3\2\2\2@A\5\22\n\2AB\7\2\2\3B\r\3\2\2\2CG\7\n\2\2DF\7"+
		"\7\2\2ED\3\2\2\2FI\3\2\2\2GE\3\2\2\2GH\3\2\2\2HJ\3\2\2\2IG\3\2\2\2JK\7"+
		"\t\2\2K\17\3\2\2\2LP\7\13\2\2MO\5\4\3\2NM\3\2\2\2OR\3\2\2\2PN\3\2\2\2"+
		"PQ\3\2\2\2QS\3\2\2\2RP\3\2\2\2ST\7\t\2\2T\21\3\2\2\2UY\7\f\2\2VX\5\n\6"+
		"\2WV\3\2\2\2X[\3\2\2\2YW\3\2\2\2YZ\3\2\2\2Z\\\3\2\2\2[Y\3\2\2\2\\]\7\t"+
		"\2\2]\23\3\2\2\2\13\30\35-\64;>GPY";
	public static final ATN _ATN =
		new ATNDeserializer().deserialize(_serializedATN.toCharArray());
	static {
		_decisionToDFA = new DFA[_ATN.getNumberOfDecisions()];
		for (int i = 0; i < _ATN.getNumberOfDecisions(); i++) {
			_decisionToDFA[i] = new DFA(_ATN.getDecisionState(i), i);
		}
	}
}