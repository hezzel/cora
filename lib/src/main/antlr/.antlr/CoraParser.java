// Generated from /Users/deividvale/Documents/cora-updated-build/lib/src/main/antlr/CoraParser.g4 by ANTLR 4.9.2

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
public class CoraParser extends Parser {
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
		RULE_constant = 0, RULE_type = 1, RULE_lowarrowtype = 2, RULE_higherarrowtype = 3, 
		RULE_typearrow = 4, RULE_onlytype = 5, RULE_declaration = 6, RULE_term = 7, 
		RULE_abstraction = 8, RULE_commatermlist = 9, RULE_binderlist = 10, RULE_binder = 11, 
		RULE_onlyterm = 12, RULE_simplerule = 13, RULE_program = 14, RULE_input = 15;
	private static String[] makeRuleNames() {
		return new String[] {
			"constant", "type", "lowarrowtype", "higherarrowtype", "typearrow", "onlytype", 
			"declaration", "term", "abstraction", "commatermlist", "binderlist", 
			"binder", "onlyterm", "simplerule", "program", "input"
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

	@Override
	public String getGrammarFileName() { return "CoraParser.g4"; }

	@Override
	public String[] getRuleNames() { return ruleNames; }

	@Override
	public String getSerializedATN() { return _serializedATN; }

	@Override
	public ATN getATN() { return _ATN; }



	public CoraParser(TokenStream input) {
		super(input);
		_interp = new ParserATNSimulator(this,_ATN,_decisionToDFA,_sharedContextCache);
	}

	public static class ConstantContext extends ParserRuleContext {
		public TerminalNode IDENTIFIER() { return getToken(CoraParser.IDENTIFIER, 0); }
		public TerminalNode STRING() { return getToken(CoraParser.STRING, 0); }
		public ConstantContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_constant; }
	}

	public final ConstantContext constant() throws RecognitionException {
		ConstantContext _localctx = new ConstantContext(_ctx, getState());
		enterRule(_localctx, 0, RULE_constant);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(32);
			_la = _input.LA(1);
			if ( !(_la==IDENTIFIER || _la==STRING) ) {
			_errHandler.recoverInline(this);
			}
			else {
				if ( _input.LA(1)==Token.EOF ) matchedEOF = true;
				_errHandler.reportMatch(this);
				consume();
			}
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

	public static class TypeContext extends ParserRuleContext {
		public ConstantContext constant() {
			return getRuleContext(ConstantContext.class,0);
		}
		public LowarrowtypeContext lowarrowtype() {
			return getRuleContext(LowarrowtypeContext.class,0);
		}
		public HigherarrowtypeContext higherarrowtype() {
			return getRuleContext(HigherarrowtypeContext.class,0);
		}
		public TerminalNode BRACKETOPEN() { return getToken(CoraParser.BRACKETOPEN, 0); }
		public TypeContext type() {
			return getRuleContext(TypeContext.class,0);
		}
		public TerminalNode BRACKETCLOSE() { return getToken(CoraParser.BRACKETCLOSE, 0); }
		public TypeContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_type; }
	}

	public final TypeContext type() throws RecognitionException {
		TypeContext _localctx = new TypeContext(_ctx, getState());
		enterRule(_localctx, 2, RULE_type);
		try {
			setState(41);
			_errHandler.sync(this);
			switch ( getInterpreter().adaptivePredict(_input,0,_ctx) ) {
			case 1:
				enterOuterAlt(_localctx, 1);
				{
				setState(34);
				constant();
				}
				break;
			case 2:
				enterOuterAlt(_localctx, 2);
				{
				setState(35);
				lowarrowtype();
				}
				break;
			case 3:
				enterOuterAlt(_localctx, 3);
				{
				setState(36);
				higherarrowtype();
				}
				break;
			case 4:
				enterOuterAlt(_localctx, 4);
				{
				setState(37);
				match(BRACKETOPEN);
				setState(38);
				type();
				setState(39);
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

	public static class LowarrowtypeContext extends ParserRuleContext {
		public ConstantContext constant() {
			return getRuleContext(ConstantContext.class,0);
		}
		public TypearrowContext typearrow() {
			return getRuleContext(TypearrowContext.class,0);
		}
		public TypeContext type() {
			return getRuleContext(TypeContext.class,0);
		}
		public LowarrowtypeContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_lowarrowtype; }
	}

	public final LowarrowtypeContext lowarrowtype() throws RecognitionException {
		LowarrowtypeContext _localctx = new LowarrowtypeContext(_ctx, getState());
		enterRule(_localctx, 4, RULE_lowarrowtype);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(43);
			constant();
			setState(44);
			typearrow();
			setState(45);
			type();
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

	public static class HigherarrowtypeContext extends ParserRuleContext {
		public TerminalNode BRACKETOPEN() { return getToken(CoraParser.BRACKETOPEN, 0); }
		public List<TypeContext> type() {
			return getRuleContexts(TypeContext.class);
		}
		public TypeContext type(int i) {
			return getRuleContext(TypeContext.class,i);
		}
		public TerminalNode BRACKETCLOSE() { return getToken(CoraParser.BRACKETCLOSE, 0); }
		public TypearrowContext typearrow() {
			return getRuleContext(TypearrowContext.class,0);
		}
		public HigherarrowtypeContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_higherarrowtype; }
	}

	public final HigherarrowtypeContext higherarrowtype() throws RecognitionException {
		HigherarrowtypeContext _localctx = new HigherarrowtypeContext(_ctx, getState());
		enterRule(_localctx, 6, RULE_higherarrowtype);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(47);
			match(BRACKETOPEN);
			setState(48);
			type();
			setState(49);
			match(BRACKETCLOSE);
			setState(50);
			typearrow();
			setState(51);
			type();
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

	public static class TypearrowContext extends ParserRuleContext {
		public TerminalNode ARROW() { return getToken(CoraParser.ARROW, 0); }
		public TerminalNode TYPEARROW() { return getToken(CoraParser.TYPEARROW, 0); }
		public TypearrowContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_typearrow; }
	}

	public final TypearrowContext typearrow() throws RecognitionException {
		TypearrowContext _localctx = new TypearrowContext(_ctx, getState());
		enterRule(_localctx, 8, RULE_typearrow);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(53);
			_la = _input.LA(1);
			if ( !(_la==ARROW || _la==TYPEARROW) ) {
			_errHandler.recoverInline(this);
			}
			else {
				if ( _input.LA(1)==Token.EOF ) matchedEOF = true;
				_errHandler.reportMatch(this);
				consume();
			}
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

	public static class OnlytypeContext extends ParserRuleContext {
		public TypeContext type() {
			return getRuleContext(TypeContext.class,0);
		}
		public TerminalNode EOF() { return getToken(CoraParser.EOF, 0); }
		public OnlytypeContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_onlytype; }
	}

	public final OnlytypeContext onlytype() throws RecognitionException {
		OnlytypeContext _localctx = new OnlytypeContext(_ctx, getState());
		enterRule(_localctx, 10, RULE_onlytype);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(55);
			type();
			setState(56);
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

	public static class DeclarationContext extends ParserRuleContext {
		public ConstantContext constant() {
			return getRuleContext(ConstantContext.class,0);
		}
		public TerminalNode DECLARE() { return getToken(CoraParser.DECLARE, 0); }
		public TypeContext type() {
			return getRuleContext(TypeContext.class,0);
		}
		public DeclarationContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_declaration; }
	}

	public final DeclarationContext declaration() throws RecognitionException {
		DeclarationContext _localctx = new DeclarationContext(_ctx, getState());
		enterRule(_localctx, 12, RULE_declaration);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(58);
			constant();
			setState(59);
			match(DECLARE);
			setState(60);
			type();
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
		public ConstantContext constant() {
			return getRuleContext(ConstantContext.class,0);
		}
		public List<TerminalNode> BRACKETOPEN() { return getTokens(CoraParser.BRACKETOPEN); }
		public TerminalNode BRACKETOPEN(int i) {
			return getToken(CoraParser.BRACKETOPEN, i);
		}
		public TerminalNode BRACKETCLOSE() { return getToken(CoraParser.BRACKETCLOSE, 0); }
		public TermContext term() {
			return getRuleContext(TermContext.class,0);
		}
		public CommatermlistContext commatermlist() {
			return getRuleContext(CommatermlistContext.class,0);
		}
		public AbstractionContext abstraction() {
			return getRuleContext(AbstractionContext.class,0);
		}
		public TermContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_term; }
	}

	public final TermContext term() throws RecognitionException {
		TermContext _localctx = new TermContext(_ctx, getState());
		enterRule(_localctx, 14, RULE_term);
		try {
			setState(80);
			_errHandler.sync(this);
			switch ( getInterpreter().adaptivePredict(_input,1,_ctx) ) {
			case 1:
				enterOuterAlt(_localctx, 1);
				{
				setState(62);
				constant();
				}
				break;
			case 2:
				enterOuterAlt(_localctx, 2);
				{
				setState(63);
				constant();
				setState(64);
				match(BRACKETOPEN);
				setState(65);
				match(BRACKETCLOSE);
				}
				break;
			case 3:
				enterOuterAlt(_localctx, 3);
				{
				setState(67);
				constant();
				setState(68);
				match(BRACKETOPEN);
				setState(69);
				term();
				setState(70);
				commatermlist();
				}
				break;
			case 4:
				enterOuterAlt(_localctx, 4);
				{
				setState(72);
				abstraction();
				}
				break;
			case 5:
				enterOuterAlt(_localctx, 5);
				{
				setState(73);
				match(BRACKETOPEN);
				setState(74);
				abstraction();
				setState(75);
				match(BRACKETCLOSE);
				setState(76);
				match(BRACKETOPEN);
				setState(77);
				term();
				setState(78);
				commatermlist();
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

	public static class AbstractionContext extends ParserRuleContext {
		public TerminalNode LAMBDA() { return getToken(CoraParser.LAMBDA, 0); }
		public BinderlistContext binderlist() {
			return getRuleContext(BinderlistContext.class,0);
		}
		public TerminalNode DOT() { return getToken(CoraParser.DOT, 0); }
		public TermContext term() {
			return getRuleContext(TermContext.class,0);
		}
		public AbstractionContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_abstraction; }
	}

	public final AbstractionContext abstraction() throws RecognitionException {
		AbstractionContext _localctx = new AbstractionContext(_ctx, getState());
		enterRule(_localctx, 16, RULE_abstraction);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(82);
			match(LAMBDA);
			setState(83);
			binderlist();
			setState(84);
			match(DOT);
			setState(85);
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

	public static class CommatermlistContext extends ParserRuleContext {
		public TerminalNode BRACKETCLOSE() { return getToken(CoraParser.BRACKETCLOSE, 0); }
		public TerminalNode COMMA() { return getToken(CoraParser.COMMA, 0); }
		public TermContext term() {
			return getRuleContext(TermContext.class,0);
		}
		public CommatermlistContext commatermlist() {
			return getRuleContext(CommatermlistContext.class,0);
		}
		public CommatermlistContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_commatermlist; }
	}

	public final CommatermlistContext commatermlist() throws RecognitionException {
		CommatermlistContext _localctx = new CommatermlistContext(_ctx, getState());
		enterRule(_localctx, 18, RULE_commatermlist);
		try {
			setState(92);
			_errHandler.sync(this);
			switch (_input.LA(1)) {
			case BRACKETCLOSE:
				enterOuterAlt(_localctx, 1);
				{
				setState(87);
				match(BRACKETCLOSE);
				}
				break;
			case COMMA:
				enterOuterAlt(_localctx, 2);
				{
				setState(88);
				match(COMMA);
				setState(89);
				term();
				setState(90);
				commatermlist();
				}
				break;
			default:
				throw new NoViableAltException(this);
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

	public static class BinderlistContext extends ParserRuleContext {
		public BinderContext binder() {
			return getRuleContext(BinderContext.class,0);
		}
		public TerminalNode COMMA() { return getToken(CoraParser.COMMA, 0); }
		public BinderlistContext binderlist() {
			return getRuleContext(BinderlistContext.class,0);
		}
		public BinderlistContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_binderlist; }
	}

	public final BinderlistContext binderlist() throws RecognitionException {
		BinderlistContext _localctx = new BinderlistContext(_ctx, getState());
		enterRule(_localctx, 20, RULE_binderlist);
		try {
			setState(99);
			_errHandler.sync(this);
			switch ( getInterpreter().adaptivePredict(_input,3,_ctx) ) {
			case 1:
				enterOuterAlt(_localctx, 1);
				{
				setState(94);
				binder();
				}
				break;
			case 2:
				enterOuterAlt(_localctx, 2);
				{
				setState(95);
				binder();
				setState(96);
				match(COMMA);
				setState(97);
				binderlist();
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

	public static class BinderContext extends ParserRuleContext {
		public TerminalNode IDENTIFIER() { return getToken(CoraParser.IDENTIFIER, 0); }
		public TerminalNode DECLARE() { return getToken(CoraParser.DECLARE, 0); }
		public TypeContext type() {
			return getRuleContext(TypeContext.class,0);
		}
		public BinderContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_binder; }
	}

	public final BinderContext binder() throws RecognitionException {
		BinderContext _localctx = new BinderContext(_ctx, getState());
		enterRule(_localctx, 22, RULE_binder);
		try {
			setState(105);
			_errHandler.sync(this);
			switch ( getInterpreter().adaptivePredict(_input,4,_ctx) ) {
			case 1:
				enterOuterAlt(_localctx, 1);
				{
				setState(101);
				match(IDENTIFIER);
				}
				break;
			case 2:
				enterOuterAlt(_localctx, 2);
				{
				setState(102);
				match(IDENTIFIER);
				setState(103);
				match(DECLARE);
				setState(104);
				type();
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

	public static class OnlytermContext extends ParserRuleContext {
		public TermContext term() {
			return getRuleContext(TermContext.class,0);
		}
		public TerminalNode EOF() { return getToken(CoraParser.EOF, 0); }
		public OnlytermContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_onlyterm; }
	}

	public final OnlytermContext onlyterm() throws RecognitionException {
		OnlytermContext _localctx = new OnlytermContext(_ctx, getState());
		enterRule(_localctx, 24, RULE_onlyterm);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(107);
			term();
			setState(108);
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

	public static class SimpleruleContext extends ParserRuleContext {
		public List<TermContext> term() {
			return getRuleContexts(TermContext.class);
		}
		public TermContext term(int i) {
			return getRuleContext(TermContext.class,i);
		}
		public TerminalNode ARROW() { return getToken(CoraParser.ARROW, 0); }
		public TerminalNode BRACEOPEN() { return getToken(CoraParser.BRACEOPEN, 0); }
		public TerminalNode BRACECLOSE() { return getToken(CoraParser.BRACECLOSE, 0); }
		public List<DeclarationContext> declaration() {
			return getRuleContexts(DeclarationContext.class);
		}
		public DeclarationContext declaration(int i) {
			return getRuleContext(DeclarationContext.class,i);
		}
		public SimpleruleContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_simplerule; }
	}

	public final SimpleruleContext simplerule() throws RecognitionException {
		SimpleruleContext _localctx = new SimpleruleContext(_ctx, getState());
		enterRule(_localctx, 26, RULE_simplerule);
		int _la;
		try {
			setState(126);
			_errHandler.sync(this);
			switch ( getInterpreter().adaptivePredict(_input,6,_ctx) ) {
			case 1:
				enterOuterAlt(_localctx, 1);
				{
				setState(110);
				term();
				setState(111);
				match(ARROW);
				setState(112);
				term();
				}
				break;
			case 2:
				enterOuterAlt(_localctx, 2);
				{
				setState(114);
				term();
				setState(115);
				match(ARROW);
				setState(116);
				term();
				setState(117);
				match(BRACEOPEN);
				setState(121);
				_errHandler.sync(this);
				_la = _input.LA(1);
				while (_la==IDENTIFIER || _la==STRING) {
					{
					{
					setState(118);
					declaration();
					}
					}
					setState(123);
					_errHandler.sync(this);
					_la = _input.LA(1);
				}
				setState(124);
				match(BRACECLOSE);
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

	public static class ProgramContext extends ParserRuleContext {
		public SimpleruleContext simplerule() {
			return getRuleContext(SimpleruleContext.class,0);
		}
		public ProgramContext program() {
			return getRuleContext(ProgramContext.class,0);
		}
		public DeclarationContext declaration() {
			return getRuleContext(DeclarationContext.class,0);
		}
		public ProgramContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_program; }
	}

	public final ProgramContext program() throws RecognitionException {
		ProgramContext _localctx = new ProgramContext(_ctx, getState());
		enterRule(_localctx, 28, RULE_program);
		try {
			setState(135);
			_errHandler.sync(this);
			switch ( getInterpreter().adaptivePredict(_input,7,_ctx) ) {
			case 1:
				enterOuterAlt(_localctx, 1);
				{
				setState(128);
				simplerule();
				setState(129);
				program();
				}
				break;
			case 2:
				enterOuterAlt(_localctx, 2);
				{
				setState(131);
				declaration();
				setState(132);
				program();
				}
				break;
			case 3:
				enterOuterAlt(_localctx, 3);
				{
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

	public static class InputContext extends ParserRuleContext {
		public ProgramContext program() {
			return getRuleContext(ProgramContext.class,0);
		}
		public TerminalNode EOF() { return getToken(CoraParser.EOF, 0); }
		public InputContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_input; }
	}

	public final InputContext input() throws RecognitionException {
		InputContext _localctx = new InputContext(_ctx, getState());
		enterRule(_localctx, 30, RULE_input);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(137);
			program();
			setState(138);
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

	public static final String _serializedATN =
		"\3\u608b\ua72a\u8133\ub9ed\u417c\u3be7\u7786\u5964\3)\u008f\4\2\t\2\4"+
		"\3\t\3\4\4\t\4\4\5\t\5\4\6\t\6\4\7\t\7\4\b\t\b\4\t\t\t\4\n\t\n\4\13\t"+
		"\13\4\f\t\f\4\r\t\r\4\16\t\16\4\17\t\17\4\20\t\20\4\21\t\21\3\2\3\2\3"+
		"\3\3\3\3\3\3\3\3\3\3\3\3\3\5\3,\n\3\3\4\3\4\3\4\3\4\3\5\3\5\3\5\3\5\3"+
		"\5\3\5\3\6\3\6\3\7\3\7\3\7\3\b\3\b\3\b\3\b\3\t\3\t\3\t\3\t\3\t\3\t\3\t"+
		"\3\t\3\t\3\t\3\t\3\t\3\t\3\t\3\t\3\t\3\t\3\t\5\tS\n\t\3\n\3\n\3\n\3\n"+
		"\3\n\3\13\3\13\3\13\3\13\3\13\5\13_\n\13\3\f\3\f\3\f\3\f\3\f\5\ff\n\f"+
		"\3\r\3\r\3\r\3\r\5\rl\n\r\3\16\3\16\3\16\3\17\3\17\3\17\3\17\3\17\3\17"+
		"\3\17\3\17\3\17\7\17z\n\17\f\17\16\17}\13\17\3\17\3\17\5\17\u0081\n\17"+
		"\3\20\3\20\3\20\3\20\3\20\3\20\3\20\5\20\u008a\n\20\3\21\3\21\3\21\3\21"+
		"\2\2\22\2\4\6\b\n\f\16\20\22\24\26\30\32\34\36 \2\4\4\2\33\33\"\"\3\2"+
		"\21\22\2\u008c\2\"\3\2\2\2\4+\3\2\2\2\6-\3\2\2\2\b\61\3\2\2\2\n\67\3\2"+
		"\2\2\f9\3\2\2\2\16<\3\2\2\2\20R\3\2\2\2\22T\3\2\2\2\24^\3\2\2\2\26e\3"+
		"\2\2\2\30k\3\2\2\2\32m\3\2\2\2\34\u0080\3\2\2\2\36\u0089\3\2\2\2 \u008b"+
		"\3\2\2\2\"#\t\2\2\2#\3\3\2\2\2$,\5\2\2\2%,\5\6\4\2&,\5\b\5\2\'(\7\b\2"+
		"\2()\5\4\3\2)*\7\t\2\2*,\3\2\2\2+$\3\2\2\2+%\3\2\2\2+&\3\2\2\2+\'\3\2"+
		"\2\2,\5\3\2\2\2-.\5\2\2\2./\5\n\6\2/\60\5\4\3\2\60\7\3\2\2\2\61\62\7\b"+
		"\2\2\62\63\5\4\3\2\63\64\7\t\2\2\64\65\5\n\6\2\65\66\5\4\3\2\66\t\3\2"+
		"\2\2\678\t\3\2\28\13\3\2\2\29:\5\4\3\2:;\7\2\2\3;\r\3\2\2\2<=\5\2\2\2"+
		"=>\7\16\2\2>?\5\4\3\2?\17\3\2\2\2@S\5\2\2\2AB\5\2\2\2BC\7\b\2\2CD\7\t"+
		"\2\2DS\3\2\2\2EF\5\2\2\2FG\7\b\2\2GH\5\20\t\2HI\5\24\13\2IS\3\2\2\2JS"+
		"\5\22\n\2KL\7\b\2\2LM\5\22\n\2MN\7\t\2\2NO\7\b\2\2OP\5\20\t\2PQ\5\24\13"+
		"\2QS\3\2\2\2R@\3\2\2\2RA\3\2\2\2RE\3\2\2\2RJ\3\2\2\2RK\3\2\2\2S\21\3\2"+
		"\2\2TU\7\17\2\2UV\5\26\f\2VW\7\20\2\2WX\5\20\t\2X\23\3\2\2\2Y_\7\t\2\2"+
		"Z[\7\f\2\2[\\\5\20\t\2\\]\5\24\13\2]_\3\2\2\2^Y\3\2\2\2^Z\3\2\2\2_\25"+
		"\3\2\2\2`f\5\30\r\2ab\5\30\r\2bc\7\f\2\2cd\5\26\f\2df\3\2\2\2e`\3\2\2"+
		"\2ea\3\2\2\2f\27\3\2\2\2gl\7\33\2\2hi\7\33\2\2ij\7\16\2\2jl\5\4\3\2kg"+
		"\3\2\2\2kh\3\2\2\2l\31\3\2\2\2mn\5\20\t\2no\7\2\2\3o\33\3\2\2\2pq\5\20"+
		"\t\2qr\7\21\2\2rs\5\20\t\2s\u0081\3\2\2\2tu\5\20\t\2uv\7\21\2\2vw\5\20"+
		"\t\2w{\7\6\2\2xz\5\16\b\2yx\3\2\2\2z}\3\2\2\2{y\3\2\2\2{|\3\2\2\2|~\3"+
		"\2\2\2}{\3\2\2\2~\177\7\7\2\2\177\u0081\3\2\2\2\u0080p\3\2\2\2\u0080t"+
		"\3\2\2\2\u0081\35\3\2\2\2\u0082\u0083\5\34\17\2\u0083\u0084\5\36\20\2"+
		"\u0084\u008a\3\2\2\2\u0085\u0086\5\16\b\2\u0086\u0087\5\36\20\2\u0087"+
		"\u008a\3\2\2\2\u0088\u008a\3\2\2\2\u0089\u0082\3\2\2\2\u0089\u0085\3\2"+
		"\2\2\u0089\u0088\3\2\2\2\u008a\37\3\2\2\2\u008b\u008c\5\36\20\2\u008c"+
		"\u008d\7\2\2\3\u008d!\3\2\2\2\n+R^ek{\u0080\u0089";
	public static final ATN _ATN =
		new ATNDeserializer().deserialize(_serializedATN.toCharArray());
	static {
		_decisionToDFA = new DFA[_ATN.getNumberOfDecisions()];
		for (int i = 0; i < _ATN.getNumberOfDecisions(); i++) {
			_decisionToDFA[i] = new DFA(_ATN.getDecisionState(i), i);
		}
	}
}