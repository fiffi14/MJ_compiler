
package rs.ac.bg.etf.pp1;
import java_cup.runtime.Symbol;

%%

%{ //blok koda koji zelim da se direktno kopira u moju java klasu

	//ukljucivanje informacije o poziciji tokena
	private Symbol new_symbol(int type) {             //metoda koja pravi novi token/simbol
		return new Symbol(type, yyline+1, yycolumn);    //type - id tokena; yyline - linija na kojoj se token procitao; yycolumn - kolona/broj slova u liniji
	}
	
	//ukljucivanje informacije o poziciji tokena
	private Symbol new_symbol(int type, Object value) {   //value - vrednost procitanog tokena
		return new Symbol(type, yyline+1, yycolumn, value);
	}
	
	//vrednost koja se cita kada se u java kodu dodje do kraja fajla
	//napravi token vrednosti EOF
	//sym klasa ce kasnije biti napravljena u odnosu na leksicku fazu koja se trnt radi

%}

%cup
%line
%column

%xstate COMMENT


%eofval{
		return new_symbol(sym.EOF);  
%eofval}

%%

" "		{ }
"\b"	{ }
"\t"	{ }
"\r\n"	{ }
"\f"	{ }

"program"		{ return new_symbol(sym.PROG, yytext()); }
"return" 		{ return new_symbol(sym.RETURN, yytext()); }
"print"			{ return new_symbol(sym.PRINT, yytext()); }
"read"			{ return new_symbol(sym.READ, yytext()); }
"break"			{ return new_symbol(sym.BREAK, yytext()); }
"continue"		{ return new_symbol(sym.CONTINUE, yytext()); }
"if"			{ return new_symbol(sym.IF, yytext()); }
"else"			{ return new_symbol(sym.ELSE, yytext()); }
"do"			{ return new_symbol(sym.DO, yytext()); }
"while"			{ return new_symbol(sym.WHILE, yytext()); }
"new"			{ return new_symbol(sym.NEW, yytext()); }
"const"			{ return new_symbol(sym.CONST, yytext()); }
"void"			{ return new_symbol(sym.VOID, yytext()); }
"union"			{ return new_symbol(sym.UNION, yytext()); }
"map"			{ return new_symbol(sym.MAP, yytext()); }
"final"			{ return new_symbol(sym.FINAL, yytext()); }


"(" 			{ return new_symbol(sym.LEFTPAREN, yytext()); }
")" 			{ return new_symbol(sym.RIGHTPAREN, yytext()); }
"[" 			{ return new_symbol(sym.LEFTBRACKET, yytext()); }
"]" 			{ return new_symbol(sym.RIGHTBRACKET, yytext()); }
"{" 			{ return new_symbol(sym.LEFTBRACE, yytext()); }
"}" 			{ return new_symbol(sym.RIGHTBRACE, yytext()); }
";" 			{ return new_symbol(sym.SEMI, yytext()); }
":" 			{ return new_symbol(sym.TWODOTS, yytext()); }
"," 			{ return new_symbol(sym.COMMA, yytext()); }
"." 			{ return new_symbol(sym.DOT, yytext()); }
"++" 			{ return new_symbol(sym.INC, yytext()); }
"--" 			{ return new_symbol(sym.DEC, yytext()); }
"*" 			{ return new_symbol(sym.MUL, yytext()); }
"/" 			{ return new_symbol(sym.DIV, yytext()); }
"%" 			{ return new_symbol(sym.MOD, yytext()); }
"+" 			{ return new_symbol(sym.PLUS, yytext()); }
"-" 			{ return new_symbol(sym.MINUS, yytext()); }
"==" 			{ return new_symbol(sym.EQ, yytext()); }
"!=" 			{ return new_symbol(sym.NOTEQ, yytext()); }
">" 			{ return new_symbol(sym.GRT, yytext()); }
">=" 			{ return new_symbol(sym.GRTEQ, yytext()); }
"<" 			{ return new_symbol(sym.LSS, yytext()); }
"<=" 			{ return new_symbol(sym.LSSEQ, yytext()); }
"&&" 			{ return new_symbol(sym.AND, yytext()); }
"||" 			{ return new_symbol(sym.OR, yytext()); }
"=" 			{ return new_symbol(sym.ASSIGN, yytext()); }
"#"				{ return new_symbol(sym.HASH, yytext()); }
"^"				{ return new_symbol(sym.CAPPA, yytext()); }



"//" 				{ yybegin(COMMENT); }
<COMMENT> .			{ yybegin(COMMENT); }
<COMMENT> "\r\n"	{ yybegin(YYINITIAL); }

[0-9]+						  	{ return new_symbol(sym.NUMBER, new Integer (yytext())); }

"'"."'"							{ return new_symbol(sym.CHARACTER, new Character(yytext().charAt(1))); }
("true"|"false")				{ return new_symbol(sym.BOOL, yytext().equals("true")? 1 : 0); }
([a-z]|[A-Z])[a-z|A-Z|0-9|_]* 	{ return new_symbol(sym.IDENT, yytext()); }

. 								{ System.err.println("Leksicka greska (" + yytext() + ") na liniji " + (yyline+1) + " u koloni " + (yycolumn+1) + "\n"); }
