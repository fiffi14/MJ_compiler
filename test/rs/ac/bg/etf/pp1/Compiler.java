package rs.ac.bg.etf.pp1;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileOutputStream;
import java.io.FileReader;
import java.io.IOException;
import java.io.Reader;

import java_cup.runtime.Symbol;

import org.apache.log4j.Logger;
import org.apache.log4j.xml.DOMConfigurator;

import rs.ac.bg.etf.pp1.ast.*;
import rs.ac.bg.etf.pp1.util.Log4JUtils;
import rs.etf.pp1.mj.runtime.Code;
import rs.etf.pp1.symboltable.*;
import rs.etf.pp1.symboltable.concepts.Obj;
import rs.etf.pp1.symboltable.concepts.Struct;
import rs.etf.pp1.symboltable.structure.HashTableDataStructure;

public class Compiler {

	static {
		DOMConfigurator.configure(Log4JUtils.instance().findLoggerConfigFile());
		Log4JUtils.instance().prepareLogFile(Logger.getRootLogger());
	}
	
	//private void addMethod()
	
	public static void tsdump() {
		Tab.dump();
	}
	
	public static void main(String[] args) throws Exception {
		
		Logger log = Logger.getLogger(Compiler.class);
		
		Reader br = null;
		try {
			File sourceCode = new File("test/program.mj");  
			log.info("Compiling source file: " + sourceCode.getAbsolutePath());
			
			br = new BufferedReader(new FileReader(sourceCode));
			Yylex lexer = new Yylex(br);
			
			/* ---- 2. Sintaksna analiza/formiranje AST ---- */
			
			MJParser p = new MJParser(lexer);
	        Symbol s = p.parse();  //formiranje AST
	        
	        Program prog = (Program)(s.value); 
	        
			// ispis AST
			log.info(prog.toString(""));
			log.info("=====================================================================");

			
			// inicijalizacija tabele simbola; prvo ide adr pa level
			Tab.init();
			
			for(Obj o: Tab.ordObj.getLocalSymbols()) {
				
				o.setFpPos(1);
			}
			for(Obj o: Tab.chrObj.getLocalSymbols()) {
				o.setFpPos(1);
			}
			for(Obj o: Tab.lenObj.getLocalSymbols()) {
				o.setFpPos(1);
			}
			Struct boolType = new Struct(Struct.Bool);
			Obj boolObj = Tab.insert(Obj.Type, "bool", boolType); // ** IME STRUCT CV SE NECE ISPISATI STO JE OKEJ
			boolObj.setAdr(-1);
			boolObj.setLevel(-1);
			
			
			Struct setType = new Struct(Struct.Enum);
			//setType.setMembers(null);
			Obj setObj = Tab.insert(Obj.Type, "set", setType);
			setObj.setAdr(-1);
			setObj.setLevel(-1);
			
			Obj addMeth = Tab.insert(Obj.Meth, "add", Tab.noType);
			addMeth.setLevel(2);
			{
				Tab.openScope();
				Tab.currentScope().addToLocals(new Obj(Obj.Var, "a", new Struct(setType.getKind()), 0, 1));
				
				Tab.currentScope().addToLocals(new Obj(Obj.Var, "b", Tab.intType, 1, 1));
				
				addMeth.setLocals(Tab.currentScope().getLocals());
				
				for(Obj o: addMeth.getLocalSymbols()) {
					o.setFpPos(1);
				}
				Tab.closeScope();
			}
			
			Obj addAllMeth = Tab.insert(Obj.Meth, "addAll", Tab.noType);
			addAllMeth.setLevel(2);
			{
				Tab.openScope();
				Tab.currentScope().addToLocals(new Obj(Obj.Var, "a", new Struct(setType.getKind()), 0, 1)); // PROMENI NA SETTYPE I PROVERI
				
				Tab.currentScope().addToLocals(new Obj(Obj.Var, "b", new Struct(Struct.Array, Tab.intType), 1, 1));
				
				addAllMeth.setLocals(Tab.currentScope().getLocals());
				
				for(Obj o: addAllMeth.getLocalSymbols()) {
					o.setFpPos(1);
				}
				Tab.closeScope();
			}
			
//			Obj addObj = Tab.insert(Obj.Meth, "add", new Struct(Struct.Set, Tab.intType);
			
			/* ---- 3. Semanticka analiza ---- */
			
			SemanticAnalyzer sa = new SemanticAnalyzer(); //sa da iskoristimo da obilazak naseg stabla
			prog.traverseBottomUp(sa); // bottom up koristimo jer je nas parser LALR bottom up
										// za svaki cvor na koji naleti u prog treba da se pozove odgovarajuci visit i da se ispisuju u logovi za odgce info
			
			
			//Ispis tabele simbola
			log.info("=====================================================================");
			//Tab.dump();
			Compiler.tsdump();
			
			if(!p.errorDetected && sa.passed()){
				
				/* ---- 4. Generisanje koda ---- */
				
				//File objFile = new File("test/" + args[0] + ".obj");

				File objFile = new File("test/program.obj");
				if(objFile.exists()) objFile.delete();
				
				CodeGenerator codeGen = new CodeGenerator();
				prog.traverseBottomUp(codeGen);
				Code.dataSize = sa.nVars; //num of glob vars
				Code.mainPc = codeGen.getMainPc();
				Code.write(new FileOutputStream(objFile));
				
				log.info("Parsiranje/Generisanje uspesno zavrseno!");
			}else{
				log.error("Parsiranje NIJE uspesno zavrseno!");
			}
			
			
			
		} 
		finally {
			if (br != null) try { br.close(); } catch (IOException e1) { log.error(e1.getMessage(), e1); }
		}

	}
	
	
}
