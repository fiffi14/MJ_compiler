package rs.ac.bg.etf.pp1;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Stack;

import rs.ac.bg.etf.pp1.ast.*;
import rs.ac.bg.etf.pp1.ast.VisitorAdaptor;
import rs.etf.pp1.mj.runtime.Code;
import rs.etf.pp1.symboltable.Tab;
import rs.etf.pp1.symboltable.concepts.Obj;
import rs.etf.pp1.symboltable.concepts.Struct;

//OPET OBILAZIMO AST I U VISIT-IMA GENERISEMO KOD

/* DESIGNATOR CE BITI UGL DEST PROMENLJIVA
 * NECE BITI ONDA AKO SE NADJE KAO DEO SMENE EXPR, ODNOSNO KAO FACTORLOW
 * 		JER TADA JE OPERAND KOJI BI MORAO DA SE NADJE NA STEKU
 * */

/* JMP INTRUKCIJE
 * - sve 3B
 * npr: 
 * pc:7  jmp 5 => pc:12 ..
 * 
 * - putJump(adr) => adr JE APS ADRESA SKOKA, KOJA SE U TELU OVE MT OBRADI KAO REL SKOK
 * 				=> primer iznad: putJmp(12);
 * 
 * - putFalseJump(op,adr) => IZVRSICE SKOK AKO USLOV NIJE ISPUNJEN; adr se stavlja da je nula za usl skok unapred 
 * 						  => uslovni skok, op - operacija, adr - aps adresa
 * 						  => jcc + inverse[op] - instr za usl skok i negirani uslov datom
 * 		
 * X  JMPEQ 12 -> SKOCI NA ADR 12 AKO SU PRVE DVE STVARI NA STEKU EKV
 * 
 * X+12 ...
 * 
 *  => PUTFALSEJUMP(CODE.NE, X+12)
 *  
 *  if(a==b){  exprStack: a, b
 *  -> AKO JE TRUE SAMO NASTAVLJAM I IMAM JMP ODMAH POSLE ESLE
 *  } else {
 *  -> AKO NIJE ISPUNJEN USLOV MORAM DA SKOCIM I NASTAVIM DALJE
 *  }
 *  
 *  - fixup(patchAdr) => KADA SE DODJE DO ELSE GRANE, TREBA POPRAVITI ONU ADRESU 0 (POCETAK ADRESE REL SKOKA)
 *  						A POPRAVICE SE DOSTAVLJAJUCI 2. BAJT TE JMP INSTR, STO JE 1. BAJT OFSETA ZA SKOK (JER JE ON 2B)
 *  				  => u tr izvrsavanja npr IF grane ne znamo gde ce se naci Else koji TREBA TEK DA SE VISIT
 *  npr:
 *  if(a==b) { 10;  jmp 0(11|12) => dostavice se 11 za patchAdr
 *  }
 *  else{ 70 => AKO JE POCETAK ELSE 70, GORE CE SE UPISATI 60 ZA PATCH JER JE TO RAZLIKA TOG REL SKOKA NEOPH DA SE SA 10 DODJE NA 70
 *  
 *  } 					 
 *  ==== OVO JE SVE COMPILETIME
 *  
 *  => U RUNTIME CE SE ZNATI ONDA GDE TREBA SKOCITI, ODN GDE JE ELSE, UKOLIKO DO TOGA DODJE
 *  
 * */


public class CodeGenerator extends VisitorAdaptor {
	
	private int mainPC;
	
	private Map<String, Integer> labels = new HashMap<>();
//  private Map<String, List<Integer>> patchAddrs = new HashMap<>();
	private int addAdr;
	
	private Map<Obj, Boolean> finalMap = new HashMap<>();
	private boolean finalFlagAssign = false;
	private boolean finalFlagElem = false;
	
	
	private void initBuiltinMethods() {
		// ord,chr,len,add,addall
		
		//'a' => 97 CHAR 'a' GLEDAMO KAO INT 97 (4B) 
		//ILI CEMO 97 DA PUSH NA STEK KAO 'a' 
		//KOJI CE ZBOG SAMOG STEKA ZAUZETI OPET 4B
		
		Obj ordMeth = Tab.ordObj; //Tab.find("ord");
		Obj chrMeth = Tab.chrObj; //Tab.find("chr");
		ordMeth.setAdr(Code.pc);
		chrMeth.setAdr(Code.pc);
		Code.put(Code.enter);
		Code.put(1);
		Code.put(1); //1 FORM PARM I 1 ZBIR PARM+LOK
		Code.put(Code.load_n);
		Code.put(Code.exit);
		Code.put(Code.return_);
		
		Obj lenMeth = Tab.lenObj;
		lenMeth.setAdr(Code.pc);
		Code.put(Code.enter); // adresa niza je form parametar na procSteku
		Code.put(1);
		Code.put(1);
		Code.put(Code.load_n); //load_0 form parametra
		Code.put(Code.arraylength);
		Code.put(Code.exit);
		Code.put(Code.return_); // ostavlja duzinu niza na steku
		
		Obj addMeth = Tab.find("add");
		int argsAdd = 2;
		int varsAdd = 3;
		//Obj pos = Tab.find("pos");
//		for(Obj o: addMeth.getLocalSymbols()) {
//			if(o.getName().equals("pos")) {
//				pos = o;
//				break;
//			}
//		}
		
		addAdr = Code.pc;
		addMeth.setAdr(addAdr);
		Code.put(Code.enter);
		Code.put(argsAdd);
		Code.put(varsAdd+argsAdd); // a, b, found, i, pos

		
		
		Code.loadConst(0);
		Code.put(Code.store_2); // found = 0
		
		Code.put(Code.load_n);
		Code.put(Code.arraylength);
		Code.loadConst(1);
		Code.put(Code.sub);
		Code.put(Code.store_3); // i = n-1  n -> num_of_elms + 1 
		
		Code.put(Code.load_n);
		Code.loadConst(0);
		Code.put(Code.aload);
		Code.put(Code.store);
		Code.put(4);		// pos = a[0]
		
		
		// for
		
		int forStart = Code.pc; //28
		
		Code.put(Code.load_3);    // set: pos | 0 0 0
								  //       0    1 2 3  => na pocetku i=3
		Code.loadConst(1);
		Code.putFalseJump(Code.ge, 0);
		int skipFor = Code.pc - 2;
		
		Code.put(Code.load_n);
		Code.put(Code.load_3);
		Code.put(Code.aload);
		Code.put(Code.load_1);
		Code.putFalseJump(Code.eq, 0);
		int beginIfEqElm = Code.pc-2;
		
		Code.loadConst(1);
		Code.put(Code.store_2); //found=1;
		Code.putJump(0);
		int elmFound = Code.pc - 2;
		
		Code.fixup(beginIfEqElm);
		
		//update i
		Code.put(Code.load_3);
		Code.loadConst(1);
		Code.put(Code.sub);
		Code.put(Code.store_3);
		
		Code.putJump(forStart);
		
		Code.fixup(skipFor);
		Code.fixup(elmFound);
		
		Code.put(Code.load_2);
		Code.loadConst(1);
		Code.putFalseJump(Code.ne, 0);
		int exitAdr = Code.pc - 2;
		
		Code.put(Code.load_n);
		Code.loadConst(0);
		Code.put(Code.load);
		Code.put(4);
		Code.loadConst(1);
		Code.put(Code.add);
		Code.put(Code.load_n);
		Code.put(Code.arraylength);
		Code.loadConst(1);
		Code.put(Code.sub);
		
		Code.put(Code.rem);
		Code.put(Code.astore); //a[0] = (pos+1)%(n-1) => n=3: pos={0,1}
		
		Code.put(Code.load_n);
		Code.put(Code.load);
		Code.put(4);
		Code.loadConst(1);
		Code.put(Code.add);
		Code.put(Code.load_1);
		Code.put(Code.astore); //a[pos+1] = b
		
		Code.fixup(exitAdr);
		
		Code.put(Code.exit);
		Code.put(Code.return_);
		
		
		
		//addAll
		Obj addAllObj = Tab.find("addAll");
		int addAllAdr = Code.pc;
		addAllObj.setAdr(addAllAdr);
		int argsAddAll = 2;
		int varsAddAll = 2;
		
		Code.put(Code.enter);
		Code.put(argsAdd);
		Code.put(varsAddAll+argsAddAll);
		
		//a, b, i, lenb
		
		Code.put(Code.load_1);
		Code.put(Code.arraylength);
		Code.put(Code.store_3);
		
		Code.loadConst(0);
		Code.put(Code.store_2);
		
		int forStartADDALL = Code.pc;
		
		Code.put(Code.load_n);
		Code.put(Code.load_1);
		Code.put(Code.load_2);
		Code.put(Code.aload);
		
		Code.put(Code.call);
		Code.put2(addAdr - Code.pc + 1);
		
		Code.put(Code.load_2);
		Code.loadConst(1);
		Code.put(Code.add);
		Code.put(Code.store_2);
		
		Code.put(Code.load_3); //n
		Code.put(Code.load_2); //i
		Code.putFalseJump(Code.le, forStartADDALL); //n>i
		
		Code.put(Code.exit);
		Code.put(Code.return_);
	
	}
		
	
	/*
	 * 
	 * 
	 * 
	 * 
	 * */
		
//		Code.put(Code.load);
//		Code.put(4);			// > iter
		
		
		/* a,b,found, i,  pos; set: pos _ _ _
		 * n,1, 2,    3,   4
		 * 
		 * load_3		| 
		 * loadConst1	|i
		 * jlt i<1		|i,1  *
		 * load_n		|
		 * load_3		|a
		 * aload		|a,i
		 * load_1		|a[i]
		 * jne a[i]!=b	|a[i], b  **lab
		 * loadConst1	|
		 * store_2		|1 => found = 1
		 * jmp ***		|
		 * fixup(**)
		 * load_3		|
		 * loadConst1	|i
		 * sub			|i,1
		 * store_3		|i-1
		 * putJump(forStart)
		 * fixup(*) jump over for at the end of it
		 * fixup(***) forward jump to elemfound
		 * 
		 * load_2		|
		 * loadConst1	| found
		 * jeq found==1	| found,1**** exit
		 * 
		 * load_n		|
		 * load
		 * put(4)		|a
		 * loadConst0	|a
		 * loadConst1	|a,0, pos
		 * add			|a,0,pos,1
		 * loadConst3	|a,0,pos+1
		 * rem			|a,0,(pos+1)%3
		 * astore		|  => a[0] = ..
		 * 
		 * load_n		|
		 * load
		 * 4			|a
		 * loadConst1	|a,pos
		 * add			|a,pos+1
		 * load_1		|a,pos+1,b
		 * astore		|
		 * 
		 * fixup(****)
		 * exit
		 * return_
		 * 
		 * */
		

	
	public CodeGenerator() {
		this.initBuiltinMethods();
	}
	

	public int getMainPc() {
		return this.mainPC;
	}
	
	/* ---- Methods ---- */
	
	@Override
	public void visit(MethodRetnName_void meth_void) {
		// ENTER MORA DA IMA 3B - OPCODE, b1, b2
		/* b1 - broj form parametara/level metode
		 * b2 - zbir form parm i lok prom
		 */
		
		meth_void.obj.setAdr(Code.pc); // PRE ENTER TREBA DA PAMTIMO PC JER BI JE POMERIO ZA GLOB PROM
		if(meth_void.getI1().equalsIgnoreCase("main")) {
			mainPC = Code.pc;
		}
		
		Code.put(Code.enter);
		Code.put(meth_void.obj.getLevel());; //b1; treba nam level => vratimo se u 3. i okacimo obj polje
		Code.put(meth_void.obj.getLocalSymbols().size()); //b2 - zbir lok prom i form parm
//	
	
	}
	
	
	@Override
	public void visit(MethodRetnName_anytype meth_anytype) {
		
		meth_anytype.obj.setAdr(Code.pc); // ADRESA CE OSTATI ZAPISANA, ODN ADRESA ENTER INSTR
		
		if(meth_anytype.getI2().equalsIgnoreCase("main")) {
			mainPC = Code.pc;
		}
		Code.put(Code.enter);
		Code.put(meth_anytype.obj.getLevel());
		Code.put(meth_anytype.obj.getLocalSymbols().size());
	}
	
	
	@Override
	public void visit(MethodDecl methDecl) {
		Code.put(Code.exit);
		Code.put(Code.return_); 
		/***** UVEK JEDAN ZA DRUGIM, EXIT ZA ENTER I RETURN ZA POVRT ADRESU *****/
	}
	
	
	/* ---- Single Statements ---- */
	
	@Override
	public void visit(SingleStatement_print ss_print) {
		
		/**
		 * - da li je ExprStack prazan -> MORA OSTATI PRAZAN NA KRAJU
		 * - Expr mora da se nadje na steku -> idemo na najjednostavnije: skup FactorLow
		 * */
		
		/* 1. LOADCONST ZA WIDTH MORA PRE PRINTA JER PRINTU TREBAJU 2 ARG SA STEKA
		 * 2. LOADCONST SE OVDE POZIVA JER SE MORA NACI NA VRHU STEKA/KASNIJE DODATI, 
		 * 		A DODACE SE KASNIJE JER SE SS CVOR KASNIJE OBILAZI
		 * */
		//Code.loadConst(0); // u varijanti bez width
		
		if(ss_print.getExpr().struct.equals(Tab.charType)) {
			Code.loadConst(0);
			Code.put(Code.bprint);
		}  else if(ss_print.getExpr().struct.getKind()==Struct.Array && ss_print.getExpr().struct.getElemType().equals(Tab.charType)) {
			
			Code.loadConst(0);
			
			int back = Code.pc;
			
			Code.put(Code.dup2);
			Code.put(Code.pop);
			Code.put(Code.arraylength);
			Code.loadConst(1);
			Code.put(Code.sub);
			Code.put(Code.dup2);
			
			Code.putFalseJump(Code.lt, 0);
			int skip = Code.pc - 2;
			
			Code.put(Code.pop);
			Code.put(Code.dup);
			Code.loadConst(0);
			Code.putFalseJump(Code.ne, 0);
			int skipFirstPrint = Code.pc - 2;
			
			Code.put(Code.dup2);
			Code.put(Code.baload);
			Code.loadConst(3);     /* ISPIS BLANKO ZNAKOVA */
			Code.put(Code.bprint);
			Code.loadConst(1);
			Code.put(Code.add);
			
			Code.putJump(back);
			
			Code.fixup(skipFirstPrint);
			Code.put(Code.dup2);
			Code.put(Code.baload);
			Code.loadConst(0);
			Code.put(Code.bprint);
			Code.loadConst(1);
			Code.put(Code.add);
			
			Code.putJump(back);
			
			Code.fixup(skip);
			Code.put(Code.pop);
			Code.put(Code.baload);
			Code.loadConst(3);      /* ISPIS BLANKO ZNAKOVA */
			Code.put(Code.bprint);
			
			/*
			 * arr
			 * back
			 * arr 0
			 * arr 0 arr 0
			 * arr 0 arr
			 * arr 0 n
			 * arr 0 n-1
			 * arr 0 n-1 0 n-1
			 * jge 0>=n-1
			 * arr 0 n-1
			 * arr 0
			 * arr 0 arr 0
			 * arr 0 arr[0]
			 * arr 0 arr[0] 0
			 * print -> printb
			 * arr 0
			 * arr 1
			 * jmp back
			 * fixup skip
			 * 
			 * arr 2 n-1
			 * arr 2
			 * arr[2]
			 * print/bprint
			 * 
			 * 
			 * */
		
		} else if(ss_print.getExpr().struct.getKind()==Struct.Array && ss_print.getExpr().struct.getElemType().equals(Tab.intType)) {
			
			Code.loadConst(0);
			
			int back = Code.pc;
			
			Code.put(Code.dup2);
			Code.put(Code.pop);
			Code.put(Code.arraylength);
			Code.loadConst(1);
			Code.put(Code.sub);
			Code.put(Code.dup2);
			
			Code.putFalseJump(Code.lt, 0);
			int skip = Code.pc - 2;
			
			Code.put(Code.pop);
			Code.put(Code.dup);
			Code.loadConst(0);
			Code.putFalseJump(Code.ne, 0);
			int skipFirstPrint = Code.pc - 2;
			
			Code.put(Code.dup2);
			Code.put(Code.aload);
			Code.loadConst(3);     /* ISPIS BLANKO ZNAKOVA */
			Code.put(Code.print);
			Code.loadConst(1);
			Code.put(Code.add);
			
			Code.putJump(back);
			
			Code.fixup(skipFirstPrint);
			Code.put(Code.dup2);
			Code.put(Code.aload);
			Code.loadConst(0);
			Code.put(Code.print);
			Code.loadConst(1);
			Code.put(Code.add);
			
			Code.putJump(back);
			
			Code.fixup(skip);
			Code.put(Code.pop);
			Code.put(Code.aload);
			Code.loadConst(3);      /* ISPIS BLANKO ZNAKOVA */
			Code.put(Code.print);
			
			/*
			 * arr
			 * back
			 * arr 0
			 * arr 0 arr 0
			 * arr 0 arr
			 * arr 0 n
			 * arr 0 n-1
			 * arr 0 n-1 0 n-1
			 * jge 0>=n-1
			 * arr 0 n-1
			 * arr 0
			 * arr 0 arr 0
			 * arr 0 arr[0]
			 * arr 0 arr[0] 0
			 * print -> printb
			 * arr 0
			 * arr 1
			 * jmp back
			 * fixup skip
			 * 
			 * arr 2 n-1
			 * arr 2
			 * arr[2]
			 * print/bprint
			 * 
			 * 
			 * */
		
		} else if(ss_print.getExpr().struct.getKind()==Struct.Enum) {
			
			Code.loadConst(1);
			
			int back = Code.pc;
			
			Code.put(Code.dup2);
			Code.put(Code.pop);
			Code.put(Code.arraylength);
			Code.loadConst(1);
			Code.put(Code.sub);
			Code.put(Code.dup2);
			
			Code.putFalseJump(Code.lt, 0);
			int skip = Code.pc - 2;
			
			Code.put(Code.pop);
			Code.put(Code.dup);
			Code.loadConst(1);
			Code.putFalseJump(Code.ne, 0);
			int skipFirstPrint = Code.pc - 2;
			
			Code.put(Code.dup2);
			Code.put(Code.aload);
			Code.loadConst(3);     /* ISPIS BLANKO ZNAKOVA */
			Code.put(Code.print);
			Code.loadConst(1);
			Code.put(Code.add);
			
			Code.putJump(back);
			
			Code.fixup(skipFirstPrint);
			Code.put(Code.dup2);
			Code.put(Code.aload);
			Code.loadConst(0);
			Code.put(Code.print);
			Code.loadConst(1);
			Code.put(Code.add);
			
			Code.putJump(back);
			
			Code.fixup(skip);
			Code.put(Code.pop);
			Code.put(Code.aload);
			Code.loadConst(3);      /* ISPIS BLANKO ZNAKOVA */
			Code.put(Code.print);
			/*
			 * s1 
			 * s1 1				s1 2
			 * s1 1 s1 1		s1 2 s1 2
			 * s1 1 s1			s1 2 s1
			 * s1 1 n			s1 2 n
			 * s1 1 n-1			s1 2 n-1
			 * s1 1 n-1 1 n-1	s1 2 n-1 2 n-1
			 * jge 1>=n-1
			 * s1 1 n-1
			 * s1 1
			 * s1 1 1
			 * s1 1 1 1
			 * jeq 1==1
			 * s1 1 s1[1]
			 * s1 1 s1[1] 0
			 * print
			 * s1 1 1
			 * s1 2
			 * 
			 * jmp back
			 * fixup
			 * s1 2 n-1
			 * s1 2
			 * s1[2]
			 * s1[2] 0
			 * print
			 * 
			 * */
			
		} else {
			Code.loadConst(0);
			Code.put(Code.print);
		}
		
		

	}
	
	@Override
	public void visit(SingleStatement_print_format ss_print_format) {
		
		if(ss_print_format.getExpr().struct.equals(Tab.charType)) {
			Code.loadConst(ss_print_format.getN2());
			Code.put(Code.bprint);
		} else if(ss_print_format.getExpr().struct.getKind()==Struct.Array && ss_print_format.getExpr().struct.getElemType().equals(Tab.intType)) {
			
			Code.loadConst(ss_print_format.getN2());
			Code.put(Code.aload);
			Code.loadConst(0);
			Code.put(Code.print);
			
		
		}  else if(ss_print_format.getExpr().struct.getKind()==Struct.Array && ss_print_format.getExpr().struct.getElemType().equals(Tab.charType)) {
			
			Code.loadConst(ss_print_format.getN2());
			Code.put(Code.baload);
			Code.loadConst(0);
			Code.put(Code.bprint);
			
		
		} else if(ss_print_format.getExpr().struct.getKind()==Struct.Enum) {
			
			Code.loadConst(1);
			
			int back = Code.pc;
			
			Code.put(Code.dup2);
			Code.put(Code.pop);
			Code.put(Code.arraylength);
			Code.loadConst(1);
			Code.put(Code.sub);
			Code.put(Code.dup2);
			
			Code.putFalseJump(Code.lt, 0);
			int skip = Code.pc - 2;
			
			Code.put(Code.pop);
			Code.put(Code.dup);
			Code.loadConst(1);
			Code.putFalseJump(Code.ne, 0);
			int skipFirstPrint = Code.pc - 2;
			
			Code.put(Code.dup2);
			Code.put(Code.aload);
			Code.loadConst(2 + ss_print_format.getN2());  /* ISPIS BLANKO ZNAKOVA */
			Code.put(Code.print);
			Code.loadConst(1);
			Code.put(Code.add);
			
			Code.putJump(back);
			
			Code.fixup(skipFirstPrint);
			Code.put(Code.dup2);
			Code.put(Code.aload);
			Code.loadConst(0 + ss_print_format.getN2());
			Code.put(Code.print);
			Code.loadConst(1);
			Code.put(Code.add);
			
			Code.putJump(back);
			
			Code.fixup(skip);
			Code.put(Code.pop);
			Code.put(Code.aload);
			Code.loadConst(2 + ss_print_format.getN2());  /* ISPIS BLANKO ZNAKOVA */
			Code.put(Code.print);
			
			
		} else {
			Code.loadConst(ss_print_format.getN2());
			Code.put(Code.print);
		}
	}
	
	@Override
	public void visit(SingleStatement_ret ss_ret) {
		Code.put(Code.exit);
		Code.put(Code.return_);
	}
	
	@Override
	public void visit(SingleStatement_retExpr ss_retExpr) { // OSTAVLJA EXPR NA STEKU PRI RET IZ MT
		Code.put(Code.exit);								// * AKO JE POZVANA SA LEVE STR - TO JE DJUBRE
		Code.put(Code.return_);								// * AKO JE POZVANA SA DESNE, BICE DESG I NEOPH ZA DALJE IZVRS
	}
	
	@Override
	public void visit(SingleStatement_read ss_read) { // bez preth arg i upisati u ono sto zelimo
		if(ss_read.getDesignator().obj.getType().equals(Tab.charType)) {
			Code.put(Code.bread);
		} else {
			Code.put(Code.read);
		}
		Code.store(ss_read.getDesignator().obj);
	}
	
	
	
	
	/* ---- FactorLow, Ops, Expr ---- */
	
	@Override
	public void visit(TermList_recr_addop tl_recr_addop) {
		if(tl_recr_addop.getAddop() instanceof Plus) {
			Code.put(Code.add);
		} else if(tl_recr_addop.getAddop() instanceof Minus) {
			Code.put(Code.sub);
		}
	}
	
	@Override
	public void visit(FactorList_recr_mulop fl_recr_mulop) {
		if(fl_recr_mulop.getMulop() instanceof Mul) {
			Code.put(Code.mul);
		} else if(fl_recr_mulop.getMulop() instanceof Div) {
			Code.put(Code.div);
		} else if(fl_recr_mulop.getMulop() instanceof Mod) {
			Code.put(Code.rem);
		}
	}
	
	@Override
	public void visit(FactorLow_num flow_num) {
		Code.loadConst(flow_num.getN1());
	}
	
	@Override
	public void visit(FactorLow_char flow_char) {
		Code.loadConst(flow_char.getC1());
	}
	
	@Override
	public void visit(FactorLow_bool flow_bool) {
		Code.loadConst(flow_bool.getB1());
	}
	
	@Override
	public void visit(FactorLow_desg_e flow_desg_e) {
		/* OVO PREPOZNAJE DA LI JE CON, VAR(GLOB/LOC).. */
		
		Code.load(flow_desg_e.getDesignator().obj);
	}
	
	/* AKO IMAMO POVR VREDNOST METODE I OSTACE NA STEKU I MORA DA OSTANE DA BI RACUNALO S NECIM*/
	
	
	@Override
	public void visit(FactorLow_desg_method_ActPars flow_meth) {
		int offset = flow_meth.getDesignator().obj.getAdr() - Code.pc;
		Code.put(Code.call);
		Code.put2(offset);
	}
	
	
	@Override
	public void visit(FactorLow_new_arr_expr flow_new_arr_expr) {
		if(flow_new_arr_expr.getType().getI1().equals("set")) {
			Code.loadConst(1);
			Code.put(Code.add);
		} else if(finalFlagAssign) {
			Code.loadConst(2);
			Code.put(Code.mul);
		}
		
		/* else if da li je fpPos == 2 i ako jeste alociraj duplo u odnosu ono sto je trnt na steku*/
		
		Code.put(Code.newarray);
		
		if(flow_new_arr_expr.getType().struct.equals(Tab.charType)) {
			Code.put(0);
		} else {
			Code.put(1);
		}
	
	}
	
	@Override
	public void visit(FactorLow_desg_hash flow_d_hash) {
		if(flow_d_hash.getDesignator().obj.getType().getKind() == Struct.Array && flow_d_hash.getDesignator().obj.getType().getElemType() == Tab.intType) {
			
			Code.load(flow_d_hash.getDesignator().obj);
			
			Code.put(Code.dup);
			Code.put(Code.dup);
			Code.loadConst(0);
			Code.put(Code.aload); /* baload */
			Code.put(Code.dup_x1);
			Code.put(Code.pop);
			Code.loadConst(1);
			
			int back = Code.pc;
			
			Code.put(Code.dup_x2);
			Code.put(Code.pop);
			Code.put(Code.arraylength);
			Code.put(Code.dup_x1);
			Code.put(Code.pop);
			Code.put(Code.dup_x2);
			Code.put(Code.pop);
			Code.put(Code.dup2);
			
			Code.putFalseJump(Code.lt, 0);
			int skipAll = Code.pc - 2;
			
			Code.put(Code.pop);
			Code.put(Code.dup_x1);
			Code.put(Code.pop);
			Code.put(Code.dup_x2);
			Code.put(Code.pop);
			Code.put(Code.dup_x1);
			Code.put(Code.pop);
			Code.put(Code.dup_x2);
			Code.put(Code.dup_x1);
			Code.put(Code.pop);
			Code.put(Code.dup_x2);
			Code.put(Code.aload); /* baload */
			Code.put(Code.dup2);
			
			Code.putFalseJump(Code.lt, 0);
			int skip2 = Code.pc - 2;
			
			Code.put(Code.dup_x1);
			Code.put(Code.pop);
			Code.put(Code.pop);
			Code.put(Code.dup_x2);
			Code.put(Code.pop);
			Code.put(Code.dup_x1);
			Code.put(Code.pop);
			Code.put(Code.dup_x2);
			Code.put(Code.dup_x1);
			Code.put(Code.pop);
			Code.loadConst(1);
			Code.put(Code.add);
			
			Code.putJump(back);
			Code.fixup(skip2);
			
			Code.put(Code.pop);
			Code.put(Code.dup_x2);
			Code.put(Code.pop);
			Code.put(Code.dup_x1);
			Code.put(Code.pop);
			Code.put(Code.dup_x2);
			Code.put(Code.dup_x1);
			Code.put(Code.pop);
			Code.loadConst(1);
			Code.put(Code.add);
			
			Code.putJump(back);
			
			Code.fixup(skipAll);
			
			Code.put(Code.pop);
			Code.put(Code.pop);
			Code.put(Code.dup_x1);
			Code.put(Code.pop);
			Code.put(Code.pop);
			
			
			/*
			 * ;arr = [1,2,3]
			 * ;n = 3

			 * 
			 * arr 
			 * 
			 * arr arr 
			 * arr arr arr
			 * arr arr arr 0
	***		 * arr arr arr[0]
			 * arr arr[0] arr arr[0]
			 * arr arr[0] arr
			 * arr arr[0] arr 1
			 * 
			 * back
			 * 
			 * arr 1 arr[0] arr 1 						arr 2 arr[1] arr 2
			 * arr 1 arr[0] arr							arr 2 arr[1] arr
			 * arr 1 arr[0] n							arr 2 arr[1] n
			 * arr 1 n arr[0] n							arr 2 n arr[1] n
			 * arr 1 n arr[0]							arr 2 n arr[1] 
			 * arr arr[0] 1 n							arr arr[1] 2 n
			 * arr arr[0] 1 n 1 n						arr arr[1] 2 n 2 n
			 * 
			 * jge skipAll
			 * 
	pop		 * arr arr[0] 1 n							arr arr[1] 2 n
	x1		 * arr arr[0] 1								arr arr[1] 2
	pop		 * arr 1 arr[0] 1							arr 2 arr[1] 2
	x2		 * arr 1 arr[0]								arr 2 arr[1]
	pop		 * arr[0] arr 1 arr[0] 						arr[1] arr 2 arr[1]
	x1		 * arr[0] arr 1								arr[1] arr 2
	pop		 * arr[0] 1 arr 1							arr[1] 2 arr 2
	x2		 * arr[0] 1 arr								arr[1] 2 arr
	x1		 * arr arr[0] 1 arr							arr arr[1] 2 arr
	pop		 * arr arr[0] arr 1 arr						arr arr[1] arr 2 arr
	x2		 * arr arr[0] arr 1							arr arr[1] arr 2
	ald		 * arr 1 arr[0] arr 1						arr 2 arr[1] arr 2
	dp2		 * arr 1 arr[0] arr[1]						arr 2 arr[1] arr[2]
			 * arr 1 arr[0] arr[1] arr[0] arr[1]		arr 2 arr[1] arr[2] arr[1] arr[2]
			 * 
			 * jge skip2
			 * 							
	x1		 * arr 1 arr[0] arr[1]						arr 2 arr[1] arr[2]
			 * arr 1 arr[1] arr[0] arr[1]  + pop,pop	arr 2 arr[2] arr[1] arr[2]
	x2		 * arr 1 arr[1]								arr 2 arr[2]
	pop		 * arr[1] arr 1 arr[1]						arr[2] arr 2 arr[2]
	x1		 * arr[1] arr 1		+pop					arr[2] arr 2
	x2		 * arr[1] 1 arr								arr[2] 2 arr 2
	x1		 * arr arr[1] 1 arr	+p						arr arr[2] 2 arr 
			 * arr arr[1] arr 1							arr arr[2] arr 2
			 * arr arr[1] arr 2							arr arr[2] arr 3
			 * 
			 * jmp back
			 * fixup(skip2)
			 * 
			 * arr 1 arr[0] arr[1]						arr 2 arr[0] arr[1]
			 * arr 1 arr[0]								arr 1 arr[0]
			 * arr[0] arr 1 arr[0]
			 * arr[0] arr 1
			 * arr[0] 1 arr
			 * arr arr[0] 1 arr
			 * arr arr[0] arr 1 arr
			 * arr arr[0] arr 1
			 * arr arr[0] arr 2							arr arr[0] arr 3
			 * 
			 * jmp back
			 * 
			 * fixup(skipAll)
			 * 
			 * arr arr[0] 1 n
			 * arr arr[0]
			 * arr[0] arr arr[0]
			 * arr[0]
			 * 
			 * */
		} else if(flow_d_hash.getDesignator().obj.getType().getKind() == Struct.Array && flow_d_hash.getDesignator().obj.getType().getElemType() == Tab.charType) {
			
			Code.load(flow_d_hash.getDesignator().obj);
			
			Code.put(Code.dup);
			Code.put(Code.dup);
			Code.loadConst(0);
			Code.put(Code.baload); /* baload */
			Code.put(Code.dup_x1);
			Code.put(Code.pop);
			Code.loadConst(1);
			
			int back = Code.pc;
			
			Code.put(Code.dup_x2);
			Code.put(Code.pop);
			Code.put(Code.arraylength);
			Code.put(Code.dup_x1);
			Code.put(Code.pop);
			Code.put(Code.dup_x2);
			Code.put(Code.pop);
			Code.put(Code.dup2);
			
			Code.putFalseJump(Code.lt, 0);
			int skipAll = Code.pc - 2;
			
			Code.put(Code.pop);
			Code.put(Code.dup_x1);
			Code.put(Code.pop);
			Code.put(Code.dup_x2);
			Code.put(Code.pop);
			Code.put(Code.dup_x1);
			Code.put(Code.pop);
			Code.put(Code.dup_x2);
			Code.put(Code.dup_x1);
			Code.put(Code.pop);
			Code.put(Code.dup_x2);
			Code.put(Code.baload); /* baload */
			Code.put(Code.dup2);
			
			Code.putFalseJump(Code.lt, 0);
			int skip2 = Code.pc - 2;
			
			Code.put(Code.dup_x1);
			Code.put(Code.pop);
			Code.put(Code.pop);
			Code.put(Code.dup_x2);
			Code.put(Code.pop);
			Code.put(Code.dup_x1);
			Code.put(Code.pop);
			Code.put(Code.dup_x2);
			Code.put(Code.dup_x1);
			Code.put(Code.pop);
			Code.loadConst(1);
			Code.put(Code.add);
			
			Code.putJump(back);
			Code.fixup(skip2);
			
			Code.put(Code.pop);
			Code.put(Code.dup_x2);
			Code.put(Code.pop);
			Code.put(Code.dup_x1);
			Code.put(Code.pop);
			Code.put(Code.dup_x2);
			Code.put(Code.dup_x1);
			Code.put(Code.pop);
			Code.loadConst(1);
			Code.put(Code.add);
			
			Code.putJump(back);
			
			Code.fixup(skipAll);
			
			Code.put(Code.pop);
			Code.put(Code.pop);
			Code.put(Code.dup_x1);
			Code.put(Code.pop);
			Code.put(Code.pop);
			
		} else if(flow_d_hash.getDesignator().obj.getType().getKind() == Struct.Enum) {
			
			Code.load(flow_d_hash.getDesignator().obj);
			
			Code.put(Code.dup);
			Code.put(Code.dup);
			Code.loadConst(1);
			Code.put(Code.aload); /* baload */
			Code.put(Code.dup_x1);
			Code.put(Code.pop);
			Code.loadConst(2);
			
			int back = Code.pc;
			
			Code.put(Code.dup_x2);
			Code.put(Code.pop);
			Code.put(Code.arraylength);
			Code.put(Code.dup_x1);
			Code.put(Code.pop);
			Code.put(Code.dup_x2);
			Code.put(Code.pop);
			Code.put(Code.dup2);
			
			Code.putFalseJump(Code.lt, 0);
			int skipAll = Code.pc - 2;
			
			Code.put(Code.pop);
			Code.put(Code.dup_x1);
			Code.put(Code.pop);
			Code.put(Code.dup_x2);
			Code.put(Code.pop);
			Code.put(Code.dup_x1);
			Code.put(Code.pop);
			Code.put(Code.dup_x2);
			Code.put(Code.dup_x1);
			Code.put(Code.pop);
			Code.put(Code.dup_x2);
			Code.put(Code.aload); /* baload */
			Code.put(Code.dup2);
			
			Code.putFalseJump(Code.lt, 0);
			int skip2 = Code.pc - 2;
			
			Code.put(Code.dup_x1);
			Code.put(Code.pop);
			Code.put(Code.pop);
			Code.put(Code.dup_x2);
			Code.put(Code.pop);
			Code.put(Code.dup_x1);
			Code.put(Code.pop);
			Code.put(Code.dup_x2);
			Code.put(Code.dup_x1);
			Code.put(Code.pop);
			Code.loadConst(1);
			Code.put(Code.add);
			
			Code.putJump(back);
			Code.fixup(skip2);
			
			Code.put(Code.pop);
			Code.put(Code.dup_x2);
			Code.put(Code.pop);
			Code.put(Code.dup_x1);
			Code.put(Code.pop);
			Code.put(Code.dup_x2);
			Code.put(Code.dup_x1);
			Code.put(Code.pop);
			Code.loadConst(1);
			Code.put(Code.add);
			
			Code.putJump(back);
			
			Code.fixup(skipAll);
			
			Code.put(Code.pop);
			Code.put(Code.pop);
			Code.put(Code.dup_x1);
			Code.put(Code.pop);
			Code.put(Code.pop);
			
		}
	}
	
	@Override
	public void visit(Factor_NoUnary f_NoUnary) {
		//rien
	}
	
	@Override
	public void visit(Factor_YesUnary f_u) {
		Code.put(Code.neg);
	}
	
	/* ZA DESG_ELEM ODNOSNO PRISTUP ELEM NIZA TIP NAM JE U EXPR, ALI ADRESA JE U IMENU/VAR TOG NIZA*/
	
	@Override
	public void visit(Expr_map e_map) {
		
		Code.loadConst(0);
		Code.load(e_map.getDesignator1().obj);
		Code.loadConst(0);

		int back = Code.pc;
		Code.put(Code.dup);
		Code.load(e_map.getDesignator1().obj);
		
		
		Code.put(Code.arraylength);
		Code.loadConst(1);
		Code.put(Code.sub);
		
		Code.putFalseJump(Code.lt, 0);
		int skip = Code.pc - 2;
		
		Code.put(Code.dup2);
		Code.put(Code.aload);
		
		Code.put(Code.call);
		Code.put2(e_map.getDesignator().obj.getAdr() - Code.pc + 1);
		
		Code.put(Code.dup_x2);
		Code.put(Code.pop);
		Code.loadConst(1);
		Code.put(Code.add);
		
		Code.putJump(back);
		Code.fixup(skip);
		
		Code.put(Code.aload);
		Code.put(Code.call);
		Code.put2(e_map.getDesignator().obj.getAdr() - Code.pc + 1);
		
		Code.load(e_map.getDesignator1().obj);
		Code.put(Code.arraylength);
		
		int back2 = Code.pc;
		
		Code.loadConst(1);
		Code.put(Code.sub);
		Code.put(Code.dup);
		Code.loadConst(0);
		
		Code.putFalseJump(Code.ge, 0);
		int skip2 = Code.pc - 2;
		
		Code.put(Code.dup_x2);
		Code.put(Code.pop);
		Code.put(Code.add);
		Code.put(Code.dup_x1);
		Code.put(Code.pop);
		
		Code.putJump(back2);
		Code.fixup(skip2);
		
		// ostaje zbir i iterator
		Code.put(Code.pop);
		
	}
	
	/* ------
	 * 0 a 0 				| 0 ret0 a 1
	 * 0 a 0 0 a		 	| 0 ret0 a 1 1 a
	 * 0 a 0 0 n 		 	| 0 ret0 a 1 1 a
	 * 0 a 0 0 n-1			| 0 ret0 a 1 1 n
	 * jge skip  			| ..
	 * 0 a 0 				| 0 ret0 a 1
	 * 0 a 0 a[0]			| 0 ret0 a 1 a[1]
	 * call					|
	 * 0 a 0 ret0			| 0 ret0 a 1 ret1
	 * 0 ret0 a 0 ret0		| 0 ret0 ret1 a 1 ret1
	 * 0 ret0 a 0			| 0 ret0 ret1 a 1 
	 * 0 ret0 a 0 1			
	 * 0 ret0 a 1			| 0 ret0 ret1 a 2
	 * jmp ------
	 * fixup(skip)
	 * 
	 * 0 ret0 ret1 a 2
	 * call
	 * 0 ret0 ret1 ret2
	 * 0 ret0 ret1 ret2 a
	 * 0 ret0 ret1 ret2 3
	 * 0 ret0 ret1 ret2 3 1
	 * 0 ret0 ret1 ret2 2 
	 * 0 ret0 ret1 ret2 2 2 0
	 * 0 ret0 ret1 ret2 2
	 * 0 ret0 2 ret1 ret2
	 * 0 ret0 2 ret12
	 * 0 ret0 ret12 2 ret12
	 * 0 ret0 ret12 2
	 * */
	
	
	@Override
	public void visit(DesignatorArrName dArrName) {
		Code.load(dArrName.obj); // ADRESA SE PUSHUJE IAKO JE SA LEVE I DESNE STR =
								// LEVA -> ZA ASTORE JER NAM JE NEOPH ADRESA ZA UPIS
		
	}
	
//	@Override
//	public void visit(Designator_elem d_elem) {
//		if(d_elem.getDesignatorArrName().obj.getType())
//	}
	
	
	/* ---- Designator Statements ---- */
	
	@Override
	public void visit(DesignatorStatement_assign ds_assign) {
		if(finalFlagElem) {

			Code.put(Code.dup_x2); Code.put(Code.pop);
			Code.put(Code.dup_x2); Code.put(Code.pop);
			Code.put(Code.dup_x2);

			Code.put(Code.dup_x2); Code.put(Code.pop);
			Code.put(Code.dup_x2); Code.put(Code.pop);
			Code.put(Code.dup_x2);
			
			Code.put(Code.dup2);

			Code.put(Code.dup_x1); Code.put(Code.pop);
			Code.put(Code.dup_x1); 

			Code.put(Code.arraylength);
			Code.loadConst(2);
			Code.put(Code.div);
			Code.put(Code.dup_x2);
			Code.put(Code.add);

			if(ds_assign.getExpr().struct.equals(Tab.intType)) {
				Code.put(Code.aload);
			} else if(ds_assign.getExpr().struct.equals(Tab.charType)) {
				Code.put(Code.baload);
			}
			Code.loadConst(1);
			
			
			Code.putFalseJump(Code.eq, 0);
			int store_ = Code.pc-2;
			
			Code.put(Code.trap);
			Code.loadConst(1);
			
			Code.fixup(store_);
			
			Code.put(Code.add);
			Code.loadConst(1);

			
			if(ds_assign.getExpr().struct.equals(Tab.intType)) {
				Code.put(Code.astore);
			} else if(ds_assign.getExpr().struct.equals(Tab.charType)) {
				Code.put(Code.bastore);
			}
			
			Code.store(ds_assign.getDesignator().obj);
			
			/*
			 * arr ind val dupx2 pop
			 * val arr ind dupx2 pop
			 * ind val arr dupx2
			 * arr ind val arr
			 * arr arr ind val
			 * arr val arr ind
			 * arr ind val arr ind arr ind
			 * arr ind val arr ind ind arr
			 * arr ind val arr ind arr ind arr
			 * arr ind val arr ind arr ind n/2
			 * arr ind val arr ind n/2 arr ind n/2
			 * arr ind val arr ind n/2 arr ind+n/2
			 * arr ind val arr ind n/2 arr[ind+n/2]
			 * arr ind val arr ind n/2 arr[ind+n/2] 1
			 * arr ind val arr ind n/2 arr[ind+n/2] 1

			 * jneq store_
			 * trap 1
			 * store_:
			 * arr ind val arr ind n/2
			 * arr ind val arr ind+n/2 1

			 * 
			 * */
		} else {
			Code.store(ds_assign.getDesignator().obj);
		}
		finalFlagAssign = false;
		finalFlagElem = false;
		/* proveriti da li je designator obj tipa Elem i ako jeste dovuci sa ind+n pozicije vrednost i ako je
		 * jednaka 0 na ind uradi store, ako je 1 onda baci trap */
	}
	
	
	/* poziv metode => u designator ce biti obj metode; upis adrese prve/enter instrukcije
	 * 
	 * call s => relativni skok, treba da mu damo razliku pocetka metode i adr trenutka skoka
	 * */
	
	/* METODE SA PARM PODRZ SE DA CE BITI NA STEKU JER JE TO LISTA EXPR */
	/* A METODA KOJA SKIDA TE FORM PARM JE ENTER METODA */
	
	@Override
	public void visit(DesignatorStatement_actPars ds_actPars) {
		int offset = ds_actPars.getDesignator().obj.getAdr() - Code.pc; //JAKO JE BITNO PRE PUT, JER CE SE PC INKR ZA 1 U TOM SLUC
		Code.put(Code.call);											// A NAMA TREBA TR POZ/VR PC
		Code.put2(offset); // s je 2B i zato PUT2
		
		
		/* U SIT KAD SE POZIVA SAMO POZIV DA BI SE OBRISALO TO DJUBRE, JER SE NECE ISKORISTITI DALJE*/
		
		if(ds_actPars.getDesignator().obj.getType() != Tab.noType) {
			Code.put(Code.pop);
		}
		
	}
	
	/*sa vars nema prob, doda dva operanda i sabere ili oduzme i storuje vrednost
	 * 
	 * kod nizova je prob sto ce ono izracunati kon vrednost ali ce za upis tog rez
	 * faliti indeks za astore tkd treba duplirati podatke u tom slucaju
	 * */
	
	@Override
	public void visit(DesignatorStatement_inc ds_inc) {
		if(ds_inc.getDesignator().obj.getKind() == Obj.Elem) {
			Code.put(Code.dup2);
		}
		Code.load(ds_inc.getDesignator().obj);
		Code.loadConst(1);
		Code.put(Code.add);
		Code.store(ds_inc.getDesignator().obj);
	}
	
	@Override
	public void visit(DesignatorStatement_dec ds_dec) {
		if(ds_dec.getDesignator().obj.getKind() == Obj.Elem) {
			Code.put(Code.dup2);
		}
		
		Code.load(ds_dec.getDesignator().obj);
		Code.loadConst(1);
		Code.put(Code.sub);
		Code.store(ds_dec.getDesignator().obj);
	}
	
	
	@Override
	public void visit(DesignatorStatement_setop ds_setop) {
		
		Obj res = ds_setop.getDesignator().obj;
		Obj s1 = ds_setop.getDesignator1().obj;
		Obj s2 = ds_setop.getDesignator2().obj;
		
		Code.loadConst(1);
		
		int back1 = Code.pc;
		
		Code.load(res);
		Code.load(s1);
		Code.put(Code.dup_x2);
		Code.put(Code.pop);
		Code.put(Code.dup_x2);
		Code.put(Code.pop);
		Code.put(Code.dup_x2);
		Code.put(Code.aload);
		
		Code.put(Code.call);
		Code.put2(addAdr - Code.pc + 1);
		
		Code.loadConst(1);
		Code.put(Code.add);
		Code.put(Code.dup);
		Code.load(s1);
		Code.put(Code.arraylength);
		Code.loadConst(1);
		Code.put(Code.sub);
		Code.putFalseJump(Code.gt, back1);
		
		Code.put(Code.pop);
		
		Code.loadConst(1);
		
		int back2 = Code.pc;
		
		Code.load(res);
		Code.load(s2);
		Code.put(Code.dup_x2);
		Code.put(Code.pop);
		Code.put(Code.dup_x2);
		Code.put(Code.pop);
		Code.put(Code.dup_x2);
		Code.put(Code.aload);
		
		Code.put(Code.call);
		Code.put2(addAdr - Code.pc + 1);
		
		Code.loadConst(1);
		Code.put(Code.add);
		Code.put(Code.dup);
		Code.load(s2);
		Code.put(Code.arraylength);
		Code.loadConst(1);
		Code.put(Code.sub);
		Code.putFalseJump(Code.gt, back2);
		
		Code.put(Code.pop);
		
		/*
		 * 1
		 * back1
		 * 1 res s1		2 res s1
		 * s1 1 res s1	s1 2 res s1
		 * s1 1 res		s1 2 res
		 * res s1 1 res	res s1 2 res
		 * res s1 1		res s1 2
		 * 1 res s1 1	2 res s1 2
		 * 1 res s1[1] 	2 res s1[2]
		 * call add		call add
		 * 1			2
		 * 2			3
		 * 2 2 s1		3 3 s1
		 * 2 2 n		3 3 n
		 * 2 2 n-1		3 3 n-1(3-1)
		 * jle back1 
		 * 
		 * 3
		 * -
		 * 1
		 * back2
		 * 1 res s2		2 res s2
		 * s2 1 res s2	s2 2 res s2
		 * s2 1 res		s2 2 res
		 * res s2 1 res	res s2 2 res
		 * res s2 1		res s2 2
		 * 1 res s2 1	2 res s2 2
		 * 1 res s2[1] 	2 res s2[2]
		 * call add		call add
		 * 1			2
		 * 2			3
		 * 2 2 s2		3 3 s2
		 * 2 2 n		3 3 n
		 * 2 2 n-1		3 3 n-1(3-1)
		 * jle back2
		 * 
		 * 3
		 * -
		 * 
		 * 
		 * */
		

		
		
	}
		/* s1[5], s2 = {2,3,5} s3 = {2,4} => uslovni skok
		 * 
		 * s1+0 = 2 (s2+0)
		 * s1+1 = 3 (s2+1)
		 * s1+2 = 5 (s2+2)
		 * 		  2 (s3+0)
		 * s1+3	= 4 (s3+1)
		 * 
		 * */
		
		
	@Override
	public void visit(DesignatorStatement_cappa dsc) {
		Code.load(dsc.getDesignator().obj);
		Code.loadConst(0);
		
		int back = Code.pc;
		Code.put(Code.dup2);
		Code.put(Code.pop);
		Code.put(Code.arraylength);
		Code.loadConst(1);
		Code.put(Code.sub);
		Code.put(Code.dup2);
		
		Code.putFalseJump(Code.le, 0);
		int skip = Code.pc - 2;
		
		Code.put(Code.pop);
		Code.put(Code.dup2);
		Code.put(Code.dup2);
		Code.put(Code.aload);
		Code.loadConst(dsc.getN2());
		Code.put(Code.mul);
		Code.put(Code.astore);
		Code.loadConst(1);
		Code.put(Code.add);
		
		Code.putJump(back);
		Code.fixup(skip);
		
		Code.put(Code.pop);
		Code.put(Code.pop);
		Code.put(Code.pop);
	}
	/* back
	 * arr 0
	 * arr 0 arr 0
	 * arr 0 arr
	 * arr 0 n-1
	 * arr 0 n-1 0 n-1
	 * jge skip
	 * arr 0 n-1
	 * arr 0
	 * arr 0 arr 0 arr 0
	 * arr 0 arr 0 arr[0] 
	 * arr 0 arr 0 arr[0] num
	 * arr 0 arr 0 arr[0]*num
	 * arr 0
	 * arr 1
	 * jump back
	 * arr n n-1
	 * pop * 3
	 * 
	 * */
	
	
	//goto na raniju adresu - putJmp(label)
	//goto na kasniju adresu - putJmp(0) + fixup(label)
	
	/*goto:
	 * if(labels.containsKey(ss_goto.getI1())
	 *   Code.putJump(labels.get(ss_goto.getI1())); -> vracanje unazad
	 * else {
	 *   Code.putJump(0); => treba nam pocetak ofseta
	 *   				// sada smo jmp | 0 | 0 | x <- OVDE
	 *   								*****
	*	int patchAdr = Code.pc - 2;
	*	List<Integer> l;
	*	MORAMO ZAPAMTITI SVE TE ADRESE KOJE TREBA DA POPRAVIMO
	*
	*	if(patchAdrMap.containsKey(ss_goto.getI1())  DA LI JE PRE NEKO VEC HTEO DA SKOCI
	*		l = patchAdrsMap.get(ss_goto.getI1()); => DOHVATI LISTU I DODAJ FIXUP
	*	else {
	*		l = new ArrayList<>(); // NIKO NIJE RANIJE HTEO DA SKOCI
	*		patchAdrsMap.put(ss_goto.getI1(), l);
	*   }
	*   
	*   l.add(patchAdr)
	*  }
	 */
	
	@Override
	public void visit(Label l) {
		labels.put(l.getI1(), Code.pc); //key:label_name val:curr_pc
	
//		if(pathsAdrsMap.containsKey(l.getI1())) {  POPUNI FIXUP ADRESE DOKLE GOD TIH ADRESA IMA
//			while(!patchAdrsMap.get(l.getI1()).isEmpty()) {
//				Code.fixup(patchAdrsMap.get(l.getI1().remove(0)));
//			}
//		}
	
	}
	
	
	
	/* ---- CONDITION ---- */
	
	private Stack<Integer> skipCondFact = new Stack<Integer>();
	private Stack<Integer> skipCondition = new Stack<Integer>();
	private Stack<Integer> skipThen = new Stack<Integer>();; //NITI KOJE NISU USPELE DA ISPUNE CONDITION IDU POSLE IF - DALJI KOD ILI U ELSE AKO POSTOJI
	private Stack<Integer> skipElse = new Stack<Integer>();;
	
	private int retRelop(Relop relop) {
		if(relop instanceof Eq) {
			return Code.eq;
		} else if(relop instanceof Noteq) {
			return Code.ne;
		} else if(relop instanceof Grt) {
			return Code.gt;
		} else if(relop instanceof Grteq) {
			return Code.ge;
		} else if(relop instanceof Lss) {
			return Code.lt;
		} else if(relop instanceof Lsseq) {
			return Code.le;
		} else {
			return -1;
		}
		
	}
	
	@Override
	public void visit(CondFact_expr cf_expr) { // samo jedna stvar na steku, a za uslov 2 je neoph
		Code.loadConst(0);
		Code.putFalseJump(Code.ne, 0); // AKO JE IZRAZ NETACAN/FALSE HOCEMO DA ISKOCIMO ~ POSTAVLJAMO NA JEDNAKO
		// if(a==0) else->a!=0
		skipCondFact.push(Code.pc-2); // stavljamo pocetak skoka
		
		//tacne
	
	}
	
	@Override
	public void visit(CondFact_expr_rel_expr cf_e_rel_e) {
		// IMAMO VEC DVA OPERANDA NA STEKU
		
		Code.putFalseJump(retRelop(cf_e_rel_e.getRelop()), 0);
		skipCondFact.push(Code.pc - 2);
		
		//tacne
	}
	
	// AKO NIJE IZBACEN NIJEDAN CONDFACT, ONDA JE STIGLA NIT DO CONDTERM
	// I AKO JE U CONDTERM ZNACI DA JE JEDAN AND IZRAZ TRUE U NIZU OR IZRAZA
	// TE CE CEO NAS IZRAZ BITI TRUE
	
	// UVEK MORAJU TACNE DA SE IZBCE PRVO, PA ONDA NETACNE DA SE UBACE, JER CE ONDA OBE DA SE IZBACE ISTOVREMENO
	
	@Override
	public void visit(CondTerm ct) { // u isto vreme kraj jednog OR i pocetak sledeceg
		//tacne - moraju prvo da se izbace
		Code.putJump(0); 
		skipCondition.push(Code.pc - 2); // MORAJU DA SE VRATE KAD POCNE THEN
		
		//vracam netacne; ispod je sl OR gde mogu biti tacne
		while(!skipCondFact.empty()) {
			Code.fixup(skipCondFact.pop());
		}
		
		//netacne -> na pocetak sl OR
		
	}
	
	
	/* PUSTA TACNE NITI DA SE IZVRSAVAJU, DOK NETACNE DRZI U SKIPTHEN SKOKU*/
	@Override
	public void visit(Condition cond) {
		//netacne 
		
		Code.putJump(0); // ELSE - JEDAN SKOK; barem jedan AND je bio netacan za sve OR
		skipThen.push(Code.pc - 2); // JEDAN SKOK JER JE SAMO JEDAN CONDITION, DOK CONDTERM I CONDFACT MOZE BITI VISE
		//fixup^ u IF
		
		//THEN ~ barem jedan OR je true/svi AND barem jednog OR su true
		while(!skipCondition.empty()) {
			Code.fixup(skipCondition.pop());
		}
		
		//tacne
	
	}
	
	/* AKO ELSE NE POSTOJI - TACNE NITI NASTAVITI SAMO; INC IH SALJEMO NA ELSE*/
	
	@Override
	public void visit(ElseStatement_no else_no) {
		//tacne
		Code.fixup(skipThen.pop());
		
		//tacne+netacne=>
	}
	
	@Override
	public void visit(Else else_) {
		//tacne
		Code.putJump(0); //TACNE BACAMO NA KRAJ ELSE
		skipElse.push(Code.pc - 2);
		Code.fixup(skipThen.pop());
		//netacne
	}
	
	@Override
	public void visit(ElseStatement_yes else_yes) {
		//netacne
		Code.fixup(skipElse.pop()); //VRACAMO TACNE KOJE SU PRESKOCILE ELSE
		//tacne+netacne=>
		
	}
	
	/* --- DOWHILE --- */
	
	private Stack<Integer> doBegin = new Stack<Integer>(); // jer dowhile mogu da se ugnjezdavaju
	
	@Override
	public void visit(DoNonTerm do_nt) {
		doBegin.push(Code.pc);
		breakHop.push(new ArrayList<Integer>());
		continueHop.push(new ArrayList<Integer>());
	
	}
	
	
	//ConditionList_no => bezuslovno vracamo na pocetak dowhile
	
	@Override
	public void visit(SingleStatement_dowhile_cond ss_dowhile) {
		Code.putJump(doBegin.pop()); // IZBACUJEM TACNE VRACANJEM NA POCETAK PETLJE
		Code.fixup(skipThen.pop()); // IZBACIVANJE NETACNIH POSLE PETLJE
		
		while(!breakHop.peek().isEmpty()) {
			Code.fixup(breakHop.peek().remove(0));
		}
		breakHop.pop();
		
		
//		if(ss_dowhile.getConditionList() instanceof ConditionList_yes) {
//			Code.putJump(doBegin.pop());
//			Code.fixup(skipThen.pop());
//		} else if(ss_dowhile.getConditionList() instanceof ConditionList_no) {
//			Code.putJump(doBegin.pop());
//		} else { //instanceof ConditionList_desg_stmt
//			Code.putJump(doBegin.pop());
//			Code.fixup(skipThen.pop());
//		}
	}
	
	@Override
	public void visit(SingleStatement_dowhile_cond_desStmt ss_cond_dsrStmt) {
		Code.putJump(doBegin.pop()); // IZBACUJEM TACNE VRACANJEM NA POCETAK PETLJE
		
		Code.fixup(skipThen.pop()); // IZBACIVANJE NETACNIH POSLE PETLJE
		
		
		while(!breakHop.peek().isEmpty()) {
			Code.fixup(breakHop.peek().remove(0));
		}
		breakHop.pop();
		
		
		
	}
	
	@Override
	public void visit(SingleStatement_dowhile_nocond ss_nocond) {
		Code.putJump(doBegin.pop()); // IZBACUJEM TACNE VRACANJEM NA POCETAK PETLJE
		//Code.fixup(skipThen.pop()); // IZBACIVANJE NETACNIH POSLE PETLJE
		
		while(!breakHop.peek().isEmpty()) {
			Code.fixup(breakHop.peek().remove(0));
		}
		breakHop.pop();
		
	}
	
	// break -> lista break-ova koje fixup-emo kada znamo gde se petlja zavrsava
	// => ONDA KADA PUSTAMO TACNE NAZAD IZ CONDITION, MI NAKON TOGA FIXUP ONE NETACNE I TADA MOZEMO I BREAK DA FIXUP
	
	// continue -> fixup pre nego sto pocne condition; kada se obidje while znamo da je tu adresa sa koje treba da se vratimo
	//		=> ne moze unutar statement jer tu se nalazi ti continue-i 
	
	//STEK listi ZA SVAKU OD PETLJI ZA BREAK I CONTINUE

	private Stack<List<Integer>> breakHop = new Stack<>();
	private Stack<List<Integer>> continueHop = new Stack<>();

	@Override
	public void visit(SingleStatement_break ss_break) {
		Code.putJump(0); // KADA SE DESI BREAK TREBA DA SE DESI SKOK NA ADRESU KOJU FIXUP
		breakHop.peek().add(Code.pc-2); // U LISTU UBACI TR ADRESU SKOKA KOJA CE SE ISKORISTI KASNIJE ZA FIXUP
	}
	
	@Override
	public void visit(SingleStatement_continue ss_continue) {
		Code.putJump(0);
		continueHop.peek().add(Code.pc-2);
	}
	
	@Override
	public void visit(WhileNonTerm whileNT) {
		
		while(!continueHop.peek().isEmpty()) {
			Code.fixup(continueHop.peek().remove(0));
		}
		continueHop.pop();
	}
	
	private Stack<Integer> whileBegin = new Stack<>();
	private Stack<List<Integer>> breakHopWhile = new Stack<>();
	private Stack<List<Integer>> continueHopWhile = new Stack<>();
	
	
	@Override
	public void visit(BeforeWhile before) {
		whileBegin.push(Code.pc);
		
		if(!continueHopWhile.isEmpty()) {
			while(!continueHopWhile.peek().isEmpty()) {
				Code.fixup(continueHopWhile.peek().remove(0));
			}
			continueHopWhile.pop();
		}
		breakHopWhile.push(new ArrayList<Integer>());
		continueHopWhile.push(new ArrayList<Integer>());
	}
	
	@Override
	public void visit(SingleStatement_while ss_while) {
		Code.putJump(whileBegin.pop()); // IZBACUJEM TACNE VRACANJEM NA POCETAK PETLJE
		
		Code.fixup(skipThen.pop()); // IZBACIVANJE NETACNIH POSLE PETLJE
		
		
		while(!breakHopWhile.peek().isEmpty()) {
			Code.fixup(breakHopWhile.peek().remove(0));
		}
		breakHopWhile.pop();
		
	}
	
	
	private Stack<Integer> forBegin = new Stack<>();
	private Stack<List<Integer>> breakHopFor = new Stack<>();
	private Stack<List<Integer>> continueHopFor = new Stack<>();

	

	

	
	@Override
	public void visit(For f) {
		breakHopFor.push(new ArrayList<Integer>());
		continueHopFor.push(new ArrayList<Integer>());
	}
	
	
	@Override
	public void visit(BeforeForCond b) {
		forBegin.push(Code.pc);
		
		if(!continueHopFor.isEmpty()) {
			while(!continueHopFor.peek().isEmpty()) {
				Code.fixup(continueHopFor.peek().remove(0));
			}
			continueHopFor.pop();
		}
	}
	
	
	
	
	@Override
	public void visit(SingleStatement_for ss_for) {
		Code.putJump(forBegin.pop()); // IZBACUJEM TACNE VRACANJEM NA POCETAK PETLJE
		
		Code.fixup(skipThen.pop()); // IZBACIVANJE NETACNIH POSLE PETLJE
		
		
		while(!breakHopFor.peek().isEmpty()) {
			Code.fixup(breakHopFor.peek().remove(0));
		}
		breakHopFor.pop();
	}
	
	
	
	// -> before neterminal za foreach za continue i foreach begin
	// -> odmah pred RIGHTPAREN neterminal u okviru kojeg se proverava redni broj elementa
	//    ako je kraj niza putFalseJmp(uslov, 0) - ovo ce se fixup-ti sa obilaskom foreach cvora; da li skipThen dodati nesto?
	//	  ako nije kraj store elementa od niza desnog dsg2 u var levo dsg1
	// -> foreach petlja ce odratiti za break sve, a pre putJump na foreachBegin i fixup za skipThen
	
	//"for" *** "(" *** Designator ":" Designator ")" *** Statement
	
	
	@Override
	public void visit(Designator_var d) {
		if(d.obj.getFpPos()==2) {
			finalFlagAssign = true;
		}
	}
	
	@Override
	public void visit(Designator_elem d) {
		if(d.getDesignatorArrName().obj.getFpPos()==2) {
			finalFlagElem = true;
		}
	}
	
	
	
//	@Override
//	public void visit(FactorMList_monkey m) {
//		
//	}
	
	/*
	 * a b
	 * a b a b
	 * a b a
	 * a b na
	 * a b na b
	 * a b na nb
	 * a b na nb na nb
	 * jle na<=nb arra
	 * 
	 * a b na nb
	 * a b nb 1
	 * jmp goB
	 * 
	 * arra:
	 * a b na nb
	 * a b na 0
	 * 
	 * goB:
	 * a b na/nb 0/1
	 * a b na/nb 0/1 1
	 * 
	 * jeq 0/1 == 1 b:
	 * 
	 * a b na
	 * a na b na
	 * a b na b
	 * a b na nb
	 * a b na res
	 * a b res
	 * 
	 * a res b res
	 * a res b
	 * 
	 * 
	 * 
	 * 
	 * */
	
	
	
	
//	@Override
//	public void visit(FactorLow_monkey m) {
//		
//		
//		Code.load(m.getDesignator().obj); //a
//		Code.put(Code.arraylength);
//		Code.load(m.getDesignator1().obj); //b
//		Code.put(Code.arraylength);
//		Code.put(Code.dup2);
//		
//		Code.putFalseJump(Code.gt, 0);
//		int arra = Code.pc - 2;
//		
//		Code.put(Code.dup_x1); 
//		Code.put(Code.pop);
//		Code.put(Code.pop);
//		Code.loadConst(1);
//		
//		Code.putJump(0);
//		int go_with_nb = Code.pc - 2;
//		
//		Code.fixup(arra);
//		
//		Code.put(Code.pop);
//		Code.loadConst(0);
//		
//		Code.fixup(go_with_nb);
//		
//		Code.loadConst(1);
//		Code.putFalseJump(Code.ne, 0);
//		int b = Code.pc-2;
//		//a niz je manji
//		Code.load(m.getDesignator1().obj);
//		Code.put(Code.arraylength);
//		Code.put(Code.newarray);
//		Code.loadConst(1);
//		Code.put(Code.dup_x1);
//		Code.put(Code.pop);
//		Code.put(Code.pop);
//		Code.loadConst(0);
//		
//		int backA1 = Code.pc;
//		
//		Code.load(m.getDesignator().obj);
//		Code.put(Code.arraylength);
//		Code.put(Code.dup2);
//		
//		Code.putFalseJump(Code.lt, 0);
//		int doneA = Code.pc - 2;
//		
//		Code.put(Code.pop);
//		Code.put(Code.dup2);
//		Code.load(m.getDesignator().obj);
//		Code.put(Code.dup_x1); Code.put(Code.pop);
//		Code.put(Code.dup_x1);
//		Code.put(Code.aload);
//		Code.load(m.getDesignator1().obj);
//		Code.put(Code.dup_x2); Code.put(Code.pop);
//		Code.put(Code.dup_x2); Code.put(Code.pop);
//		Code.put(Code.dup_x2);
//		Code.put(Code.aload);
//		Code.put(Code.add);
//		Code.put(Code.astore);
//		Code.loadConst(1);
//		Code.put(Code.add);
//		
//		Code.putJump(backA1);
//		Code.fixup(doneA);
//		
//		Code.put(Code.pop);
//		
//		int backA2 = Code.pc;
//		
//		Code.load(m.getDesignator1().obj);
//		Code.put(Code.arraylength);
//		Code.put(Code.dup2);
//		
//		Code.putFalseJump(Code.lt, 0);
//		int done1 = Code.pc - 2;
//		
//		Code.put(Code.pop);
//		Code.put(Code.dup2);
//		Code.load(m.getDesignator1().obj);
//		Code.put(Code.dup_x1); Code.put(Code.pop);
//		Code.put(Code.dup_x1);
//		Code.put(Code.aload);
//		Code.put(Code.astore);
//		Code.loadConst(1);
//		Code.put(Code.add);
//		
//		Code.putJump(backA2);
//		
//		//----------------------
//		
//		Code.fixup(b);
//		//b niz je manji
//		
//		Code.load(m.getDesignator().obj);
//		Code.put(Code.arraylength);
//		Code.put(Code.newarray);
//		Code.loadConst(1);
//		Code.put(Code.dup_x1);
//		Code.put(Code.pop);
//		Code.put(Code.pop);
//		Code.loadConst(0);
//		
//		int backB1 = Code.pc;
//		
//		Code.load(m.getDesignator1().obj);
//		Code.put(Code.arraylength);
//		Code.put(Code.dup2);
//		
//		Code.putFalseJump(Code.lt, 0);
//		int doneB = Code.pc - 2;
//		
//		Code.put(Code.pop);
//		Code.put(Code.dup2);
//		Code.load(m.getDesignator().obj);
//		Code.put(Code.dup_x1); Code.put(Code.pop);
//		Code.put(Code.dup_x1);
//		Code.put(Code.aload);
//		Code.load(m.getDesignator1().obj);
//		Code.put(Code.dup_x2); Code.put(Code.pop);
//		Code.put(Code.dup_x2); Code.put(Code.pop);
//		Code.put(Code.dup_x2);
//		Code.put(Code.aload);
//		Code.put(Code.add);
//		Code.put(Code.astore);
//		Code.loadConst(1);
//		Code.put(Code.add);
//		
//		Code.putJump(backB1);
//		Code.fixup(doneB);
//		
//		Code.put(Code.pop);
//		
//		int backB2 = Code.pc;
//		
//		Code.load(m.getDesignator().obj);
//		Code.put(Code.arraylength);
//		Code.put(Code.dup2);
//		
//		Code.putFalseJump(Code.lt, 0);
//		int done2 = Code.pc - 2;
//		
//		Code.put(Code.pop);
//		Code.put(Code.dup2);
//		Code.load(m.getDesignator().obj);
//		Code.put(Code.dup_x1); Code.put(Code.pop);
//		Code.put(Code.dup_x1);
//		Code.put(Code.aload);
//		Code.put(Code.astore);
//		Code.loadConst(1);
//		Code.put(Code.add);
//		
//		Code.putJump(backB2);
//		
//		Code.fixup(done1);
//		Code.fixup(done2);
//		
//		Code.put(Code.pop);
//		Code.put(Code.pop);
//		
//	}
	
	/*
	 * na nb
	 * na nb na nb
	 * jge na<=nb arra
	 * 
	 * na nb
	 * nb na nb
	 * nb 1
	 * jmp go_with_nb
	 * 
	 * arra:
	 * na nb
	 * na 0
	 * 
	 * go_with_nb:
	 * na/nb 0/1
	 * na/nb 0/1 1
	 * 
	 * jeq 0/1 == 1 b
	 * 
	 * NA JE MANJE:
	 * 
	 * na
	 * na b
	 * na nb
	 * na res
	 * res na res
	 * res
	 *  
	 * backA1:
	 * 
	 * res 0
	 * res 0 a
	 * res 0 na
	 * res 0 na 0 na
	 * jge 0>=na doneA
	 * 
	 * res 0 na
	 * res 0 res 0
	 * res 0 res 0 a
	 * res 0 res a 0 a
	 * res 0 res a 0
	 * res 0 res 0 a 0 
	 * res 0 res 0 a[0]
	 * res 0 res 0 a[0] b
	 * res 0 res b 0 a[0]
	 * res 0 res a[0] b 0 
	 * res 0 res 0 a[0] b 0
	 * res 0 res 0 a[0]+b[0]
	 * res 0
	 * res 1
	 * jmp backA1
	 * doneA:
	 * res na na
	 * 
	 * backA2:
	 * res na
	 * res na b
	 * res na nb
	 * res na nb na nb
	 * jge na>=nb done
	 * res na nb
	 * res na 
	 * res na res na b
	 * res na res b na b
	 * res na res b na
	 * res na res na b na
	 * res na res na b[na]
	 * res na
	 * res na+1
	 * jmp backA2
	 * 
	 * 
	 * b:
	 * nb
	 * nb a
	 * nb na
	 * nb res
	 * res nb res
	 * res nb
	 * res
	 * 
	 * backB1:
	 * res 0
	 * res 0 b
	 * res 0 nb
	 * res 0 nb 0 nb
	 * jge 0>=nb doneB
	 * 
	 * res 0 nb
	 * res 0 res 0
	 * res 0 res 0 a
	 * res 0 res a 0 a
	 * res 0 res a 0
	 * res 0 res 0 a 0 
	 * res 0 res 0 a[0]
	 * res 0 res 0 a[0] b
	 * res 0 res b 0 a[0]
	 * res 0 res a[0] b 0 
	 * res 0 res 0 a[0] b 0
	 * res 0 res 0 a[0]+b[0]
	 * res 0
	 * res 1
	 * jmp backB1
	 * 
	 * doneB:
	 * res nb nb
	 * 
	 * backB2:
	 * res nb
	 * res nb a
	 * res nb na
	 * res nb na nb na
	 * jge nb>=na done
	 * res nb na
	 * res nb 
	 * res nb res nb a
	 * res nb res a nb a
	 * res nb res a nb
	 * res nb res nb a nb
	 * res nb res nb a[nb]
	 * res nb
	 * res nb+1
	 * jmp backB2
	 * 
	 * done:
	 * res na/nb nb/na
	 * res
	 * 
	 * */
	
//	@Override
//	public void visit(Final_f f) {
//		finalFlag = true;
//	}
//	
//	@Override
//	public void visit(VarDeclList v) {
//		if(v.getFinal() instanceof Final_f) finalFlag = false;
//	}
//	
}

