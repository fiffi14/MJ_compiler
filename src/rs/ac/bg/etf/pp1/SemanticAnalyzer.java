package rs.ac.bg.etf.pp1;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;

import org.apache.log4j.Logger;

import rs.ac.bg.etf.pp1.ast.*;
import rs.etf.pp1.symboltable.Tab;
import rs.etf.pp1.symboltable.concepts.Obj;
import rs.etf.pp1.symboltable.concepts.Struct;

public class SemanticAnalyzer extends VisitorAdaptor {
	
	private boolean errorDetected = false;
	
	Logger log = Logger.getLogger(getClass());

	private Obj currentProg;
	private Struct currentType;
	private int constant; //32b
	private Struct constantType;
	private Struct boolType = Tab.find("bool").getType();  /* SIG CE SE POSTOJATI JER CE TAB SIM BITI INIC PRE CELE 3. FAZE*/
	private Struct setType = Tab.find("set").getType();
	private Obj mainMethod;
	private Obj currentMethod;
	private boolean returnExists;
	private int loopCnt = 0; // broj petlji do-while
	private boolean finalFleg = false;
	
	private HashSet<String> setOfLabels = null;

	int nVars;

	private Obj currentTypeObj;
	
	//private boolean finalFlag = false;
	
	
	// LOGS
	public void report_error(String message, SyntaxNode info) {
		errorDetected = true;
		StringBuilder msg = new StringBuilder(message);
		int line = (info == null) ? 0: info.getLine();
		if (line!=0)
			msg.append(" na liniji ").append(line);
		log.error(msg.toString());
		
	}
	
	public void report_info(String message, SyntaxNode info) {
		StringBuilder msg = new StringBuilder(message);
		int line = (info == null) ? 0: info.getLine();
		if (line!=0)
			msg.append(" na liniji ").append(line);
		log.info(msg.toString());
		
	}
	
	public boolean passed() {
		return !errorDetected; // true - desila se greska
	}
	
	/* SEMANTIC PASS CODE */
	
	// NIKADA NE REDEFINISI ZA APS KLASE, NPR. NIKADA ZA ConVarDeclList, VEC SAMO ZA IZVEDENE I DODAVATI ANOTACIJU
	
	// PROVERITI KONTEKSNE USLOVE; UNIVERSE I GLOB SU DONEKLE ISTI OPSEZI, A GLOB I LOK NISU
	
	@Override
	public void visit(ProgramName programName) {
		currentProg = Tab.insert(Obj.Prog, programName.getI1(), Tab.noType); //void/null za Struct
		Tab.openScope(); 													// MORAMO ZATVORITI JER MORAMO IZVRSITI PRELANCAVANJE GLOB PROM-IH
	}
	
	@Override
	public void visit(Program program) {
		
		this.nVars = Tab.currentScope().getnVars();
		
		Tab.chainLocalSymbols(currentProg);
		Tab.closeScope(); // ZNAMO DA JE OSTAO SAMO GLOB SCOPE
		currentProg = null;
		
		if(mainMethod == null || mainMethod.getLevel()>0) { // da li se postavio main
			report_error("Nije definisana adekvatna main metoda", program);
		}
	
		
		//report_info("Hello program", program);
		//Tab.chainLocalSymbols(Tab.find(null)); //u koji Obj cvor? => Obj.Prog
						/* MORA SE TRAZITI PO USLOVU DA BUDE TRAZENOG NAME I DA JE KIND Prog, JER OBICNA VAR MOZE BITI ISTOG IMENA*/
		
	
	}
	
	@Override
	public void visit(Type type) { // NESTO STO JE VEC DEFINISANO (INT,CHAR..)
		/*AKO JE NEKI TIP RECORD/CLASS ONDA TAJ TIP MORA BITI DEF PRE DEKL PROM */
		
		Obj typeObj = Tab.find(type.getI1()); // ***PRETRAGA NA OSNOVU IMENA PO CITAVOJ TAB SIMBOLA
		
		if(typeObj == Tab.noObj) { 									/* AKO SAMO IME TOG TIPA NIJE PRONADJENO U UNIVERSE TAB */
			report_error("Nepostojeci tip podatka: [Type]" + type.getI1(), type);
			type.struct = currentType = Tab.noType;
		}
		else if(typeObj.getKind() != Obj.Type) {					 /* AKO JE PRONADJENO NESTO STO ODGOVARA IMENU TIPA ALI JE NEKI DRUGI OBJ CVOR */
			report_error("Neadekvatan tip podatka: [Type]" + type.getI1(), type);
			type.struct = currentType = Tab.noType;
		}
		else {
			type.struct = currentType = typeObj.getType();	
			currentTypeObj = typeObj;
			//report_info("***** Type " + currentTypeObj.getName(), type);
		}
		
		
	}
	

	
	/* ------------------- CONSTs ------------------- */
	
	/* provera tipova pri dodeli */
	
	@Override
	public void visit(Constant_num constant_num) {
		constant = constant_num.getN1();
		constantType = Tab.intType;
	}
	
	@Override
	public void visit(Constant_char c_char) {
		constant = c_char.getC1();
		constantType = Tab.charType;
	}
	
	@Override
	public void visit(Constant_bool c_bool) {
		constant = c_bool.getB1();
		/* NE POSTOJI STAT BOOL POKAZIVAC NA STRUCT/OBJ CVOR */
		constantType = boolType;
	}
	
	@Override
	public void visit(ConstDecl constDecl) { /* NIKAKO PRISTUPATI PARENT KLASI KOJA JE NEKAKVA REKURZIJA, 
												DOZVOLJENO JE ZA ONE SMENE GDE TOGA NEMA (1 ILI 2 STEPENA NA GORE U STABLU) */
		// => ISKORISTITI VISIT-E !!!!
		// TYPE SE OBILAZI PRE BILO KOG ConstDecl tkd MOZEMO GA SACUVATI NEGDE I ISKORISTITI POSLE
		
		Obj constObj = Tab.find(constDecl.getI1());
		
		if(constObj != Tab.noObj) { 												//takva konst postoji
			report_error("Visetruka definicija konstante: [constDecl]" + constDecl.getI1(), constDecl);
		} else {																	// ne postoji, stavi je u tab
			
			if(constantType.assignableTo(currentType)) {                        // desni operand/src/currentType je istog tipa kao i levi operand/dest/currentType
				constObj = Tab.insert(Obj.Con, constDecl.getI1(), currentType);
				constObj.setAdr(constant); 
				report_info("Accessing CONST " + constObj.getName() + " ObjInfo: " + constObj.getKind() + ", " + constObj.getType().getKind() + ", " + constObj.getAdr() + ", " + constObj.getLevel() + ";", constDecl);
			} else {
				report_error("Neadekvatna dodela konstanti: [constDecl]" + constDecl.getI1(), constDecl);
			}
			
													
		}
		
	  //prom je tipa Type sto je neki IDENT
		/* ZA CONST U ADR IDE VR STO MORAMO MI DA DOPISEMO*/
	
		
	}
	
	
	/* ------------------- VARs ------------------- */
	
	@Override
	public void visit(VarDeclList v) {
		if(v.getFinal() instanceof Final_f) finalFleg = false;
	}
	
	@Override
	public void visit(VarDecl_var varDecl_var) {
		Obj varObj = null;
								//Tab.currentScope().findSymbol(null); // VRACA NULL AKO SIMBOLA NEMA U TRNT SCOPE-U
		
		if(currentMethod == null) { // U GLOB SCOPE SMO
			varObj = Tab.find(varDecl_var.getI1());
			//report_info("Accessing Global VAR " + varObj.getName() + " ObjInfo: " + varObj.getKind() + ", " + varObj.getType().getKind() + ", " + varObj.getAdr() + ", " + varObj.getLevel() + ";", varDecl_var);
			
		} else { // LOCAL SCOPE
			varObj = Tab.currentScope().findSymbol(varDecl_var.getI1());
			
		}
		
		
		if(varObj == Tab.noObj || varObj == null) { // AKO VEC POSTOJI TAKAV SIMBOL ILI AKO SU PRETRAGE IZNAD NASLE U TEKUCIM OPSEZIMA ISTI SIMBOL, odnosno nisu
			//nema dodele vrednosti kod dekl Var
			varObj = Tab.insert(Obj.Var, varDecl_var.getI1(), currentType);
			
//			if(finalFleg) {
//				varObj.setFpPos(2);
//			}
			report_info("Accessing VAR " + varObj.getName() + " ObjInfo: " + varObj.getKind() + ", " + varObj.getType().getKind() + ", " + varObj.getAdr() + ", " + varObj.getLevel() + ";", varDecl_var);
			
			// OVDE DODATI IF CURRENTCLASS == NULL -> DODAJ VAR U TAB; ELSE -> KREIRAJ OBJ.FLD I LEVEL=2
		} else {
			report_error("Visestruka definicija promenljive: [VarDecl_var]" + varDecl_var.getI1(), varDecl_var);
			
		}
	}
	
	@Override
	public void visit(VarDecl_arr varDecl_arr) {
		Obj arrObj = null;
		
		if(currentMethod == null) { // GLOB SCOPE
			arrObj = Tab.find(varDecl_arr.getI1());
		} else { // LOCAL SCOPE
			arrObj = Tab.currentScope().findSymbol(varDecl_arr.getI1());
		}
		
		if(arrObj == Tab.noObj || arrObj == null) { 
			
			arrObj = Tab.insert(Obj.Var, varDecl_arr.getI1(), new Struct(Struct.Array, currentType));
			
			if(finalFleg) {
				arrObj.setFpPos(2);
				report_info(arrObj.getName() + ": FpPos-> "+arrObj.getFpPos(), varDecl_arr);
			}
			
			report_info("Accessing VAR of Array " + arrObj.getName() + " ObjInfo: " + arrObj.getKind() + ", " + arrObj.getType().getKind() + ", " + arrObj.getAdr() + ", " + arrObj.getLevel() + ";", varDecl_arr);	
			/*       *tipa Var*                ***tipa Struct za Nizove a onda u okv tipa refc u Elem type na int***   */

		} else {
			report_error("Visestruka definicija promenljive (niz): [VarDecl_arr]" + varDecl_arr.getI1(), varDecl_arr);
		}
	}

	
	
//	if(currentRefType==null) { **ZA KLASE
	
//		arrObj = Tab.insert(Obj.Var, varDecl_arr.getI1(), new Struct(Struct.Array, currentType));
//		/*       *tipa Var*                ***tipa Struct za Nizove a onda u okv tipa refc u Elem type na int***   */
//	
//	} else {
//		arrObj = Tab.insert(Obj.Fld, varDecl_arr.getI1(), new Struct(Struct.Array, currentType));
//		arrObj.setLevel(2);
//	}
	
	
	/* ------------------- METHODs ------------------- */
	
	// !!! napravili smo posebnu smenu za naziv i povr tip metode da bismo mogli da otvorimo odnosno zatvorimo nas scope
	
	/* povratni tip sa return se moze potvrditi sa vremenom prevodjenja, a ne za vreme izvrsavanja
	 * jer mikroJava mora biti spremna i form se na osnovu trece faze
	 *  */
	
	@Override
	public void visit(MethodRetnName_void methodRetnName_void) {
		
		currentMethod = Tab.insert(Obj.Meth, methodRetnName_void.getI1(), Tab.noType);
		methodRetnName_void.obj = currentMethod;
		Tab.openScope();
		
		if(methodRetnName_void.getI1().equalsIgnoreCase("main")) {  // NE BUDI SENZITIVAN NA MALA I VELIKA SLOVA => MaIn je prihvatljivo
			mainMethod = currentMethod;
		}
		

		setOfLabels = new HashSet<>();
	}
	
	@Override
	public void visit(MethodRetnName_anytype methodRetnName_anytype) {
		// ograniciti ime fja da se odvoji od imena prom ??
		
		currentMethod = Tab.insert(Obj.Meth, methodRetnName_anytype.getI2(), currentType);
		methodRetnName_anytype.obj = currentMethod;
		Tab.openScope();
		
		setOfLabels = new HashSet<>();
	}
	
	@Override
	public void visit(MethodDecl methodDecl) {
		Tab.chainLocalSymbols(currentMethod);
		Tab.closeScope();
		
		// PROVERE **ev za !setOfLabels.containsAll(setOfGotos) => err
		if(currentMethod.getType() != Tab.noType && !returnExists) {
			report_error("Ne postoji return unutar non-void metode [MethodDecl].", methodDecl);
		}
		
		currentMethod = null;
		returnExists = false;
	
		setOfLabels = null;
	}
	
	/* ------------------- FORMAL PARMs ------------------- */
	//Level kod Meth inkr za broj parm
	//za Var/Formalne parm FpPos upisati 1
	
	@Override
	public void visit(FormPars_var formPars_var) {
		Obj formVar = null;
		//uvek cemo se naci u nekoj metodi
		
		if(currentMethod == null) { // GLOB
			report_error("Semanticka greska - formalni parametri se ne mogu naci u globalnom opsegu. [FormPars_var]", formPars_var);
		} else {
			formVar = Tab.currentScope().findSymbol(formPars_var.getI2());  /*getI2 je a ne 1 jer imamo Type pre ovoga, te je ovo IDENT 2. po redu*/
			
		}
		
		if(formVar==null || formVar == Tab.noObj) {
			formVar = Tab.insert(Obj.Var, formPars_var.getI2(), currentType);
			formVar.setFpPos(1);
			currentMethod.setLevel(currentMethod.getLevel() + 1); /*******/
			
			report_info("Accessing FORMAL PARM " + formVar.getName() + " ObjInfo: " + formVar.getKind() + ", " + formVar.getType().getKind() + ", " + formVar.getAdr() + ", " + formVar.getLevel() + ";", formPars_var);	
			
			
		} else {
			report_error("Visestruka definicija formalnog parametra [FormPars_var]: " + formPars_var.getI2(), formPars_var);
		}
				
	}
	
	@Override
	public void visit(FormPars_arr formPars_arr) {
		Obj formArr = null;
		
		if(currentMethod==null) {
			report_error("Semanticka greska - formalni parametri se ne mogu naci u globalnom opsegu. [FormPars_arr]", formPars_arr);
		} else {
			formArr = Tab.currentScope().findSymbol(formPars_arr.getI2());
		}
		
		if(formArr == null || formArr == Tab.noObj) {
			formArr = Tab.insert(Obj.Var, formPars_arr.getI2(), new Struct(Struct.Array, currentType));
			formArr.setFpPos(1);
			currentMethod.setLevel(currentMethod.getLevel() + 1); /*******/
			
			report_info("Accessing FORMAL PARM " + formArr.getName() + " ObjInfo: " + formArr.getKind() + ", " + formArr.getType().getKind() + ", " + formArr.getAdr() + ", " + formArr.getLevel() + ";", formPars_arr);	
			
			
		} else {
			report_error("Visestruka definicija formalnog parametra tipa niz [FormPars_arr]]: " + formPars_arr.getI2(), formPars_arr);
		}
	}
	
	
	
//	@Override
//	public void visit(RecDeclName recDeclName) {
//		Obj recObj = Tab.find(recDeclName.getI1());
//		if(recObj != Tab.noObj) {
//			report_error("Dvostruka definicija rekorda: " + recDeclName.getI1(), recDeclName);
//		}
//		else {
//			currentRecord = new Struct(Struct.Class);
//			recObj = Tab.insert(Obj.Type, recDeclName.getI1(), currentRecord);
//			Tab.openScope();
//		}
//	}
//	
//	@Override
//	public void visit(RecDecl recDecl) {
//		Tab.chainLocalSymbols(currentRecord);
//		Tab.closeScope();
//		currentRecord = null;
//	}

	
	/* ------------------- KONTEKSNI USLOVI ------------------- */
	
	// ----- Designator -----
	@Override
	public void visit(Designator_var d_var) {
		// PRVO VAR TREBA DA SE PROVERI DA LI JE NEGDE DEF - LOK,GLOB ILI UNI
	
		Obj varObj = Tab.find(d_var.getI1());
		if(varObj==Tab.noObj) {
			report_error("Pristup nedefinisanoj promenljivoj: [Designator_var]" + d_var.getI1(), d_var);
			d_var.obj = Tab.noObj; // DA NAM NE BI PUKAO NULL POINTER EXCEPTION
			
		} else if(varObj.getKind() != Obj.Var && varObj.getKind() != Obj.Con && varObj.getKind() != Obj.Meth) {	
			// AKO NIJE I ELEM, ALI ON SE NE MOZE DOHVATITI
			
			report_error("Neadekvatan tip promeljive [designator_var]: " + d_var.getI1(), d_var);
			d_var.obj = Tab.noObj;
		} else {
			d_var.obj = varObj; // za sad: ako postoji takav simb u tab i prosledi ga na gore
			
			/* SAGLEDATI STA DESIGNATOR SVE MOZE DA BUDE
			 * FactorLow
			 * - Var, con, Meth (kao poziv mt, B nivo), Elem (**ne moze se naci u Tab**)
			 * - ne mogu: Type(int+int), Prog, Field (C)
			 * 
			 * DesignatorStatement
			 * - ne moze se naci konstanta jer ++ -- i nema dodele u konst
			 * 
			 * */
		}
	}
	
	@Override
	public void visit(DesignatorArrName dArrName) {
		
		Obj arrObj = Tab.find(dArrName.getI1());
		if(arrObj == Tab.noObj) {
			report_error("Pristup nedefinisanoj promenljivoj niza [DesignatorArrName]: " + dArrName.getI1(), dArrName);
			dArrName.obj = Tab.noObj;
		} else if(arrObj.getType().equals(setType)) {
			report_error("Nedozvoljeno indeksiranje reference tipa SET [Designator_elem]: " + dArrName.getI1(), dArrName);
		} else if(arrObj.getKind() != Obj.Var || arrObj.getType().getKind() != Struct.Array) {  // ako Obj cvor nije Var ili ako Struct nije Array, a sam tip elemenata je svj
			report_error("Neadekvatan tip promenljive niza [DesignatorArrName]: " + dArrName.getI1(), dArrName);
			dArrName.obj = Tab.noObj;
		} else {
			dArrName.obj = arrObj;
		}
		/*U DesignatorArrName cemo okaciti Obj cvor Niza,
		 *  a Designator_elem okaciti Obj.Elem koji cemo u tom tr napraviti
		 *  */
	}
	
	@Override
	public void visit(Designator_elem d_elem) { // prvo smo obisli DesignatorArrName i gledamo da li je bilo greske
		/* POTOMAK U STABLU JE VEC OBISAO TABELU I NEMA STA OVAJ DA SE BAVI SA ISTOM */
		
		Obj arrObj = d_elem.getDesignatorArrName().obj;
		
		if(arrObj == Tab.noObj) {
			d_elem.obj = Tab.noObj;
		} else if(!(d_elem.getExpr().struct.equals(Tab.intType))) {
			report_error("Indeksiranje se vrsi non-int elementom. [Designator_elem]", d_elem);
			d_elem.obj = Tab.noObj;
			
		} else { // postoji validan niz
			
			//Obj tmp = Tab.find(arrObj.getName()).get
			d_elem.obj = new Obj(Obj.Elem, arrObj.getName() + "[$]", arrObj.getType().getElemType());
			
			report_info("Accessing ELEM " + d_elem.obj.getName() + " ObjInfo: " + d_elem.obj.getKind() + ", " + d_elem.obj.getType().getKind() + ", " + d_elem.obj.getAdr() + ", " + d_elem.obj.getLevel() + ";", d_elem);
			//report_info("currentType "+currentType.getKind(), d_elem);
			
					/*   OBJ CVOR ELEM NIZA; NIZ[..] BICE DEF U RUNTIME; TIPA EELEMANATA NIZA U DEKL*/
			//report_info("Detektovan", d_elem);
				/**** JAKO JE BITNO DODATI NOVI CVOR U VIDU ELEMENTA NIZA ****/
		}
	}
	
	/*
	 * 
	 * a.b.c => rez tip je od c, JER AKO JA PRISTUPAM a.b.c KONACNO POLJE JE TO C I NJEN TIP TREBA DA SE POREDI U NEKOM IZRAZU
	 *
	 *
	 * a -> Designator
	 * .b.c -> DesignatorRecr..
	 * */

	
	// ----- Factor -> Expr -----
	
	// za factorlist, kod smene za factor nije potrebno nista spec, samo se prenese struct
	// ali za smenu factorlist mulop factor, mi znamo da ce factorlist biti sigurno obidjen, te mozemo koristiti za dalje provere bez prob
	
	@Override
	public void visit(Expr_map e_map) {
		//left je metoda sa 1 parm tipa int i povr vr int
		//right je obj.var struct.Array elemtype.int
		Obj left = e_map.getDesignator().obj;
		Obj right = e_map.getDesignator1().obj;
		
		ArrayList<Obj> tmp = new ArrayList<Obj>();
		for(Obj o: left.getLocalSymbols()) {
			tmp.add(o);
			//report_info("Form parm fju za map: " + o.getName(), e_map);
		}
		//report_info(right.getName() + " type: " + (right.getType().getKind() == Struct.Array ? "da" : "ne"), e_map);
		if((left.getKind()==Obj.Meth && tmp.get(0).getType()==Tab.intType && left.getType() == Tab.intType) && (right.getKind() == Obj.Var && right.getType().getKind() == Struct.Array && right.getType().getElemType() == Tab.intType)) {
			e_map.struct = Tab.intType;
		} else {
			report_error("Map operacija non-int vrednostima [Expr_map]", e_map);
			e_map.struct = Tab.noType;
		}
	}
	
	@Override
	public void visit(Expr_terms e_terms) {
		e_terms.struct = e_terms.getTermList().struct;
	}
	
	@Override
	public void visit(TermList_recr_addop tl_recr_addop) {
		Struct left = tl_recr_addop.getTermList().struct;
		Struct right = tl_recr_addop.getTerm().struct;
		
		if(left.equals(Tab.intType) && right.equals(Tab.intType)) {
			tl_recr_addop.struct = Tab.intType;
		} else {
			report_error("Addop operacija sa non-int vrednostima [TermList_recr_addop]", tl_recr_addop);
			tl_recr_addop.struct = Tab.noType;
		}
	}
	
	
	@Override
	public void visit(TermList_single tl_single) {
		tl_single.struct = tl_single.getTerm().struct;
	}
	
	@Override
	public void visit(Term term) {
		term.struct = term.getFactorList().struct;
	}
	
	
	@Override
	public void visit(FactorList_single flist_single) {
		flist_single.struct = flist_single.getFactor().struct;
	}
	
	@Override
	public void visit(FactorList_recr_mulop flist_recr_mulop) {
		Struct left = flist_recr_mulop.getFactorList().struct; //ovo polje je ovo iznad
		Struct right = flist_recr_mulop.getFactor().struct;
		
		if(left.equals(Tab.intType) && right.equals(Tab.intType)) {
			flist_recr_mulop.struct = Tab.intType;
		} else {
			report_error("Mulop operacija sa non-int vrednostima [FactorList_recr_mulop]", flist_recr_mulop);
			flist_recr_mulop.struct = Tab.noType;
		}
	}
	

	
	@Override
	public void visit(Factor_YesUnary factor_yesUnary) {
		if(factor_yesUnary.getFactorLow().struct.equals(Tab.intType)) {
			factor_yesUnary.struct = Tab.intType;
		} else {
			report_error("Negacija non-int vrednosti [Factor_YesUnary]", factor_yesUnary);
			factor_yesUnary.struct = Tab.noType;
		}
	}
	
	@Override
	public void visit(Factor_NoUnary factor_noUnary) {
		factor_noUnary.struct = factor_noUnary.getFactorLow().struct;
	}
	
	@Override
	public void visit(FactorLow_desg_e f_desg_e) {
		f_desg_e.struct = f_desg_e.getDesignator().obj.getType(); // obj.getType() -> struct konverzija
	}
	
	@Override
	public void visit(FactorLow_desg_hash flow_desg_hash) {
		if(flow_desg_hash.getDesignator().obj.getType().getKind() != Struct.Array && flow_desg_hash.getDesignator().obj.getType().getKind() != setType.getKind()) {
			report_error("Max vrednost na non-array/set promenljivom [FactorLow_desg_hash]: " + flow_desg_hash.getDesignator().obj.getName(), flow_desg_hash);
		} 
		if(flow_desg_hash.getDesignator().obj.getType().getKind() == Struct.Array && (!flow_desg_hash.getDesignator().obj.getType().getElemType().equals(Tab.intType) && !flow_desg_hash.getDesignator().obj.getType().getElemType().equals(Tab.charType))) {
			report_error("Max vrednost sa nizom non-int/char vrednostima [FactorLow_desg_hash]: " + flow_desg_hash.getDesignator().obj.getName(), flow_desg_hash);
		}
		
		if(flow_desg_hash.getDesignator().obj.getType().getKind() == Struct.Array)
			flow_desg_hash.struct = flow_desg_hash.getDesignator().obj.getType().getElemType();
		else
			flow_desg_hash.struct = Tab.intType;
	}
	
	
	@Override
	public void visit(FactorLow_desg_method_ActPars flow_method_actPars) {
		if(flow_method_actPars.getDesignator().obj.getKind() != Obj.Meth) {
			report_error("Poziv neadekvatne metode [FactorLow_desg_method_ActParsNo]: " + flow_method_actPars.getDesignator().obj.getName(), flow_method_actPars);
			flow_method_actPars.struct = Tab.noType;
		} else {
			flow_method_actPars.struct = flow_method_actPars.getDesignator().obj.getType();
			
			
			
			/** DA BI SE PROVERA ACTPARS PRENELA I NA UNGZ POZIVE METODA, JER BEZ TOGA SE PROVERAVAO SAMO SPOLJ POZIV **/
			
			
			List<Struct> fpList = new ArrayList<Struct>();
			for( Obj local: flow_method_actPars.getDesignator().obj.getLocalSymbols()) {
				//report_info(local.getName() + " " + local.getFpPos(), flow_method_actPars);
				if(local.getKind() == Obj.Var && local.getLevel() == 1 && local.getFpPos() == 1) {
					fpList.add(local.getType());
				}
			}
			
	
			ActParsCounter apc = new ActParsCounter(); // PODSTABLO ZA VISITE ACTPARS
			
			flow_method_actPars.getActParsList().traverseBottomUp(apc);
			
			List<Struct> apList = apc.finalActParsList;
			
			try {
				//report_info(flow_method_actPars.getDesignator().obj.getName() + " fpList size: " + fpList.size(), flow_method_actPars);
				//report_info(flow_method_actPars.getDesignator().obj.getName() + " apList size: " + apList.size(), flow_method_actPars);
				
				if(fpList.size() != apList.size()) {
					throw new Exception("Size error");
				}
				
				for (int i = 0; i < fpList.size(); i++) {
					Struct fps = fpList.get(i);
					Struct aps = apList.get(i);
					
					if(fps.getKind()==Struct.Enum && aps.getKind()==Struct.Enum) {
						continue;
					} else if(!aps.assignableTo(fps)) {
						throw new Exception("Type error");
					}
				}
				
			} catch (Exception e) {
				report_error("[" + e.getMessage() + "] " + "Parametri se ne poklapaju pri pozivu metode [FactorLow_desg_method_ActPars]: " + flow_method_actPars.getDesignator().obj.getName(), flow_method_actPars);
			}
			
			report_info("Method call " + flow_method_actPars.getDesignator().obj.getName() + " ObjInfo: " + flow_method_actPars.getDesignator().obj.getKind() + ", type: " + flow_method_actPars.getDesignator().obj.getType().getKind() + ", adr: " + flow_method_actPars.getDesignator().obj.getAdr() + ", level: " + flow_method_actPars.getDesignator().obj.getLevel() + ";", flow_method_actPars);
			
		}
	}
	
	@Override
	public void visit(FactorLow_num flow_num) {
		flow_num.struct = Tab.intType;
	}
	
	@Override
	public void visit(FactorLow_bool flow_bool) {
		flow_bool.struct = boolType;
	}
	
	@Override
	public void visit(FactorLow_char f_char) {
		f_char.struct = Tab.charType;
	}
	
	
	@Override
	public void visit(FactorLow_new_arr_expr flow_new_arr_expr) { //new int[5]
		
		if(!flow_new_arr_expr.getExpr().struct.equals(Tab.intType)) {
			report_error("Velicina niza nije int tipa [FactorLow_new_arr_expr]", flow_new_arr_expr);
			flow_new_arr_expr.struct = Tab.noType;
		} else {
			
			if(currentType.equals(setType) && currentTypeObj.getName()=="set") {
				//report_info("evo ga set", flow_new_arr_expr);
				flow_new_arr_expr.struct = new Struct(setType.getKind());//setType
				//flow_new_arr_expr.struct.setMembers(new HashTableDataStructure());
				
				//report_info("***** SETTTT ****** KIND: " + setType.getKind(), flow_new_arr_expr);
				
			} else {
				flow_new_arr_expr.struct = new Struct(Struct.Array, currentType); // da li je int[2] dodeljivo u a; a = new int[2]
																					// => EXPR CE ZA SEBE PROVERAVATI DA JE INT, A KOMP DODELE REFC KROZ DESG ASSIGN
			}
			
		}
	}
	
// *** vrv FactorLow_new_arr_actpars za C nivo
//	@Override
//	public void visit(FactorSub_new_record factorSub_new_record) {
//		factorSub_new_record.struct = new Struct(Struct.Class, currentType.getMembersTable());
//	}
	
	
//	@Override
//	public void visit(FactorLow_new_arr_actpars flow_new_arr_pars) {
//		if(!flow_new_arr_pars.getType().equals(Struct.Class)) {
//			report_error("Tip promenljive nije klasnog tipa [FactorLow_new_arr_expr_actpars]", flow_new_arr_pars);
//		}
//	
//		
//	}
	
	@Override
	public void visit(FactorLow_expr_cast flow_expr_cast) { //(int-int) => int
		flow_expr_cast.struct = flow_expr_cast.getExpr().struct;
	}
	
	
	/* ----- Designator Statements ----- */
	
	@Override
	public void visit(DesignatorStatement_assign ds_assign) {
		if(ds_assign.getDesignator().obj.getKind() != Obj.Var && ds_assign.getDesignator().obj.getKind() != Obj.Elem && ds_assign.getDesignator().obj.getKind() != Obj.Fld && !ds_assign.getDesignator().obj.getType().equals(setType)) {
			report_error("Dodela vrednosti u neadkvatan tip promenljive [DesignatorStatement_assign]: " + ds_assign.getDesignator().obj.getName(), ds_assign);
		
		} else if(ds_assign.getDesignator().obj.getType().getKind() == setType.getKind()) {
			report_info("Dodela vrednosti u var tipa SET: " + ds_assign.getDesignator().obj.getName(), ds_assign);
		} else if(ds_assign.getExpr().struct.getKind() == setType.getKind()) {
			report_info("Pristup promenljivoj tipa SET pri dodeli [DesignatorStatement_assign]", ds_assign);
		} else if(!ds_assign.getExpr().struct.assignableTo(ds_assign.getDesignator().obj.getType())) {
			report_info("*****Type expr: " + ds_assign.getExpr().struct.getKind() + " type Designator: " + ds_assign.getDesignator().obj.getType().getKind(), ds_assign);
			report_error("Neadekvatna dodela vrednosti/nekompatibilni tipovi [DesignatorStatement_assign]: " + ds_assign.getDesignator().obj.getName(), ds_assign);
		} 
		
		//report_info("----CurrType " + currentTypeObj.getName(), ds_assign);
		
	}
	
	@Override
	public void visit(DesignatorStatement_inc ds_inc) {
		if(ds_inc.getDesignator().obj.getKind() != Obj.Var && ds_inc.getDesignator().obj.getKind() != Obj.Elem && ds_inc.getDesignator().obj.getKind() != Obj.Fld ) {
			report_error("(Post)Inkrement neadekvatnog tipa promenljive [DesignatorStatement_inc]: " + ds_inc.getDesignator().obj.getName(), ds_inc);
		
		} else if(!ds_inc.getDesignator().obj.getType().equals(Tab.intType)) {
			report_error("(Post)Inkrement non-int promenljive [DesignatorStatement_inc]: " + ds_inc.getDesignator().obj.getName(), ds_inc);
			
		}
		
	}
	
	@Override
	public void visit(DesignatorStatement_dec ds_dec) {
		if(ds_dec.getDesignator().obj.getKind() != Obj.Var && ds_dec.getDesignator().obj.getKind() != Obj.Elem && ds_dec.getDesignator().obj.getKind() != Obj.Fld ) {
			report_error("(Post)Dekrement neadekvatnog tipa promenljive [DesignatorStatement_inc]: " + ds_dec.getDesignator().obj.getName(), ds_dec);
		
		} else if(!ds_dec.getDesignator().obj.getType().equals(Tab.intType)) {
			report_error("(Post)Dekrement non-int promenljive [DesignatorStatement_inc]: " + ds_dec.getDesignator().obj.getName(), ds_dec);
			
		}
		
	}
	
	
	/*MOZEMO U ONOM PAKETU SA SYM, SEMANTICANALYZER KLASAMA DA NAPRAVIMO NOVU KLASU 
	 * IZVEDENU IZ ...ast.VisitorAdaptor.java 
	 * S KOJOM MOZEMO DA DEFINISEMO POSEBAN 
	 * NACIN VISIT-A NEKOG KONKRETNOG PODSTABLA*/
	
	/* cvorovi u obe liste treba da budu isti, tkd jedan po jedan proveravamo da su assignable */
	
	/* prolazeci na dole pravimo nove liste, a vracajuci se na gore brisacemo trnt listu ako postoji neka ranije napravljena */
	
	@Override
	public void visit(DesignatorStatement_actPars ds_actPars) {
		if(ds_actPars.getDesignator().obj.getKind() != Obj.Meth) {
			report_error("Poziv neadekvatne metode [DesignatorStatement_actParsYes]: " + ds_actPars.getDesignator().obj.getName(), ds_actPars);
		} else {
			List<Struct> fpList = new ArrayList<Struct>();
			for( Obj local: ds_actPars.getDesignator().obj.getLocalSymbols()) {
				if(local.getKind() == Obj.Var && local.getLevel() == 1 && local.getFpPos() == 1) {
					report_info("Local " + local.getName(), ds_actPars);
					fpList.add(local.getType());
				}
			}
			
			//report_error(ds_actParsYes.getDesignator().obj.getName() + " fpList size: " + fpList.size(), ds_actParsYes);
		
			ActParsCounter apc = new ActParsCounter(); // PODSTABLO ZA VISITE ACTPARS
			
			//HOCU DA SE OBIDJE STABLO SA OVIM PODSTB
			
			ds_actPars.getActParsList().traverseBottomUp(apc);
			
			List<Struct> apList = apc.finalActParsList;
			
			try {
				//report_info(ds_actPars.getDesignator().obj.getName() + " fpList size: " + fpList.size(), ds_actPars);
				//report_info(ds_actPars.getDesignator().obj.getName() + " apList size: " + apList.size(), ds_actPars);
				
				if(fpList.size() != apList.size()) {
					throw new Exception("Size error");
				}
				
				for (int i = 0; i < fpList.size(); i++) {
					Struct fps = fpList.get(i);
					report_info("STRUCT KIND " + fps.getKind(), ds_actPars);
					Struct aps = apList.get(i);
					report_info("STRUCT KIND " + aps.getKind(), ds_actPars);
	
					if(fps.getKind()==Struct.Enum && aps.getKind()==Struct.Enum) {
						report_info("CONTINUE", ds_actPars);
						continue;
					} else if(!aps.assignableTo(fps)) {
						report_info("TYPE ERR", ds_actPars);
						
						throw new Exception("Type error");
					}
				}
				
			} catch (Exception e) {
				report_error("[" + e.getMessage() + "] " + "Parametri se ne poklapaju pri pozivu metode [DesignatorStatement_actPars]: " + ds_actPars.getDesignator().obj.getName(), ds_actPars);
			}
		
			report_info("Poziv metode [DesignatorStatement_actPars]: " + ds_actPars.getDesignator().obj.getName(), ds_actPars);
			
		}
		
		
	}
	
	@Override
	public void visit(DesignatorStatement_setop ds_setop) {
		Obj dsg1 = ds_setop.getDesignator().obj;
		Obj dsg2 = ds_setop.getDesignator1().obj;
		Obj dsg3 = ds_setop.getDesignator2().obj;
		
		if(!dsg1.getType().equals(setType) || !dsg2.getType().equals(setType) || !dsg3.getType().equals(setType)) {
			report_error("Neadekvatni tipovi promenljiva pri setop operaciji [DesignatorStatement_setop]: " + (!dsg1.getType().equals(setType) ? dsg1.getName() : (!dsg2.getType().equals(setType) ? dsg2.getName() : dsg3.getName())), ds_setop);
		}
	}
	
	
	/*label1: ...
	 * . . .  
	 *goto label1 => OK
	 * 
	 * 
	 * goto label2 => OK
	 * ...
	 * label2: ...
	 *  . . .
	 * goto l3 => ERR
	 *  
	 *  ~ set; ne sme postojati def vise istih tabeli i ne sme postojati goto sa labelom koja nije u setu
	 *  
	 * */
	
	/*
	//Twodots ::= (Twodots) TWODOTS;
	//Label ::= (Label) IDENT;
	//Statement ::= .. Label TWODOTS SingleStatement;
	//SingleStatement ::= ... (SignleStatement_goto) GOTO IDENT SEMI;... -> Umesto IDENT ne ide Label, da se ne bi dvaput pozivao visit i bacao gresku 
	
	 * private HashSet<String> setOfLabels = null; //svakim ulaskom u neku mt cemo inic, izlaskom na null
	 * private HashSet<String> setOfGotos = null;
	 * @Override
	 * public void visit(MethodRetnName_void/anytype ..){
	 * .... openScoupe()
	 * 		setOfLabels = new HashSet<>();
	 * 		setOfGotoLabels = new HashSet<>();
	 * }
	 * 
	 * @Override
	 * public void visit(MethodDecl ..){
	 * ....
	 * 		//provera labela da li je setOfGotoLabels PODSKUP setOfLabels
	 * 
	 * 		if(!setOfLabels.containsAll(setOfGotoLabels)){ //** ISPISATI KOJA JE TO LABELA
	 * 
	 * 			report_error("Postoji neadekvatan goto iskaz " + currentMethod.getName(), methodDecl);
	 * 		
	 * 		}
	 * 
	 * 		if ...
	 * 
	 * 		setOfLabels = null;
	 * 		setOfGotoLabels = null;
	 * 		---
	 * }
	 * 
	 * @Override
	 * public void visit(Label label) {
	 * 		if(!setOfLabels.add(label.getI1())){ //false -> vec postoji prom
	 * 
	 * 			report_error("Dvostruka definicija labele [Label]"+label.getI1(),label);
	 * 		}
	 * 
	 * }
	 * 
	 * @Override
	 * public void visit(SignleStatement_goto ss_goto) { // VISE GOTO NA ISTU LABELA JE OKEJ
	 * 		setOfGotoLabels.add(ss_goto.getI1())
	 * 
	 * }
	*/
	
	
	
	
	/* ----- Single Statements ----- */
	
	@Override
	public void visit(Label label) {
		if(!setOfLabels.add(label.getI1())) {
			report_error("Pokusaj definisanje vec postojece labele [Label]: " + label.getI1(), label);
		}
		
		report_info("Labela " + label.getI1(), label);
	}
	
	@Override
	public void visit(SingleStatement_read ss_read) {
		Struct ssType = ss_read.getDesignator().obj.getType();
		
		if(ss_read.getDesignator().obj.getKind() != Obj.Var && ss_read.getDesignator().obj.getKind() != Obj.Elem && ss_read.getDesignator().obj.getKind() != Obj.Fld ) {
			report_error("Read u promenljivu neadekvatnog tipa [SingleStatement_read]: " + ss_read.getDesignator().obj.getName(), ss_read);
		
		} else if(!ssType.equals(Tab.intType) && !ssType.equals(Tab.charType) && !ssType.equals(boolType)) {
			report_error("Read non-int/char/bool promenljive [SingleStatement_read]: " + ss_read.getDesignator().obj.getName(), ss_read);
			
		}
	}
	
	@Override
	public void visit(SingleStatement_print ss_print) {
		Struct exprType = ss_print.getExpr().struct;
		
		if(!exprType.equals(Tab.intType) && !exprType.equals(Tab.charType) && !exprType.equals(boolType) && !exprType.equals(setType) && !(exprType.getKind()==Struct.Array)) {
			report_error("Print non-int/char/bool/set/array promenljive [SingleStatement_print]", ss_print);
			
		}
	}
	
	@Override
	public void visit(SingleStatement_print_format ss_print_format) {
		Struct exprType = ss_print_format.getExpr().struct;
		
		if(!exprType.equals(Tab.intType) && !exprType.equals(Tab.charType) && !exprType.equals(boolType) && !exprType.equals(setType) && !(exprType.getKind()==Struct.Array)) {
			report_error("Print non-int/char/bool/set/array promenljive [SingleStatement_print_format]", ss_print_format);
			
		}
	}
	
	// VEC JE PROVERENO SVE ZA EXPR
	
	@Override
	public void visit(SingleStatement_ret ss_ret) {
//		if(currentMethod==null) {
//			report_error("Return se nalazi van tela metode [SingleStatement_ret].", ss_ret);
//		}
		returnExists = true;
		if(currentMethod.getType() != Tab.noType) {
			report_error("Void metoda nema odgovarajuci povratni tip [SingleStatement_ret]: " + currentMethod.getName(), ss_ret);
		}
	}
	
	@Override
	public void visit(SingleStatement_retExpr ss_retExpr) {
//		if(currentMethod==null) {
//			report_error("Return se nalazi van tela metode [SingleStatement_retExpr].", ss_retExpr);
//		}
		returnExists = true;
		if(!currentMethod.getType().equals(ss_retExpr.getExpr().struct)) {
			report_error("Metoda nema odgovarajuci povratni tip [SingleStatement_retExpr]: " + currentMethod.getName(), ss_retExpr);
		}
	}
	
	@Override
	public void visit(DoNonTerm doNotTerm) {
		loopCnt++;
	}
	
	@Override
	public void visit(SingleStatement_dowhile_nocond ss_dw_nocond) {
		loopCnt--;
	}
	
	@Override
	public void visit(SingleStatement_dowhile_cond ss_dw_cond) {
		loopCnt--;
	}
	
	@Override
	public void visit(SingleStatement_dowhile_cond_desStmt ss_dw_cond_desStmt) {
		loopCnt--;
	}
	
	@Override
	public void visit(SingleStatement_for ss_for) {
		loopCnt--;
	}
	
	
	@Override
	public void visit(SingleStatement_break ss_break) {
		if(loopCnt == 0) {
			report_error("Break naredba se ne nalazi u telu petlje [SingleStatement_break].", ss_break);
		}
		
	}
	
	@Override
	public void visit(SingleStatement_continue ss_continue) {
		if(loopCnt == 0) {
			report_error("Continue naredba se ne nalazi u telu petlje [SingleStatement_Continue].", ss_continue);
		}
		
	}
	
	@Override
	public void visit(SingleStatement_while ss_while) {
		loopCnt--;
	}
	
	/* ----- Condition ----- */
	
	// -> NE MORAMO PROVERAVATI U IF-ELSE I DO-WHILE JER TOKOM VISITA OVIH CVOROVA
	//    BACICEMO ERROR UKOLIKO NEKI ASPEKAT NIJE REZ TIPA BOOL
	
	// DA BISMO PRENOSILI KOJI JE TIP MORAMO SACUVATI POLJE TIPA STRUCT
	
	@Override
	public void visit(Condition cond) {
		cond.struct = cond.getConditionTermList().struct;
		if(!cond.struct.equals(boolType)) {
			report_error("Condition nije tipa bool.", cond);
		}
	}
	
	
	@Override
	public void visit(ConditionTermList_recr ctl_recr) {
		Struct left = ctl_recr.getConditionTermList().struct;
		Struct right = ctl_recr.getCondTerm().struct;
		
		if(left.equals(boolType) && right.equals(boolType)) {
			ctl_recr.struct = boolType;
		} else {
			report_error("OR operacija ima non-bool operandE [CondTermList_recursion]", ctl_recr);
			ctl_recr.struct = Tab.noType;
		}
	}
	
	
	@Override
	public void visit(ConditionTermList_single ctl_single) {
		ctl_single.struct = ctl_single.getCondTerm().struct;
	}
	
	
	@Override
	public void visit(CondTerm ct) {
		ct.struct = ct.getCondFactList().struct;
	}
	
	
	@Override
	public void visit(CondFactList_single cfl_single) {
		cfl_single.struct = cfl_single.getCondFact().struct;
	}
	
	@Override
	public void visit(CondFactList_recursion cfl_recr) {
		Struct left = cfl_recr.getCondFactList().struct;
		Struct right = cfl_recr.getCondFact().struct;
		
		if(left.equals(boolType) && right.equals(boolType)) {
			cfl_recr.struct = boolType;
		} else {
			report_error("AND operacija ima non-bool operandE [CondFactList_recursion]", cfl_recr);
			cfl_recr.struct = Tab.noType;
		}
	}
	
	
	@Override
	public void visit(CondFact_expr cf_expr) {
		if(!cf_expr.getExpr().struct.equals(boolType)) {
			report_error("Logicka operacija ima non-bool operanda [CondFact_expr]", cf_expr);
			cf_expr.struct = Tab.noType;
		} else {
			cf_expr.struct = boolType;
		}
	}
	
	@Override
	public void visit(CondFact_expr_rel_expr cf_expr_rel_expr) { // DA LI SU UPOREDIVI
		Struct left = cf_expr_rel_expr.getExpr().struct;
		Struct right = cf_expr_rel_expr.getExpr1().struct;
		
		if(left.compatibleWith(right)) {
			if(left.isRefType() || right.isRefType()) {
				if(cf_expr_rel_expr.getRelop() instanceof Eq || cf_expr_rel_expr.getRelop() instanceof Noteq) {
					cf_expr_rel_expr.struct = boolType;
				} else {
					report_error("Logicka operacija izmedju referenci sa neadekvatnim operatorima (mora == ili !=)", cf_expr_rel_expr);
					cf_expr_rel_expr.struct = Tab.noType;
				}
			}
			cf_expr_rel_expr.struct = boolType;
		} else {
			report_error("Logicka operacija ima nekompatibilne operandE [CondFact_expr_rel_expr]", cf_expr_rel_expr);
			cf_expr_rel_expr.struct = Tab.noType;
		}
	}
	
	
	@Override
	public void visit(DesignatorStatement_cappa d_cappa) {
		if(d_cappa.getDesignator().obj.getType().getKind()!=Struct.Array) {
			report_error("Operacija cappa ne radi sa array tipa promenljivom [DesignatorStatement_cappa]: " + d_cappa.getDesignator().obj.getName(), d_cappa);
		} else if (d_cappa.getDesignator().obj.getType().getKind()==Struct.Array && d_cappa.getDesignator().obj.getType().getElemType()!=Tab.intType) {
			report_error("Operacija cappa radi sa array tipa podataka non-int [DesignatorStatement_cappa]: " + d_cappa.getDesignator().obj.getName(), d_cappa);
		}
	}
	
	@Override
	public void visit(Final_f f) {
		finalFleg = true;
	}
	

	
//	@Override
//	public void visit(FactorLow_monkey m) {
//		if(m.getDesignator().obj.getType().getKind() != Struct.Array || m.getDesignator1().obj.getType().getKind() != Struct.Array) {
//			report_error("Monkey operacija sa non-array tipom podataka " + (m.getDesignator().obj.getType().getKind() != Struct.Array ? m.getDesignator().obj.getName() : m.getDesignator1().obj.getName()), m);
//			m.struct = Tab.noType;
//		}
//		if(!m.getDesignator().obj.getType().getElemType().equals(Tab.intType) || !m.getDesignator1().obj.getType().getElemType().equals(Tab.intType)) {
//			report_error("Monkey operacija sa non-int tipom podataka " + (!m.getDesignator().obj.getType().getElemType().equals(Tab.intType) ? m.getDesignator().obj.getName() : m.getDesignator1().obj.getName()), m);
//			m.struct = Tab.noType;
//		}
//		
//		m.struct = m.getDesignator().obj.getType();
//	}
	
//	@Override
//	public void visit(Label l) {
//		if(!setOfLabels.add(l.getI1()){
//			report_error("Dvostruka definicija labele: " + label.getI1(), label);
//	}	}
//	}
	
}
