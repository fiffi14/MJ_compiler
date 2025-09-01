package rs.ac.bg.etf.pp1;

import rs.ac.bg.etf.pp1.ast.VisitorAdaptor;

import java.util.ArrayList;
import java.util.List;
import java.util.Stack;

import rs.ac.bg.etf.pp1.ast.*;

import rs.etf.pp1.symboltable.concepts.Struct;
import rs.etf.pp1.symboltable.concepts.Obj;


public class ActParsCounter extends VisitorAdaptor {
		
	List<Struct> finalActParsList;
	
	Stack<List<Struct>> actParsListStack = new Stack<List<Struct>>();
	
	@Override
	public void visit(ActParsListBefore aplBefore) {
		actParsListStack.push(new ArrayList<Struct>());
	}
	
	@Override
	public void visit(ActPars ap) {
		actParsListStack.peek().add(ap.getExpr().struct);
	}
	
	@Override
	public void visit(ActParsList_recr ap_recr) {
		finalActParsList = actParsListStack.pop();
	}
	
	@Override
	public void visit(ActParsList_e ap_e) {
		finalActParsList = actParsListStack.pop();
	}
	
	
//	@Override
//	public void visit(ActPars ap) {
//		ActParsList.add(ap.getExpr().struct);
//	}
//	
}
