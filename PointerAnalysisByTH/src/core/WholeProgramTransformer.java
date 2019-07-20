package core;

import java.util.ArrayList;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Queue;
import java.util.Stack;
import java.util.TreeMap;
import java.util.TreeSet;

import soot.Local;
import soot.PrimType;
import soot.MethodOrMethodContext;
import soot.Scene;
import soot.SceneTransformer;
import soot.SootClass;
import soot.SootMethod;
import soot.Unit;
import soot.Value;
import soot.jimple.DefinitionStmt;
import soot.jimple.Expr;
import soot.jimple.IntConstant;
import soot.jimple.InvokeExpr;
import soot.jimple.InvokeStmt;
import soot.jimple.NewExpr;
import soot.jimple.ParameterRef;
import soot.jimple.ReturnStmt;
import soot.jimple.internal.InvokeExprBox;
import soot.jimple.internal.JAssignStmt;
import soot.jimple.internal.JVirtualInvokeExpr;
import soot.jimple.internal.JimpleLocal;
import soot.jimple.toolkits.callgraph.CallGraph;
import soot.jimple.toolkits.callgraph.ReachableMethods;
import soot.util.Chain;
import soot.util.queue.QueueReader;


public class WholeProgramTransformer extends SceneTransformer {
	private static int MaxRecursionLevel = 50;
	private static String[] PrimTypes = {"int", "byte", "double", "char", "boolean", "float", "long", "short"};
	
	private static boolean isPrimTypes(String s) {
		for (String pt : PrimTypes) {
			if (s.equals(pt)) return true;
		}
		return false;
	}
	
	@Override
	protected void internalTransform(String arg0, Map<String, String> arg1) {
		
		TreeMap<Integer, Local> queries = new TreeMap<Integer, Local>();
		Anderson anderson = new Anderson(); 
		
		ReachableMethods reachableMethods = Scene.v().getReachableMethods();
		QueueReader<MethodOrMethodContext> qr = reachableMethods.listener();		
		while (qr.hasNext()) {
			SootMethod sm = qr.next().method();
			//if (sm.toString().contains("Hello")) {
				//System.out.println(sm);
			if (sm.isJavaLibraryMethod()) continue;
			System.out.println("Reached method:\t" + sm.toString());
			int allocId = 0;
			if (sm.toString().equals("<test.FieldSensitivity: void test()>"))
				allocId = 0;
			if (sm.hasActiveBody()) {
				for (Unit u : sm.getActiveBody().getUnits()) {
					//System.out.println("S: " + u);
					//System.out.println(u.getClass());
					if (u instanceof InvokeStmt) {
						InvokeExpr ie = ((InvokeStmt) u).getInvokeExpr();
						if (ie.getMethod().toString().equals("<benchmark.internal.Benchmark: void alloc(int)>")) {
							allocId = ((IntConstant)ie.getArgs().get(0)).value;
						}
						else if (ie.getMethod().toString().equals("<benchmark.internal.Benchmark: void test(int,java.lang.Object)>")) {
							Value v = ie.getArgs().get(1);
							int id = ((IntConstant)ie.getArgs().get(0)).value;
							queries.put(id, (Local)v);
						}
						else {
							int callId = ParamConstraint.getMethodCallId(ie.getMethod());
							for (int i = 0; i < ie.getArgCount(); ++i) {
								String typeName = ie.getArg(i).getType().toString();
								if (ie.getArg(i) instanceof Local) {	
									anderson.addParamConstraint(ie.getMethod(), callId, i, true, (Local)ie.getArg(i), WholeProgramTransformer.isPrimTypes(typeName));
								} else {
									//我们始终关注的是allocId因此对于非Local的部分，我们不妨新建一个Local来替代，同时建立new constraint-> allocId=0
									Local local = new JimpleLocal(ie.getArg(i).toString(), ie.getMethod().getParameterType(i));
									anderson.addNewConstraint(0, local);
									anderson.addParamConstraint(ie.getMethod(), callId, i, true, local, WholeProgramTransformer.isPrimTypes(typeName));
								}
							}
						}
						
					}
					if (u instanceof DefinitionStmt) {
						if (((DefinitionStmt) u).getLeftOp().toString().equals("r5"))
							System.out.println();
						if (((DefinitionStmt)u).getRightOp() instanceof NewExpr) {
							//System.out.println("Alloc " + allocId);
							anderson.addNewConstraint(allocId, (Local)((DefinitionStmt) u).getLeftOp());
						}
						if (((DefinitionStmt)u).getLeftOp() instanceof Local && ((DefinitionStmt)u).getRightOp() instanceof Local) {
							anderson.addAssignConstraint((Local)((DefinitionStmt) u).getRightOp(), (Local)((DefinitionStmt) u).getLeftOp());
						}
						if (((DefinitionStmt)u).getLeftOp() instanceof Local && ((DefinitionStmt)u).getRightOp() instanceof ParameterRef) {
							//函数参数赋值语句
							int paramIndex = ((ParameterRef)((DefinitionStmt) u).getRightOp()).getIndex();
							anderson.addParamConstraint(sm, 0, paramIndex, false, (Local)((DefinitionStmt) u).getLeftOp(), true);
						}
						if (((DefinitionStmt)u).getLeftOp() instanceof Local && ((DefinitionStmt)u).getRightOp() instanceof InvokeExpr) {
							InvokeExpr ie2 = ((DefinitionStmt) u).getInvokeExpr();
							int callId = ParamConstraint.getMethodCallId(ie2.getMethod());
							
							for (int i = 0; i < ie2.getArgCount(); ++i) {
								String typeName = ie2.getArg(i).getType().toString();
								if (ie2.getArg(i) instanceof Local) {	
									anderson.addParamConstraint(ie2.getMethod(), callId, i, true, (Local)ie2.getArg(i), this.isPrimTypes(typeName));
								} else {
									//我们始终关注的是allocId因此对于非Local的部分，我们不妨新建一个Local来替代，同时建立new constraint-> allocId=0
									Local local = new JimpleLocal(ie2.getArg(i).toString(), ie2.getMethod().getParameterType(i));
									anderson.addNewConstraint(0, local);
									anderson.addParamConstraint(ie2.getMethod(), callId, i, true, local, this.isPrimTypes(typeName));
								}
							}
							Local returnTo = (Local)((DefinitionStmt) u).getLeftOp();
							anderson.addParamConstraint(ie2.getMethod(), callId, -1, true, returnTo, true);
						}
						//TODO: 需要完成域分析（即成员变量的分析）
					}
					if (u instanceof ReturnStmt) {
						ReturnStmt rs = ((ReturnStmt)u);
						if (rs.getOp() instanceof Local) {
							ParamConstraint.addMethodReturnLocals(sm, (Local)rs.getOp());
						} else {
							Local local = new JimpleLocal(rs.getOp().toString(), sm.getReturnType());
							anderson.addNewConstraint(0, local);
							ParamConstraint.addMethodReturnLocals(sm, local);
						}
					}
				}
			}
			//}
		}
		
		anderson.run();
		String answer = "";
		for (Entry<Integer, Local> q : queries.entrySet()) {
			TreeSet<Integer> result = anderson.getPointsToSet(q.getValue());
			answer += q.getKey().toString() + ":";
			for (Integer i : result) {
				answer += " " + i;
			}
			answer += "\n";
		}
		AnswerPrinter.printAnswer(answer);
		
	}

}
