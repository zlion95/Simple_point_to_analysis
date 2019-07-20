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
import soot.jimple.internal.InvokeExprBox;
import soot.jimple.internal.JAssignStmt;
import soot.jimple.internal.JVirtualInvokeExpr;
import soot.jimple.toolkits.callgraph.CallGraph;
import soot.jimple.toolkits.callgraph.ReachableMethods;
import soot.util.Chain;
import soot.util.queue.QueueReader;

public class WholeProgramTransformer extends SceneTransformer {
	private static int MaxRecursionLevel = 50;
	
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
				int allocId = 0;
				if (sm.hasActiveBody()) {
					for (Unit u : sm.getActiveBody().getUnits()) {
						//System.out.println("S: " + u);
						//System.out.println(u.getClass());
						if (u instanceof InvokeStmt) {
							InvokeExpr ie = ((InvokeStmt) u).getInvokeExpr();
							if (ie.getMethod().toString().equals("<benchmark.internal.Benchmark: void alloc(int)>")) {
								allocId = ((IntConstant)ie.getArgs().get(0)).value;
							}
							if (ie.getMethod().toString().equals("<benchmark.internal.Benchmark: void test(int,java.lang.Object)>")) {
								Value v = ie.getArgs().get(1);
								int id = ((IntConstant)ie.getArgs().get(0)).value;
								queries.put(id, (Local)v);
							}
						}
						if (u instanceof DefinitionStmt) {
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
								anderson.addParamConstraint(sm, 0, paramIndex, false, (Local)((DefinitionStmt) u).getLeftOp());
							}
							if (((DefinitionStmt)u).getLeftOp() instanceof Local && ((DefinitionStmt)u).getRightOp() instanceof InvokeExpr) {
								InvokeExprBox ib = (InvokeExprBox)((DefinitionStmt) u).getRightOpBox();
								
							}
						}
					}
				}
			//}
		}
		
		CallGraph cg = Scene.v().getCallGraph();
		SootMethod mainFunc = Scene.v().getMainMethod();
		Chain<SootClass> applicationClasses = Scene.v().getApplicationClasses();
		int level = 1;
		Queue<SootMethod> toCallMethods = new LinkedList<SootMethod>();
		SootMethod testMethod = applicationClasses.getFirst().getMethodByName("test");
		for (Unit u : testMethod.getActiveBody().getUnits()) {
			if (u.toString().equals("specialinvoke r0.<test.FieldSensitivity: void assign(benchmark.objects.A,benchmark.objects.A)>(r2, r3)")) {
//				JAssignStmt js = (JAssignStmt) u;
//				JVirtualInvokeExpr jvie = (JVirtualInvokeExpr)js.getRightOp();
//				List<Value> args = jvie.getArgs();
				InvokeExpr ie = (InvokeExpr) u;
				SootMethod callMethod = ie.getMethod();
				List<Value> args = ie.getArgs();
				if (ie.getArgCount() != callMethod.getParameterCount()) continue;
				for (int i = 0; i < ie.getArgCount(); ++i) {
					//这里可能存在很大问题Local是自动序列化的参数
					Local arg = (Local)ie.getArg(i);
					Local parameter = callMethod.getActiveBody().getParameterLocal(i);
				}
			}
		}
		toCallMethods.offer(mainFunc);
		while (!toCallMethods.isEmpty() && level < this.MaxRecursionLevel) {
			SootMethod sm = toCallMethods.poll();
			
			if (!sm.hasActiveBody()) continue;
			if (!Scene.v().getReachableMethods().contains(sm)) continue;
			
			for (Unit u : sm.getActiveBody().getUnits()) {
				if (u instanceof InvokeExpr) {
					
				}
				if (u instanceof DefinitionStmt) {
					
				}
			}
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
