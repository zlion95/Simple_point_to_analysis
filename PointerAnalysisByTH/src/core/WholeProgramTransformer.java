package core;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.ListIterator;
import java.util.Map;
import java.util.Map.Entry;
import java.util.TreeMap;
import java.util.TreeSet;

import soot.Local;
import soot.MethodOrMethodContext;
import soot.PackManager;
import soot.PhaseOptions;
import soot.Scene;
import soot.SceneTransformer;
import soot.SootClass;
import soot.SootField;
import soot.SootMethod;
import soot.Unit;
import soot.Value;
import soot.jimple.DefinitionStmt;
import soot.jimple.IntConstant;
import soot.jimple.InvokeExpr;
import soot.jimple.InvokeStmt;
import soot.jimple.JimpleBody;
import soot.jimple.NewExpr;
import soot.jimple.Stmt;
import soot.jimple.toolkits.callgraph.ReachableMethods;
import soot.jimple.toolkits.callgraph.Targets;
import soot.jimple.toolkits.callgraph.TopologicalOrderer;
import soot.jimple.toolkits.invoke.InlinerSafetyManager;
import soot.jimple.toolkits.invoke.SiteInliner;
import soot.jimple.toolkits.invoke.StaticInliner;
import soot.options.Options;
import soot.tagkit.Host;
import soot.jimple.toolkits.callgraph.CallGraph;
import soot.jimple.toolkits.callgraph.Edge;
import soot.jimple.toolkits.callgraph.ExplicitEdgesPred;
import soot.jimple.toolkits.callgraph.Filter;
import soot.util.Chain;
import soot.util.HashChain;
import soot.util.queue.QueueReader;


public class WholeProgramTransformer extends SceneTransformer {
	
	private void inlineTransform(String arg0, Map options) {
	    Filter explicitInvokesFilter = new Filter(new ExplicitEdgesPred());

	    //获取配置参数
	    boolean enableNullPointerCheckInsertion = PhaseOptions.getBoolean(options, "insert-null-checks");
	    boolean enableRedundantCastInsertion = PhaseOptions.getBoolean(options, "insert-redundant-casts");
	    String modifierOptions = PhaseOptions.getString(options, "allowed-modifier-changes");
	    float expansionFactor = PhaseOptions.getFloat(options, "expansion-factor");
	    int maxContainerSize = PhaseOptions.getInt(options, "max-container-size");
	    int maxInlineeSize = PhaseOptions.getInt(options, "max-inlinee-size");
	    boolean rerunJb = PhaseOptions.getBoolean(options, "rerun-jb");
	    
	    CallGraph cg = Scene.v().getCallGraph();
	    ArrayList<List<Host>> sitesToInline = new ArrayList<List<Host>>();
	    computeAverageMethodSizeAndSaveOriginalSizes();
	    
	    //构建inline的函数体到container的映射关系
	    //三元组： [需要inline的sootmethod，invoke unit, container]
	    {
	        TopologicalOrderer orderer = new TopologicalOrderer(cg);
	        orderer.go();
	        List<SootMethod> order = orderer.order();
	        ListIterator<SootMethod> it = order.listIterator(order.size());

	        while (it.hasPrevious()) {
	          SootMethod container = it.previous();
	          //TODO: 这里过滤的结果只inline了输入的文件的函数体，没有考虑其他文件中的inline情况,
	          //      比如FieldSensitivity中，就没有考虑class A和B的inline
	          if (methodToOriginalSize.get(container) == null) {
	            continue;
	          }

	          if (!container.isConcrete()) {
	            continue;
	          }

	          if (!explicitInvokesFilter.wrap(cg.edgesOutOf(container)).hasNext()) {
	            continue;
	          }

	          JimpleBody b = (JimpleBody) container.retrieveActiveBody();

	          List<Unit> unitList = new ArrayList<Unit>();
	          unitList.addAll(b.getUnits());
	          Iterator<Unit> unitIt = unitList.iterator();

	          while (unitIt.hasNext()) {
	            Stmt s = (Stmt) unitIt.next();
	            if (!s.containsInvokeExpr()) {
	              continue;
	            }

	            Iterator targets = new Targets(explicitInvokesFilter.wrap(cg.edgesOutOf(s)));
	            if (!targets.hasNext()) {
	              continue;
	            }
	            SootMethod target = (SootMethod) targets.next();
	            if (targets.hasNext()) {
	              continue;
	            }

	            if (!target.getDeclaringClass().isApplicationClass() || !target.isConcrete()) {
	              continue;
	            }

	            if (!InlinerSafetyManager.ensureInlinability(target, s, container, modifierOptions)) {
	              continue;
	            }

	            List<Host> l = new ArrayList<Host>();
	            l.add(target);
	            l.add(s);
	            l.add(container);

	            sitesToInline.add(l);
	          }
	        }
	     }
	    
	    //利用上面得到的三元组进行inline
	    //TODO:inline的顺序存在问题，应该把低一级的inline到高一级的才对吧
	    //TODO:考虑类的关联问题
	    {
	        Iterator<List<Host>> sitesIt = sitesToInline.iterator();
	        while (sitesIt.hasNext()) {
	          List l = sitesIt.next();
	          SootMethod inlinee = (SootMethod) l.get(0);
	          int inlineeSize = ((JimpleBody) (inlinee.retrieveActiveBody())).getUnits().size();

	          Stmt invokeStmt = (Stmt) l.get(1);

	          SootMethod container = (SootMethod) l.get(2);
	          int containerSize = ((JimpleBody) (container.retrieveActiveBody())).getUnits().size();

	          //TODO: 默认的maxContainerSize，和maxInlineeSize为0,会导致无法inline，我需要考虑一个合适的大小
//	          if (inlineeSize + containerSize > maxContainerSize) {
//	            continue;
//	          }

//	          if (inlineeSize > maxInlineeSize) {
//	            continue;
//	          }
	          
	          //TODO:设置一个比较合适的可拓展比例系数
//	          if (inlineeSize + containerSize > expansionFactor * methodToOriginalSize.get(container).intValue()) {
//	            continue;
//	          }

	          if (InlinerSafetyManager.ensureInlinability(inlinee, invokeStmt, container, modifierOptions)) {
	            // Not that it is important to check right before inlining if the site is still valid.
	        	//TODO: soot自带的inline对类的成员变量没有做关联处理！我需要完成这部分的补全
	            SiteInliner.inlineSite(inlinee, invokeStmt, container, options);
	            if (rerunJb) {
	              PackManager.v().getPack("jb").apply(container.getActiveBody());
	            }
	          }
	        }
	     }
	}
	
	@Override
	protected void internalTransform(String arg0, Map options) {
		
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
							//System.out.println(ie);
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
							//当等号右边的box为 new语句时，生成一个新的约束
							if (((DefinitionStmt)u).getRightOp() instanceof NewExpr) {
								//System.out.println("Alloc " + allocId);
								Local test_value = (Local)((DefinitionStmt) u).getLeftOp();
								System.out.println(allocId + "\t" + test_value.getName());
								anderson.addNewConstraint(allocId, (Local)((DefinitionStmt) u).getLeftOp());
							}
							if (((DefinitionStmt)u).getLeftOp() instanceof Local && ((DefinitionStmt)u).getRightOp() instanceof Local) {
								anderson.addAssignConstraint((Local)((DefinitionStmt) u).getRightOp(), (Local)((DefinitionStmt) u).getLeftOp());
							}
						}
					}
				}
			//}
		}
		this.inlineTransform(arg0, options);
	    
		System.out.println("Start anderson checking.");
		anderson.run();
		String answer = "";
		for (Entry<Integer, Local> q : queries.entrySet()) {
			System.out.println(q);
		}
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
	
	//保存原始的jimple文件的函数对应的代码长度
	private final HashMap<SootMethod, Integer> methodToOriginalSize = new HashMap<SootMethod, Integer>();

	//TODO:这里只使用了applicationClass的，实际上也可能会
	private void computeAverageMethodSizeAndSaveOriginalSizes() {
		long sum = 0, count = 0;
		Scene scene_v = Scene.v();
		Iterator classesIt = Scene.v().getApplicationClasses().iterator();

		while (classesIt.hasNext()) {
			SootClass c = (SootClass) classesIt.next();
			Iterator methodsIt = c.methodIterator();
			while (methodsIt.hasNext()) {
				SootMethod m = (SootMethod) methodsIt.next();
		        if (m.isConcrete()) {
		          Chain<SootClass> refClasses = this.getRefClasses(m, c);
		          int size = ((JimpleBody) m.retrieveActiveBody()).getUnits().size();
		          sum += size;
		          methodToOriginalSize.put(m, new Integer(size));
		          count++;
		        }
			}
		}
		if (count == 0) {
			return;
		}
	}

	//把除了包含本函数的所有调用到的类都添加进来
	//TODO: 需要过滤处理一下标准库的类，比如System.out
	private Chain<SootClass> getRefClasses(SootMethod m, SootClass referingClass) {
		Chain<SootClass> refClasses = new HashChain<SootClass>();
		for (Unit u: m.getActiveBody().getUnits()) {
			if (u instanceof InvokeStmt) {
				//需要exclude本身的类
				SootMethod method = ((InvokeStmt) u).getInvokeExpr().getMethod();
				List<Value> args =  ((InvokeStmt) u).getInvokeExpr().getArgs();
				SootClass refClass = method.getDeclaringClass();
				if (refClass.equals(referingClass)) continue;
				if (!refClasses.contains(refClass)) refClasses.add(refClass);
			}
		}
		return refClasses;
	}
}
