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
import soot.SootFieldRef;
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
import soot.jimple.internal.JInstanceFieldRef;
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
	          if (methodToOriginalSize.get(container) == null) {
	            continue;
	          }

	          //这里暴力的把library的方法全部过滤掉是否会出问题呢？
	          if (container.isJavaLibraryMethod()) continue;
	          if (!container.isConcrete()) continue;

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

	            // 这里先判断过滤完的结果是否存在，再判断是否唯一
	            Iterator targets = new Targets(explicitInvokesFilter.wrap(cg.edgesOutOf(s)));
	            if (!targets.hasNext()) continue;
	            SootMethod target = (SootMethod) targets.next();
	            if (targets.hasNext()) continue;
	            if (!target.isConcrete()) continue;
	            //这里确保了只内联applicationClass内的函数
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
	        
	            sitesToInline.add(0, l);
	          }
	        }
	     }
	    
	    //利用上面得到的三元组进行inline
	    {
	        Iterator<List<Host>> sitesIt = sitesToInline.iterator();
	        while (sitesIt.hasNext()) {
	          List l = sitesIt.next();
	          SootMethod inlinee = (SootMethod) l.get(0);
	          int inlineeSize = ((JimpleBody) (inlinee.retrieveActiveBody())).getUnits().size();

	          Stmt invokeStmt = (Stmt) l.get(1);

	          SootMethod container = (SootMethod) l.get(2);
	          int containerSize = ((JimpleBody) (container.retrieveActiveBody())).getUnits().size();

	          if (InlinerSafetyManager.ensureInlinability(inlinee, invokeStmt, container, modifierOptions)) {
	            // Not that it is important to check right before inlining if the site is still valid.
	        	//TODO: soot自带的inline对类的成员变量没有做关联处理！我需要完成这部分的补全
	            SiteInliner.inlineSite(inlinee, invokeStmt, container, options);
	          }
	        }
	     }
	}
	
	@Override
	protected void internalTransform(String arg0, Map options) {
		
		TreeMap<Integer, Local> queries = new TreeMap<Integer, Local>();
		Anderson anderson = new Anderson(); 
		
		//TODO: inline会破坏callgraph
//		this.inlineTransform(arg0, options);	//把applicationClass的函数做inline
		ReachableMethods reachableMethods = Scene.v().getReachableMethods();
		QueueReader<MethodOrMethodContext> qr = reachableMethods.listener();		
		
		Filter explicitInvokesFilter = new Filter(new ExplicitEdgesPred());
		//TODO: 1.需要把对象的域与函数调用的参数传递挂接起来
		//		2.
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
							//跳过基本库里面的方法，可能会存在问题
//							if (ie.getMethod().isJavaLibraryMethod()) continue;
//							Iterator<Edge> edges = explicitInvokesFilter.wrap(Scene.v().getCallGraph().edgesOutOf(sm));
//							int edge_id = 0;
//							while (edges.hasNext()) {
//								Edge e = edges.next();
//								System.out.println(edge_id + "\t" + e.toString());
//								edge_id++;
//							}
							//标注
							if (ie.getMethod().toString().equals("<benchmark.internal.Benchmark: void alloc(int)>")) {
								allocId = ((IntConstant)ie.getArgs().get(0)).value;
							}
							//测试
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
	
	private HashMap<SootField, TreeSet<JInstanceFieldRef>> fieldReferMap = new HashMap<SootField, TreeSet<JInstanceFieldRef>>();
	
	private void buildCallMethodConstrain(InvokeExpr ie, Anderson anderson, int allocId) {
        SootMethod sm = ie.getMethod();
        if (!sm.hasActiveBody()) return;
        if (!Scene.v().getReachableMethods().contains(sm)) return;
        
		SootClass c = sm.getDeclaringClass();
		Iterator<SootField> it = c.getFields().iterator();
		while (it.hasNext()) {
			fieldReferMap.put(it.next(), new TreeSet<JInstanceFieldRef>());
		}
		for (Unit u : sm.getActiveBody().getUnits()) {
			if (u instanceof DefinitionStmt) {
				//TODO: 这里需要做的是把全局变量的修改结果和container的使用挂接起来
			}
		}
	}
	
	//保存原始的jimple文件的函数对应的代码长度
	private final HashMap<SootMethod, Integer> methodToOriginalSize = new HashMap<SootMethod, Integer>();

	//把可能需要inline的函数都填写进来并统计长度
	  private void computeAverageMethodSizeAndSaveOriginalSizes() {
	    long sum = 0, count = 0;
	    Iterator classesIt = Scene.v().getApplicationClasses().iterator();

	    while (classesIt.hasNext()) {
	      SootClass c = (SootClass) classesIt.next();

	      Iterator methodsIt = c.methodIterator();
	      while (methodsIt.hasNext()) {
	        SootMethod m = (SootMethod) methodsIt.next();
	        if (m.isConcrete()) {
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
//	private void computeAverageMethodSizeAndSaveOriginalSizes() {
//		long sum = 0, count = 0;
//		Scene scene_v = Scene.v();
//		Iterator classesIt = Scene.v().getApplicationClasses().iterator();
//		Chain<SootClass> refClassSet = new HashChain<SootClass>();
//		Chain<SootClass> checkedClassSet = new HashChain<SootClass>();
//		boolean appHasNext = classesIt.hasNext(),
//				isRefClassSetEmpty = refClassSet.isEmpty();
//		while (appHasNext || !isRefClassSetEmpty) {
//			SootClass c;
//			if (appHasNext) c = (SootClass) classesIt.next();
//			else {
//				c = refClassSet.getFirst();
//				refClassSet.removeFirst();
//			}
//			Iterator methodsIt = c.methodIterator();
//			while (methodsIt.hasNext()) {
//				SootMethod m = (SootMethod) methodsIt.next();
//		        if (m.isConcrete()) {
//		          Chain<SootClass> refClasses = this.getRefClasses(m, c);
//		          for (SootClass refClass : refClasses) {
//		        	  if (refClassSet.contains(refClass) || checkedClassSet.contains(refClass)) continue;
//		        	  refClassSet.add(refClass);
//		          }
//		          int size = ((JimpleBody) m.retrieveActiveBody()).getUnits().size();
//		          sum += size;
//		          methodToOriginalSize.put(m, new Integer(size));
//		          count++;
//		        }
//			}
//			checkedClassSet.add(c);
//			appHasNext = classesIt.hasNext();
//			isRefClassSetEmpty = refClassSet.isEmpty();
//		}
//		if (count == 0) {
//			return;
//		}
//	}

//	private Chain<SootClass> getRefClasses(SootMethod m, SootClass referingClass) {
//		Chain<SootClass> refClasses = new HashChain<SootClass>();
//		if (m.hasActiveBody()) {
//			for (Unit u: m.getActiveBody().getUnits()) {
//				if (u instanceof InvokeStmt) {
//					SootMethod method = ((InvokeStmt) u).getInvokeExpr().getMethod();
//					List<Value> args =  ((InvokeStmt) u).getInvokeExpr().getArgs();
//					SootClass refClass = method.getDeclaringClass();
//					if (refClass.equals(referingClass)) continue;
//					if (!refClasses.contains(refClass)) refClasses.add(refClass);
//				}
//			}
//		}
//		return refClasses;
//	}
}
