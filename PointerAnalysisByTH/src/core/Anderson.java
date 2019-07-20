package core;

import java.util.ArrayList;
import java.util.Comparator;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;

import soot.Local;
import soot.SootMethod;
import soot.SootMethodRef;
import soot.Type;
import soot.jimple.ParameterRef;
import soot.jimple.internal.JimpleLocal;

class AssignConstraint {
	ConditionLocal from, to;
	int callId = -1;
	AssignConstraint(ConditionLocal cl, ConditionLocal conditionLocal) {
		this.from = cl;
		this.to = conditionLocal;
	}
}

class NewConstraint {
	Local to;
	int allocId;
	int callId = -1;
	NewConstraint(int allocId, Local to) {
		this.allocId = allocId;
		this.to = to;
	}
}

class ParamConstraint implements Comparable<ParamConstraint>{
	static Map<SootMethod, Integer> methodCallId = new HashMap<SootMethod, Integer>();
	static Map<SootMethod, TreeSet<Local>> methodCallAssignLocals = 
			new HashMap<SootMethod, TreeSet<Local>>();
	static Map<SootMethod, ArrayList<Local>> methodReturnLocals 
	= new HashMap<SootMethod, ArrayList<Local>>();
	
	public static void addCallMethodLocal(SootMethod method, Local local) {
		TreeSet<Local> locals;
		if (methodCallAssignLocals.containsKey(method)) locals = methodCallAssignLocals.get(method);
		else locals = new TreeSet<Local>();
		locals.add(local);
		methodCallAssignLocals.put(method, locals);
	}
	public static TreeSet<Local> getMethodCallLocals(SootMethod sm) {
		return methodCallAssignLocals.get(sm);
	}
	public static void addMethod(SootMethod method) {
		//从1开始是调用函数的语句的constraint，0用来存放函数本身的constraint
		if (!methodCallId.containsKey(method)) methodCallId.put(method, 1);
	}
	
	public static List<Local> getMethodReturnLocals(SootMethod sm) {
		return methodReturnLocals.get(sm);
	}
	
	public static int getPresentCallId(SootMethod method) {
		if (!methodCallId.containsKey(method)) return 0;
		return methodCallId.get(method);
	}
	
	public static int getMethodCallId(SootMethod method) {
		if (!methodCallId.containsKey(method)) addMethod(method);
		int id = methodCallId.get(method);
		methodCallId.put(method, id + 1);
		return id;
	}
	
	// 0 0 1 1 2 2 。。。M M 
	public static void addMethodReturnLocals(SootMethod sm, Local local) {
		List<Local> returnLocals;
		if (methodReturnLocals.containsKey(sm)) returnLocals = methodReturnLocals.get(sm);
		else returnLocals = new ArrayList<Local>();
		returnLocals.add(local);
		methodReturnLocals.put(sm, (ArrayList<Local>) returnLocals);
	}
	
	int callId;
	SootMethod method;
	Local local;
	int index;	//不妨使index为-1时代表返回的目标local
	boolean bias;	//用于表示call_args 与 method_args的方向
	boolean isPrimType;	 //true表示值传递，不需要加上隐含赋值语句; false引用传递，访问同一地址，需要加上隐含的返回赋值。
	
	ParamConstraint(SootMethod method, int callId, int index, boolean bias, Local local, boolean isPrimType) {
		this.method = method;
		this.index = index;
		this.callId = callId;
		this.bias = bias;
		this.local = local;
		this.isPrimType = isPrimType;
	}

	@Override
	public int compareTo(ParamConstraint o) {
		return this.callId - o.callId;
	}
}

class ConditionInteger implements Comparable<ConditionInteger> {

	int value;
	SootMethod sm;
	int condition;
	public ConditionInteger(int value, SootMethod sm, int condition) {
		this.value = value;
		this.sm = sm;
		this.condition = condition;
	}
	@Override
	public int compareTo(ConditionInteger o) {
		if (this.condition > o.condition) return 1;
		else if (this.condition < o.condition) return -1;
		else return this.value - o.value;
	}
	
	public static TreeSet<Integer> transferCondIntToIngeter(TreeSet<ConditionInteger> cit) {
		Iterator<ConditionInteger> it = cit.iterator();
		TreeSet<Integer> is = new TreeSet<Integer>();
		while (it.hasNext()) {
			ConditionInteger ci = it.next();
			is.add(ci.value);
		}
		return is;
	}
}

class ConditionLocal {
	Local local;
	SootMethod sm;
	int condition;
	public ConditionLocal(Local local, SootMethod sm, int condition) {
		this.local = local;
		this.sm = sm;
		this.condition = condition;
	}
	
}

public class Anderson {
	private List<AssignConstraint> assignConstraintList = new ArrayList<AssignConstraint>();
	private List<NewConstraint> newConstraintList = new ArrayList<NewConstraint>();
	//TODO: 全局变量传递的constraint
//	private List<ParamConstraint> paramConstraintList = new ArrayList<ParamConstraint>();
	private Map<SootMethod, ArrayList<ParamConstraint>> paramConstraintMap = 
			new HashMap<SootMethod, ArrayList<ParamConstraint>>();
	Map<Local, TreeSet<ConditionInteger>> pts = new HashMap<Local, TreeSet<ConditionInteger>>();
	void addAssignConstraint(ConditionLocal cl, ConditionLocal conditionLocal) {
		assignConstraintList.add(new AssignConstraint(cl, conditionLocal));
	}
	void addAssignConstraint(Local from, Local to) {
		assignConstraintList.add(new AssignConstraint(
				new ConditionLocal(from, null, 0), new ConditionLocal(to, null, 0)));
	}
	void addNewConstraint(int alloc, Local to) {
		newConstraintList.add(new NewConstraint(alloc, to));		
	}
	void addParamConstraint(SootMethod sm, int callId, int index, boolean bias, Local local, boolean isPrimType) {
		List<ParamConstraint> paramConstraintList;
		if (paramConstraintMap.containsKey(sm)) {
			paramConstraintList = paramConstraintMap.get(sm);
		} else {
			paramConstraintList = new ArrayList<ParamConstraint>(); 
		}
		paramConstraintList.add(new ParamConstraint(sm, callId, index, bias, local, isPrimType));
		paramConstraintMap.put(sm, (ArrayList<ParamConstraint>) paramConstraintList);
	}
	
	void run() {
		for (NewConstraint nc : newConstraintList) {
			ConditionInteger ncci = new ConditionInteger(nc.allocId, null, 0);
			if (!pts.containsKey(nc.to)) {
				pts.put(nc.to, new TreeSet<ConditionInteger>());
			}
			pts.get(nc.to).add(ncci);
		}
		
		//Transfer paramConstraint to assignConstraint
		//TODO:需要测试
		Iterator<SootMethod> ipc = paramConstraintMap.keySet().iterator();
		while (ipc.hasNext()) {
			SootMethod sm = ipc.next();
			List<ParamConstraint> lpc = paramConstraintMap.get(sm);
			if (lpc.isEmpty()) continue;
			lpc.sort(null);
			
			Map<Integer, Local> pattern_args = new HashMap<Integer, Local>();
			Local returnLocal = null;
			//Find parameters and return-to local
			for (ParamConstraint pc : lpc) {
				if (pc.callId == 0 && !pc.bias) {
					pattern_args.put(pc.index, pc.local);
				} 

			}
			for (ParamConstraint pc : lpc) {
				if (pc.bias && pc.index == -1) {
					returnLocal = pc.local;
				}
				if (pc.callId == 0 || pc.index == -1) continue;
				ConditionLocal cl = new ConditionLocal(pc.local, sm, pc.callId);
				this.addAssignConstraint(cl, 
						new ConditionLocal(pattern_args.get(pc.index), sm, pc.callId));
				if (!pc.isPrimType) { //引用类型需要把情况全部同步
					this.addAssignConstraint(new ConditionLocal(pattern_args.get(pc.index), sm, pc.callId), cl);
				}
				List<Local> methodReturnLocals = ParamConstraint.getMethodReturnLocals(sm);
				if (methodReturnLocals == null) continue;
				for (Local l : methodReturnLocals) {
					for (int i = 1; i <= ParamConstraint.getPresentCallId(sm); ++i) {
						this.addAssignConstraint(new ConditionLocal(l, sm, i), 
								new ConditionLocal(returnLocal, sm, pc.callId));				
					}
				}
			}
		}
		
//		paramConstraintMap.clear();
		System.out.println("All assignConstraint size: " + assignConstraintList.size());
		
		for (boolean flag = true; flag; ) {
			flag = false;
			for (AssignConstraint ac : assignConstraintList) {
				if (!pts.containsKey(ac.from.local)) {
					continue;
				}
				if (!pts.containsKey(ac.to.local)) {
					pts.put(ac.to.local, new TreeSet<ConditionInteger>());
				}
				Local to = ac.to.local;
				//如果是函数调用返回值
				TreeSet<Local> methodCallLocals = ParamConstraint.getMethodCallLocals(ac.from.sm);
				if (methodCallLocals == null) continue;
				if (methodCallLocals.contains(to)) {
					Iterator<ConditionInteger> fit = pts.get(ac.from.local).iterator();
					while (fit.hasNext()) {
						ConditionInteger fci = fit.next();
						if (fci.condition == ac.to.condition) {
							flag &= pts.get(ac.to.local).add(new ConditionInteger(fci.value, ac.to.sm, 0));
						}
					}
				} else {
					//非函数返回值
					if (pts.get(ac.to.local).addAll(pts.get(ac.from.local))) {
						flag = true;
					}
				}
			}
		}
	}
	
	TreeSet<Integer> getPointsToSet(Local local) {
		TreeSet<ConditionInteger> cit = pts.get(local);
		return ConditionInteger.transferCondIntToIngeter(cit);
	}
	
}
