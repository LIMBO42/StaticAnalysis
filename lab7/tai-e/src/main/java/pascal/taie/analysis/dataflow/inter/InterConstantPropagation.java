 /*
  * Tai-e: A Static Analysis Framework for Java
  *
  * Copyright (C) 2020-- Tian Tan <tiantan@nju.edu.cn>
  * Copyright (C) 2020-- Yue Li <yueli@nju.edu.cn>
  * All rights reserved.
  *
  * Tai-e is only for educational and academic purposes,
  * and any form of commercial use is disallowed.
  * Distribution of Tai-e is disallowed without the approval.
  */

 package pascal.taie.analysis.dataflow.inter;


 import pascal.taie.World;
 import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
 import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
 import pascal.taie.analysis.dataflow.analysis.constprop.Value;
 import pascal.taie.analysis.dataflow.solver.Solver;
 import pascal.taie.analysis.graph.cfg.CFG;
 import pascal.taie.analysis.graph.cfg.CFGBuilder;
 import pascal.taie.analysis.graph.icfg.CallEdge;
 import pascal.taie.analysis.graph.icfg.CallToReturnEdge;
 import pascal.taie.analysis.graph.icfg.NormalEdge;
 import pascal.taie.analysis.graph.icfg.ReturnEdge;
 import pascal.taie.analysis.pta.PointerAnalysisResult;
 import pascal.taie.analysis.pta.core.cs.element.ArrayIndex;
 import pascal.taie.analysis.pta.core.cs.element.CSObj;
 import pascal.taie.analysis.pta.core.cs.element.InstanceField;
 import pascal.taie.analysis.pta.core.cs.element.StaticField;
 import pascal.taie.analysis.pta.core.heap.Obj;
 import pascal.taie.analysis.pta.pts.PointsToSet;
 import pascal.taie.config.AnalysisConfig;
 import pascal.taie.ir.IR;
 import pascal.taie.ir.exp.*;
 import pascal.taie.ir.proginfo.FieldRef;
 import pascal.taie.ir.stmt.*;
 import pascal.taie.language.classes.JField;
 import pascal.taie.language.classes.JMethod;

 import java.util.*;
 import java.util.concurrent.ConcurrentHashMap;
 import java.util.stream.Stream;

 /**
  * Implementation of interprocedural constant propagation for int values.
  */
 public class InterConstantPropagation extends
         AbstractInterDataflowAnalysis<JMethod, Stmt, CPFact> {

     public static final String ID = "inter-constprop";

     private final ConstantPropagation cp;

     private Stream<InstanceField> instanceFieldStream;

     private Stream<ArrayIndex> arrayIndexStream;

     private Stream<StaticField> staticFieldStream;

     private PointerAnalysisResult pta;

     //private ConcurrentHashMap<FieldRef, Value> instanceFieldRefMap = new ConcurrentHashMap<>();
     //PointerAnalysisResult pta;

     private ConcurrentHashMap<InstanceFieldAccess,Value> instanceToValue = new ConcurrentHashMap<>();
     private ConcurrentHashMap<FieldRef,Value> staticFieldRef = new ConcurrentHashMap<>();
     private ConcurrentHashMap<ArrayAccess,Value> arrayToValue = new ConcurrentHashMap<>();

     //Var和Value的hashmap
     private ConcurrentHashMap<Var,Value> params = new ConcurrentHashMap<>();

     public InterConstantPropagation(AnalysisConfig config) {
         super(config);
         cp = new ConstantPropagation(new AnalysisConfig(ConstantPropagation.ID));
     }

     @Override
     protected void initialize() {
         String ptaId = getOptions().getString("pta");
         //PointerAnalysisResult pta = World.getResult(ptaId);
         pta = World.getResult(ptaId);
         // You can do initialization work here
         instanceFieldStream = pta.instanceFields();
         arrayIndexStream = pta.arrayIndexes();
         staticFieldStream = pta.staticFields();

         instanceFieldStream.forEach(instanceField -> {
             Object obj = instanceField.getBase().getObject();
             System.out.println(instanceField);

         });
         staticFieldStream.forEach(staticField -> {
             JField jField = staticField.getField();
             //这个是用来干嘛的？
             Set<Obj> ObjSet = pta.getPointsToSet(jField);
             for(Obj obj: ObjSet){
                 System.out.println(obj);
             }
         });

     }


     @Override
     public boolean isForward() {
         return cp.isForward();
     }

     @Override
     public CPFact newBoundaryFact(Stmt boundary) {
         IR ir = icfg.getContainingMethodOf(boundary).getIR();
         return cp.newBoundaryFact(ir.getResult(CFGBuilder.ID));
     }

     @Override
     public CPFact newInitialFact() {
         return cp.newInitialFact();
     }

     @Override
     public void meetInto(CPFact fact, CPFact target) {
         cp.meetInto(fact, target);
     }

     @Override
     protected boolean transferCallNode(Stmt stmt, CPFact in, CPFact out) {
         // TODO - finish me
         CPFact tmpFact = new CPFact();
         tmpFact.copyFrom(in);
         return out.copyFrom(tmpFact);
     }

     @Override
     protected boolean transferNonCallNode(Stmt stmt, CPFact in, CPFact out) {
         // TODO - finish me

         /*
         //y=x.f这样
         if(stmt instanceof LoadField){
             LoadField loadField = (LoadField) stmt;
             LValue lVal = loadField.getLValue();


         }
         //x.f=y
         else if(stmt instanceof StoreField){
             StoreField storeField = (StoreField) stmt;
             //我想把instanceField存的值都用map保存

         }*/


         if(stmt instanceof New){
             New newStmt = (New) stmt;

             LValue lValue = newStmt.getLValue();

             if(lValue instanceof Var){
                 //new 了一个 x
                 Var var = (Var) lValue;
                 List<LoadField> loadFieldList = var.getLoadFields();
                 List<StoreField> storeFieldList = var.getStoreFields();
                 Set xPts = pta.getPointsToSet(var);
                 //y=x.f
                 for(LoadField loadField : loadFieldList){
                     FieldRef fieldRef = loadField.getFieldRef();

                 }
                //x.f=y
                for(StoreField storeField : storeFieldList){
                    FieldRef fieldRef = storeField.getFieldRef();

                }

             }
         }
         /*else if(stmt instanceof DefinitionStmt){
             DefinitionStmt defStmt = (DefinitionStmt) stmt;
             LValue lValue = defStmt.getLValue();
             if(lValue instanceof Var){
                Var var = (Var) lValue;

             }
         }*/
         //x.f = y
         else if(stmt instanceof StoreField) {
             //静态变量 存储进hashmap
             StoreField storeField = (StoreField) stmt;
             if (storeField.isStatic()) {
                 //TODO 这里return什么呢？
                FieldRef fieldRef = storeField.getFieldRef();
                Var rVar = storeField.getRValue();
                if(staticFieldRef.containsKey(fieldRef)){
                    Value v1 = staticFieldRef.get(fieldRef);
                    Value v2 = in.get(rVar);
                    if(params.containsKey(rVar))
                        v2 = params.get(rVar);
                    staticFieldRef.put(fieldRef,cp.meetValue(v1,v2));
                }else{
                    //TODO 这里可能有问题 rVar 可能为null或者怎么的
                    if(rVar!=null) {
                        Value v = in.get(rVar);
                        if(params.containsKey(rVar))
                            v = params.get(rVar);
                        staticFieldRef.put(fieldRef, v);
                    }
                }
             } else {
                /*
                 Var rVar = storeField.getRValue();
                 if (!instanceFieldRefMap.containsKey(storeField.getFieldRef())) {
                     instanceFieldRefMap.put(storeField.getFieldRef(), in.get(rVar));
                 } else {
                     Value value1 = instanceFieldRefMap.get(storeField.getFieldRef());
                     Value value2 = in.get(rVar);
                     instanceFieldRefMap.put(storeField.getFieldRef(), cp.meetValue(value1, value2));
                 }*/
                 //x.f = y
                 InstanceFieldAccess instanceFieldAccess = (InstanceFieldAccess) storeField.getFieldAccess();
                 var rvar = storeField.getRValue();
                 if(rvar!=null){
                     boolean flag = false;
                     for(Map.Entry entry : instanceToValue.entrySet()){
                         InstanceFieldAccess key = (InstanceFieldAccess) entry.getKey();
                         Value val = (Value) entry.getValue();
                         flag = isInstanceAlias(key.getBase(),key.getFieldRef(),instanceFieldAccess.getBase(),instanceFieldAccess.getFieldRef());
                         if(flag){
                             Value v1 = instanceToValue.get(instanceFieldAccess);

                             Value v2 = in.get(rvar);
                             if(params.containsKey(rvar))
                                 v2 = params.get(rvar);
                             if(v1==null) v1=v2;
                             Value v = cp.meetValue(cp.meetValue(v1,v2),val);
                             instanceToValue.put(instanceFieldAccess,v);
                         }
                     }
                     if(flag==false){
                         Value v = in.get(rvar);
                         if(params.containsKey(rvar)){
                             v = params.get(rvar);
                         }
                         instanceToValue.put(instanceFieldAccess,v);
                     }
                 }
             }
         }
         //y = x.f
         else if(stmt instanceof LoadField) {
             LoadField loadField = (LoadField) stmt;
             LValue lVal = loadField.getLValue();
             if (loadField.isStatic()) {
                 if (lVal instanceof Var) {
                     Var var = (Var) lVal;
                     boolean changed = false;
                     for (Var inVar : in.keySet()) {
                         if (!inVar.equals(var)) {
                             if(in.get(inVar)!=null)
                                changed |= out.update(inVar, in.get(inVar));
                         }
                     }

                     if (cp.canHoldInt(var)) {
                         FieldRef fieldRef = loadField.getFieldRef();
                         Value tmpVar = staticFieldRef.get(fieldRef);

                         //Value tmp = fieldAccessMap.get(loadField.getRValue());
                         //这里获取不到是因为fieldAccess不是同一个。
                         if(tmpVar!=null)
                         changed |= out.update(var, tmpVar);
                     }
                     return changed;
                 }
             } else {
                 /*
                 if (lVal instanceof Var) {
                     Var var = (Var) lVal;
                     boolean changed = false;
                     for (Var inVar : in.keySet()) {
                         if (!inVar.equals(var)) {
                             changed |= out.update(inVar, in.get(inVar));
                         }
                     }

                     if (cp.canHoldInt(var)) {
                         //FieldAccess tmpAc = loadField.getRValue();

                         FieldRef fieldRef = loadField.getFieldRef();
                         Value tmp = instanceFieldRefMap.get(fieldRef);
                         //这里获取不到是因为fieldAccess不是同一个。
                         changed |= out.update(var, tmp);
                     }
                     return changed;
                 }
                */
                 //y=x.f
                 if(lVal instanceof Var){
                     Var var = (Var) lVal;
                     boolean changed = false;
                     for (Var inVar : in.keySet()) {
                         if (!inVar.equals(var)) {
                             if(in.get(inVar)!=null)
                             changed |= out.update(inVar, in.get(inVar));
                         }
                     }

                     if (cp.canHoldInt(var)) {
                         InstanceFieldAccess instanceFieldAccess = (InstanceFieldAccess) loadField.getFieldAccess();
                         Value tmpValue = Value.getUndef();
                         Value v =null;
                         for(Map.Entry entry : instanceToValue.entrySet()){
                             InstanceFieldAccess key = (InstanceFieldAccess) entry.getKey();
                             Value val = (Value) entry.getValue();
                             boolean flag = isInstanceAlias(key.getBase(), key.getFieldRef(),instanceFieldAccess.getBase(),instanceFieldAccess.getFieldRef());
                             if(flag){
                                 if(v==null)
                                     v=val;
                                 else{
                                     v=cp.meetValue(v,val);
                                 }
                             }
                         }
                         if(v!=null)
                             tmpValue = v;
                         if(tmpValue!=null)
                         changed |= out.update(var, tmpValue);
                     }
                     return changed;
                 }
             }
         }
         //a[i] = x
         //TODO 我的处理方式是map存储数组和它对应的值
         else if(stmt instanceof StoreArray){
            StoreArray storeArray = (StoreArray) stmt;
            ArrayAccess arrayAccess = storeArray.getArrayAccess();
            Var rvar = storeArray.getRValue();


                if(rvar!=null){
                    //TODO 如果是别名的话应该都需要变

                    boolean flag=false;
                    for(Map.Entry entry:arrayToValue.entrySet()){
                        //如果键值都相等
                        //if(entry.getKey().equals(arrayAccess.getBase())&&entry.getValue().equals(arrayAccess.getIndex())){
                            /*
                            flag=true;
                            Value v1 = arrayToValue.get(arrayAccess);
                            Value v2 = in.get(rvar);
                            arrayToValue.put(arrayAccess,cp.meetValue(v1,v2));
                             */
                            ArrayAccess key = (ArrayAccess) entry.getKey();
                            Value val = (Value) entry.getValue();
                            /*
                            if(params.containsKey(key.getIndex())){
                                flag = isArrAlias(key.getBase(),params.get(key.getIndex()),arrayAccess.getBase(),in.get(arrayAccess.getIndex()));
                            }

                            if(params.containsKey(arrayAccess.getIndex())){
                                flag = isArrAlias(key.getBase(),in.get(key.getIndex()),arrayAccess.getBase(),params.get(arrayAccess.getIndex()));
                            }
                            else {
                                flag = isArrAlias(key.getBase(), in.get(key.getIndex()), arrayAccess.getBase(), in.get(arrayAccess.getIndex()));
                            }*/

                        Value value1 = in.get(key.getIndex());
                        Value value2 = in.get(arrayAccess.getIndex());
                        if(params.containsKey(key.getIndex())){
                            value1 = params.get(key.getIndex());
                        }
                        if(params.containsKey(arrayAccess.getIndex())){
                            value2 = params.get(arrayAccess.getIndex());
                        }
                        flag = isArrAlias(key.getBase(),value1,arrayAccess.getBase(),value2);


                        //flag = isArrAlias(key.getBase(), in.get(key.getIndex()), arrayAccess.getBase(), in.get(arrayAccess.getIndex()));
                            if(flag){
                                Value v1 = arrayToValue.get(arrayAccess);
                                Value v2 = in.get(rvar);
                                if(params.containsKey(rvar))
                                    v2 = params.get(rvar);
                                Value v = cp.meetValue(cp.meetValue(v1,v2),val);
                                arrayToValue.put(arrayAccess,v);
                                //arrayToValue.put(key,v);
                            }
                        //}
                    }
                    if(flag==false){
                        Value v = in.get(rvar);
                        if(params.containsKey(rvar))
                            v = params.get(rvar);
                        arrayToValue.put(arrayAccess,v);
                    }

                }
            }


         // x = a[i]
         //TODO 遇到load，去hashmap里面找别名进行处理
         else if(stmt instanceof LoadArray){
            LoadArray loadArray = (LoadArray) stmt;
            LValue lVal = loadArray.getLValue();

            if(lVal instanceof Var){
                Var var = (Var) lVal;
                boolean changed = false;
                for (Var inVar : in.keySet()) {
                    if (!inVar.equals(var)) {
                        if(in.get(inVar)!=null)
                        changed |= out.update(inVar, in.get(inVar));
                    }
                }

                if (cp.canHoldInt(var)) {
                    //这里通过别名去找value
                    ArrayAccess arrayAccess = loadArray.getArrayAccess();
                    //Value tmpValue = arrayToValue.get(arrayAccess);
                    Value tmpValue = Value.getUndef();
                    Value v = null;
                    for(Map.Entry entry : arrayToValue.entrySet()){
                        ArrayAccess key = (ArrayAccess) entry.getKey();
                        Value val = (Value) entry.getValue();
                        //TODO 是因为换了函数 in不一样了，因此会出现undefined的情况
                        boolean flag=false;
                        Value v1 = in.get(key.getIndex());
                        Value v2 = in.get(arrayAccess.getIndex());
                        if(params.containsKey(key.getIndex())){
                            v1 = params.get(key.getIndex());
                        }
                        if(params.containsKey(arrayAccess.getIndex())){
                            v2 = params.get(arrayAccess.getIndex());
                        }
                        flag = isArrAlias(key.getBase(),v1,arrayAccess.getBase(),v2);
                        if(flag){
                            if(v==null)
                                v=val;
                            else{
                                v=cp.meetValue(v,val);
                            }
                            //tmpValue = val;
                        }
                    }
                    if(v!=null)
                        tmpValue = v;
                    if(tmpValue!=null)
                    changed |= out.update(var, tmpValue);
                }
                return changed;
            }

         }

         else{return cp.transferNode(stmt,in,out);}
         return out.copyFrom(in);
     }

     @Override
     protected CPFact transferNormalEdge(NormalEdge<Stmt> edge, CPFact out) {
         // TODO - finish me
         CPFact tmpFact = new CPFact();
         tmpFact.copyFrom(out);
         return tmpFact;
     }

     @Override
     protected CPFact transferCallToReturnEdge(CallToReturnEdge<Stmt> edge, CPFact out) {
         // TODO - finish me
         Stmt source = edge.getSource();
         Stmt target = edge.getTarget();
         //左边存在。。。
         if(source.getDef().isPresent()) {
             LValue lValue = source.getDef().get();
             Var xValue = null;
             if(lValue instanceof  Var)
                 xValue = (Var) lValue;
             CPFact tmpFact = new CPFact();
             tmpFact.copyFrom(out);
             tmpFact.remove(xValue);
             return tmpFact;
         }else{
             //左边不存在
             CPFact tmpFact = new CPFact();
             tmpFact.copyFrom(out);
             return tmpFact;
         }
     }

     @Override
     protected CPFact transferCallEdge(CallEdge<Stmt> edge, CPFact callSiteOut) {
         // TODO - finish me
         //TODO question: 这里对吗
         List<Var> methodParams = edge.getCallee().getIR().getParams();
         //List<RValue> useParams = edge.getSource().getUses();
         //edge.getSource().
         Stmt src = edge.getSource();

         CPFact tmpFact = new CPFact();
         /*
         if(methodParams.size() != useParams.size()){
             System.out.println("Error : params is not the same, CallEdge is wrong!");
         }*/
         //TODO 这里可能要instance of
         //int count = useParams.size()-methodParams.size();
         for(int i = 0; i < methodParams.size(); ++i){
             Value v = callSiteOut.get((Var)((Invoke)src).getInvokeExp().getArg(i));
             //传入的参数成了undef

             Set<Obj> pts = pta.getPointsToSet(((Invoke)src).getInvokeExp().getArg(i));
             Set<Obj> pts1 = pta.getPointsToSet(methodParams.get(i));

             tmpFact.update(methodParams.get(i), callSiteOut.get((Var)((Invoke)src).getInvokeExp().getArg(i)));
             params.put(methodParams.get(i),callSiteOut.get((Var)((Invoke)src).getInvokeExp().getArg(i)));
             //count++;
         }
         return tmpFact;
     }

     @Override
     protected CPFact transferReturnEdge(ReturnEdge<Stmt> edge, CPFact returnOut) {
         // TODO - finish me
         Stmt callsite = edge.getCallSite();
         if(!(callsite instanceof Invoke)){
             System.out.println("callsite not Invoke");
             return new CPFact();
         }

         Var LHS = ((Invoke) callsite).getLValue();
         if(LHS == null) return new CPFact();
         CPFact result = new CPFact();
         result.update(LHS, Value.getUndef());

         edge.returnVars().forEach(returnvar -> {
             Value current = result.get(LHS);
             current = cp.meetValue(returnOut.get(returnvar), current);
             result.update(LHS, current);
         });
         return result;
     }

     public boolean isOverlap(Set<Obj> s1, Set<Obj> s2){
         for(Obj obj1 : s1){
             if(s2.contains(obj1)){
                 return true;
             }
         }
         return false;
     }

     public boolean isInstanceAlias(Var base1,FieldRef f1, Var base2,FieldRef f2){
         Set s1 = pta.getPointsToSet(base1);
         Set s2 = pta.getPointsToSet(base2);
         if(isOverlap(s1,s2)&&f1.equals(f2)){
             return true;
         }
         return false;
     }

     public boolean isArrAlias(Var base1,Value index1,Var base2, Value index2){
         Set s1 = pta.getPointsToSet(base1);
         Set s2 = pta.getPointsToSet(base2);
         if(isOverlap(s1,s2)){
             if(index1.isUndef()||index2.isUndef()){
                 return false;
             }
             if(index1.isNAC() || index2.isNAC()){
                 return true;
             }
             //TODO 这里的equals对不对
             if(index1.equals(index2)){
              //if(index1.isConstant()&&index2.isConstant()&&(index1.getConstant()== index2.getConstant())){
                return true;
             }
         }
         return false;
     }

 }
