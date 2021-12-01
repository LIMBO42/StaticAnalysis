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

package pascal.taie.analysis.pta.ci;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.CallGraphs;
import pascal.taie.analysis.graph.callgraph.CallKind;
import pascal.taie.analysis.graph.callgraph.DefaultCallGraph;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.proginfo.MethodRef;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;
import pascal.taie.util.AnalysisException;
import pascal.taie.language.type.Type;

import java.lang.reflect.Method;
import java.util.*;
import java.util.concurrent.ConcurrentLinkedDeque;

class Solver {

    private static final Logger logger = LogManager.getLogger(Solver.class);

    private final HeapModel heapModel;

    private DefaultCallGraph callGraph;

    private PointerFlowGraph pointerFlowGraph;

    private WorkList workList;

    private StmtProcessor stmtProcessor;

    private ClassHierarchy hierarchy;

    //private Set<JMethod> RM;



    //private ConcurrentLinkedDeque RM;
    private ConcurrentLinkedDeque S;


    Solver(HeapModel heapModel) {
        this.heapModel = heapModel;
    }

    /**
     * Runs pointer analysis algorithm.
     */
    void solve() {
        initialize();
        analyze();
    }

    /**
     * Initializes pointer analysis.
     */
    private void initialize() {
        workList = new WorkList();
        pointerFlowGraph = new PointerFlowGraph();
        callGraph = new DefaultCallGraph();
        stmtProcessor = new StmtProcessor();
        hierarchy = World.getClassHierarchy();

        S = new ConcurrentLinkedDeque();

        // initialize main method
        JMethod main = World.getMainMethod();
        callGraph.addEntryMethod(main);
        addReachable(main);
    }

    /**
     * Processes new reachable method.
     */

    //question: 这边需要调用solver.resolveCallee?
    private void addReachable(JMethod method) {
        // TODO - finish me
        //ConcurrentLinkedDeque<Stmt> Sm; Sm = new ConcurrentLinkedDeque<>();
        if(!callGraph.contains(method)){
            // add m to RM
            callGraph.addReachableMethod(method);
            //S U= Sm
            List<Stmt> stmtList = method.getIR().getStmts();
            System.out.println("--------mthod:--------");
            for(Stmt stmt:stmtList){
                //Sm.add(stmt);
                S.add(stmt);
                System.out.println(stmt);
            }
            System.out.println("--------mthod:--------");
            //for each

            //for(Stmt stmt: method.getIR()){
            method.getIR().forEach(stmt -> {
                //question 这些stmt的时候需要加入pt吗
                if(stmt instanceof New){
                    stmtProcessor.visit((New) stmt);
                }else if(stmt instanceof Copy){
                    stmtProcessor.visit((Copy) stmt);
                }else if(stmt instanceof StoreField && ((StoreField) stmt).isStatic()){
                    stmtProcessor.visit((StoreField) stmt);
                }else if(stmt instanceof LoadField && ((LoadField) stmt).isStatic()){
                    stmtProcessor.visit((LoadField) stmt);
                }else if(stmt instanceof Invoke && ((Invoke) stmt).isStatic()){
                    stmtProcessor.visit((Invoke) stmt);
                }
            });
        }
        //Sm.clear();
    }

    /**
     * Processes statements in new reachable methods.
     */
    private class StmtProcessor implements StmtVisitor<Void> {
        // TODO - if you choose to implement addReachable()
        //  via visitor pattern, then finish me
        @Override
        public Void visit(New stmt){
            //get x
            LValue lValue = stmt.getLValue();

            VarPtr varPtr = pointerFlowGraph.getVarPtr((Var) lValue);
            //get new T

            //PointsToSet pointsToSet = varPtr.getPointsToSet();
            PointsToSet pointsToSet = new PointsToSet();
            Obj obj = heapModel.getObj(stmt);
            pointsToSet.addObject(obj);
            //add x,{Oi}
            workList.addEntry(varPtr,pointsToSet);
            System.out.println("visit new: "+varPtr+" "+pointsToSet);


            return null;
        }

        @Override
        public Void visit(Copy stmt) {
            LValue lValue = stmt.getLValue();
            RValue rValue = stmt.getRValue();

            VarPtr x = pointerFlowGraph.getVarPtr((Var) lValue);
            VarPtr y = pointerFlowGraph.getVarPtr((Var) rValue);
            // x = y
            //addEdge(y,x)
            addPFGEdge(y,x);

            return null;
        }

        @Override
        public Void visit(StoreField stmt) {
            if(stmt.isStatic()) {
                //T.f
                JField field = stmt.getFieldRef().resolve();
                StaticField staticField = pointerFlowGraph.getStaticField(field);

                //question 这里能转换吗？

                RValue rValue = stmt.getRValue();

                VarPtr y = pointerFlowGraph.getVarPtr((Var) rValue);
                //T.f = y
                //addEdge(y,T.f)
                addPFGEdge(y, staticField);

                return null;
            }
            return null;

        }



        @Override
        public Void visit(LoadField stmt) {
            if(stmt.isStatic()) {
                //T.f
                JField field = stmt.getFieldRef().resolve();

                StaticField staticField = pointerFlowGraph.getStaticField(field);
                //y
                LValue lValue = stmt.getLValue();

                VarPtr y = pointerFlowGraph.getVarPtr((Var) lValue);
                //y = T.f
                //addEdge(T.f,y)
                addPFGEdge(staticField, y);

                return null;
            }
            return null;
        }



        @Override
        public Void visit(Invoke stmt) {
            if(stmt.isStatic()) {
                //getMethodRef.resolve获得是形参
                //invoke exp获得的是实参
                //应该是实参指向形参

                //加边
                //resolveCallee(null,stmt).getIR().getParams()
                JMethod callee = resolveCallee(null, stmt);
                if (stmt.getInvokeExp().getArgCount() != callee.getParamCount()) {
                    System.out.println("visit Invoke error!");
                }

                //VarPtr mThis = pointerFlowGraph.getVarPtr(callee.getIR().getThis());
                /*
                PointsToSet pointsToSet = new PointsToSet();
                pointsToSet.addObject();
                workList.addEntry();*/

                //if (!callGraph.hasEdge(, callee)) {
                CallKind kind = CallKind.STATIC;
                Edge newEdge = new Edge(kind, stmt, callee);
                if (callGraph.addEdge(newEdge)) {
                    //callGraph.addReachableMethod(callee);
                    addReachable(callee);
                    for (int i = 0; i < stmt.getInvokeExp().getArgCount(); i++) {
                        //question:
                        //var是实参
                        Var var = stmt.getInvokeExp().getArg(i);

                        VarPtr varPtr = pointerFlowGraph.getVarPtr(var);
                        //这个应该是形参
                        Var targetVar = callee.getIR().getParam(i);
                        VarPtr varPtrTarget = pointerFlowGraph.getVarPtr(targetVar);
                        addPFGEdge(varPtr, varPtrTarget);

                    }
                    List<Var> varList = callee.getIR().getReturnVars();
                    Var r = stmt.getResult();
                    if (r != null) {
                        VarPtr rPtr = pointerFlowGraph.getVarPtr(r);
                        //questions
                        for (Var var : varList) {
                            VarPtr mRet = pointerFlowGraph.getVarPtr(var);
                            addPFGEdge(mRet, rPtr);
                        }
                        return null;
                    }
                }
            }
            //}
            return null;
        }

        @Override
        public Void visit(LoadArray stmt) {
            //arrayLoad

            //y=x[i]

            //y
            LoadArray loadArray = stmt;
            LValue lValue = loadArray.getLValue();

            VarPtr y = pointerFlowGraph.getVarPtr((Var) lValue);
            //x[i]
            ArrayAccess arrayAccess = loadArray.getArrayAccess();

            ArrayIndex arrayIndex = pointerFlowGraph.getArrayIndex((Obj)arrayAccess.getBase());
            addPFGEdge(arrayIndex, y);

            return null;
        }

        @Override
        public Void visit(StoreArray stmt) {
            //arrayStore
            StoreArray arrayStore = stmt;

            //x[i]=y

            //x[i]
            ArrayAccess arrayAccess = arrayStore.getLValue();

            ArrayIndex arrayIndex = pointerFlowGraph.getArrayIndex((Obj) arrayAccess.getBase());
            //y
            RValue rValue = arrayStore.getRValue();

            VarPtr y = pointerFlowGraph.getVarPtr((Var)rValue);
            addPFGEdge(y, arrayIndex);

            return null;
        }
    }

    /**
     * Adds an edge "source -> target" to the PFG.
     */
    private void addPFGEdge(Pointer source, Pointer target) {
        // TODO - finish me
        final boolean[] flag = {false};
        //找后继,如果后继为相依的值
        pointerFlowGraph.succsOf(source).forEach(succ->{
            if(succ.equals(target)){
            //if(succ==target){
                flag[0] =true;
            }
        });
        //不属于
        if(flag[0]==false){
            pointerFlowGraph.addEdge(source,target);
            if(!source.getPointsToSet().isEmpty()){
                workList.addEntry(target,source.getPointsToSet());
            }
        }
    }

    /**
     * Processes work-list entries until the work-list is empty.
     */
    private void analyze() {
        // TODO - finish me
        while(!workList.isEmpty()){

            WorkList.Entry entry = workList.pollEntry();
            if(entry==null){
                System.out.println("error in analyze!");
            }

            //propagate(n,delta);
            PointsToSet delta;
            delta = propagate(entry.pointer, entry.pointsToSet);
            // propagate(entry.pointer,delta);

            //如果是一个变量x
            if(entry.pointer instanceof VarPtr){

                delta.forEach(o->{

                    Var var = ((VarPtr) entry.pointer).getVar();

                    var.getLoadArrays().forEach(stmt->{
                        //y=x[i]
                        //y
                        LValue lValue = stmt.getLValue();
                        VarPtr y = pointerFlowGraph.getVarPtr((Var) lValue);
                        //x[i]
                        ArrayAccess arrayAccess = stmt.getArrayAccess();
                        ArrayIndex arrayIndex = pointerFlowGraph.getArrayIndex(o);
                        addPFGEdge(arrayIndex, y);
                    });

                    var.getStoreArrays().forEach(stmt->{
                        //x[i]
                        ArrayAccess arrayAccess = stmt.getLValue();

                        ArrayIndex arrayIndex = pointerFlowGraph.getArrayIndex(o);

                        //y
                        RValue rValue = stmt.getRValue();

                        VarPtr y = pointerFlowGraph.getVarPtr((Var)rValue);
                        addPFGEdge(y, arrayIndex);
                    });

                    var.getStoreFields().forEach(stmt->{
                        //y=x.f
                        //x.f
                        JField field = stmt.getFieldRef().resolve();

                        InstanceField instanceField = pointerFlowGraph.getInstanceField(o, field);

                        RValue rValue = stmt.getRValue();

                        VarPtr y = pointerFlowGraph.getVarPtr((Var) rValue);
                        addPFGEdge(y, instanceField);
                    });

                    var.getLoadFields().forEach(stmt->{
                        //x.f
                        JField field = stmt.getFieldRef().resolve();
                        InstanceField instanceField = pointerFlowGraph.getInstanceField(o, field);

                        //y
                        LValue lValue = stmt.getLValue();

                        VarPtr y = pointerFlowGraph.getVarPtr((Var) lValue);
                        addPFGEdge(instanceField, y);
                    });

                    /*
                    S.forEach(stmt0->{
                        if(stmt0 instanceof LoadField){
                            LoadField stmt = (LoadField) stmt0;
                            //x.f
                            JField field = stmt.getFieldRef().resolve();
                            InstanceField instanceField = pointerFlowGraph.getInstanceField(o, field);

                            //y
                            LValue lValue = stmt.getLValue();

                            VarPtr y = pointerFlowGraph.getVarPtr((Var) lValue);
                            addPFGEdge(instanceField, y);
                        }else if(stmt0 instanceof StoreField) {
                            StoreField stmt = (StoreField) stmt0;
                            //y=x.f
                            //x.f
                            JField field = stmt.getFieldRef().resolve();

                            InstanceField instanceField = pointerFlowGraph.getInstanceField(o, field);

                            RValue rValue = stmt.getRValue();

                            VarPtr y = pointerFlowGraph.getVarPtr((Var) rValue);
                            addPFGEdge(y, instanceField);
                        }else if(stmt0 instanceof LoadArray){
                            LoadArray stmt = (LoadArray) stmt0;
                            //y=x[i]
                            //y
                            LValue lValue = stmt.getLValue();
                            VarPtr y = pointerFlowGraph.getVarPtr((Var) lValue);
                            //x[i]
                            ArrayAccess arrayAccess = stmt.getArrayAccess();
                            ArrayIndex arrayIndex = pointerFlowGraph.getArrayIndex(o);
                            addPFGEdge(arrayIndex, y);
                        }else if(stmt0 instanceof StoreArray){
                            StoreArray stmt = (StoreArray) stmt0;
                            //x[i]
                            ArrayAccess arrayAccess = stmt.getLValue();

                            ArrayIndex arrayIndex = pointerFlowGraph.getArrayIndex(o);

                            //y
                            RValue rValue = stmt.getRValue();

                            VarPtr y = pointerFlowGraph.getVarPtr((Var)rValue);
                            addPFGEdge(y, arrayIndex);
                        }
                    });*/
                    processCall(var, o);
                });


            }
        }
    }

    /**
     * Propagates pointsToSet to pt(pointer) and its PFG successors,
     * returns the difference set of pointsToSet and pt(pointer).
     */
    private PointsToSet propagate(Pointer pointer, PointsToSet pointsToSet) {
        // TODO - finish me
        //参数是n和pts
        PointsToSet ptn = pointer.getPointsToSet();
        PointsToSet delta = new PointsToSet();

        for(Obj obj : pointsToSet){
            if(ptn.addObject(obj)){
                delta.addObject(obj);
            }
        }
        if(!delta.isEmpty()){
            //看后继 是否有 n->s的线
            pointerFlowGraph.succsOf(pointer).forEach(s->{
                //worklist add (s,pts)
                workList.addEntry(s,delta);
            });
        }
        //计算delta pts-ptn

        /*
        pointsToSet.forEach(point->{
            final boolean[] flag = {false};
            //遍历ptn看有无相同的，如果有相同的，就不加入
            ptn.forEach(point2->{
                if(point.equals(point2)){
                //if(point==point2){
                    flag[0] =true;
                }
            });
            //不相同的加入
            if(flag[0]==false){
                delta.addObject(point);
            }
        });
        //这里是delta

        if(!delta.isEmpty()) {
            //ptn = ptn U pts
            delta.forEach(p->{
                ptn.addObject(p);
            });
            //看后继 是否有 n->s的线
            pointerFlowGraph.succsOf(pointer).forEach(s->{
                //worklist add (s,pts)
                workList.addEntry(s,delta);
            });
        }
        */

        return delta;
    }

    /**
     * Processes instance calls when points-to set of the receiver variable changes.
     *
     * @param var the variable that holds receiver objects
     * @param recv a new discovered object pointed by the variable.
     */
    private void processCall(Var var, Obj recv) {
        // TODO - finish me
        //
        //var.getInvokes().forEach(stmt->{
        System.out.println(var);

        var.getInvokes().forEach(invoke-> {
            //if(stmt instanceof Invoke && !((Invoke) stmt).isStatic()) {
                //Invoke invoke = (Invoke) stmt;

                //  问题在这
                //JMethod m = resolveCallee(recv, invoke);
                //JMethod jMethod = resolveCallee(recv,invoke);
                //JMethod m = hierarchy.dispatch(recv.getType(), invoke.getMethodRef());
                JMethod m = resolveCallee(recv, invoke);
                //JMethod m = hierarchy.dispatch(recv.getType(), var.getMethod().getRef());

                if (m != null) {
                    if (invoke.isInterface() || invoke.isSpecial()) {
                        m = resolveCallee(recv, invoke);
                    }

                    VarPtr mThis = pointerFlowGraph.getVarPtr(m.getIR().getThis());
                    if(var.isTempConst()){
                        System.out.println(var);
                    }
                    //PointsToSet pointsToSet = mThis.getPointsToSet();
                    PointsToSet pointsToSet = new PointsToSet();
                    pointsToSet.addObject(recv);
                    //add {Mthis,{o}}
                    workList.addEntry(mThis, pointsToSet);

                    //question
                    JMethod jMethod = invoke.getMethodRef().resolve();
                    JMethod tmpMethod = invoke.getContainer();

                    //问题！
                    //
                    //if (!callGraph.hasEdge(callGraph.getContainerMethodOf(invoke), m)) {
                        CallKind kind = CallKind.OTHER;
                        if (invoke.isDynamic()) {
                            kind = CallKind.DYNAMIC;
                        } else if (invoke.isSpecial()) {
                            kind = CallKind.SPECIAL;
                        } else if (invoke.isInterface()) {
                            kind = CallKind.INTERFACE;
                        } else if (invoke.isVirtual()) {
                            kind = CallKind.VIRTUAL;
                        } else if (invoke.isStatic()) {
                            kind = CallKind.STATIC;
                        }
                        Edge newEdge = new Edge(kind, invoke, m);
                        //callGraph.addEdge(newEdge);
                    if(callGraph.addEdge(newEdge)){
                        addReachable(m);

                        if (invoke.getInvokeExp().getArgCount() != m.getParamCount()) {
                            System.out.println("ProcessCall error!");
                        }
                        for (int i = 0; i < invoke.getInvokeExp().getArgCount(); i++) {
                            //L:
                            //实参
                            Var v = invoke.getInvokeExp().getArg(i);

                            VarPtr varPtr = pointerFlowGraph.getVarPtr(v);
                            //method
                            Var targetV = m.getIR().getParam(i);

                            VarPtr varPtrTarget = pointerFlowGraph.getVarPtr(targetV);
                            addPFGEdge(varPtr, varPtrTarget);
                        }
                        List<Var> varList = m.getIR().getReturnVars();
                        Var r = invoke.getResult();

                        if (r != null) {
                            VarPtr rPtr = pointerFlowGraph.getVarPtr(r);
                            for (Var var1 : varList) {

                                VarPtr mRet = pointerFlowGraph.getVarPtr(var1);
                                addPFGEdge(mRet, rPtr);
                            }
                        }
                    }
                    //});
                    //}
                }
            //}
        });
    }

    /**
     * Resolves the callee of a call site with the receiver object.
     *
     * @param recv     the receiver object of the method call. If the callSite
     *                 is static, this parameter is ignored (i.e., can be null).
     * @param callSite the call site to be resolved.
     * @return the resolved callee.
     */
    private JMethod resolveCallee(Obj recv, Invoke callSite) {
        Type type = recv != null ? recv.getType() : null;
        return CallGraphs.resolveCallee(type, callSite);
    }

    CIPTAResult getResult() {
        return new CIPTAResult(pointerFlowGraph, callGraph);
    }
}
