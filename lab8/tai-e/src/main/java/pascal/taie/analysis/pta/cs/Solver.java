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

package pascal.taie.analysis.pta.cs;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.CallGraph;
import pascal.taie.analysis.graph.callgraph.CallGraphs;
import pascal.taie.analysis.graph.callgraph.CallKind;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.PointerAnalysisResultImpl;
import pascal.taie.analysis.pta.core.cs.CSCallGraph;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.element.ArrayIndex;
import pascal.taie.analysis.pta.core.cs.element.CSCallSite;
import pascal.taie.analysis.pta.core.cs.element.CSManager;
import pascal.taie.analysis.pta.core.cs.element.CSMethod;
import pascal.taie.analysis.pta.core.cs.element.CSObj;
import pascal.taie.analysis.pta.core.cs.element.CSVar;
import pascal.taie.analysis.pta.core.cs.element.InstanceField;
import pascal.taie.analysis.pta.core.cs.element.MapBasedCSManager;
import pascal.taie.analysis.pta.core.cs.element.Pointer;
import pascal.taie.analysis.pta.core.cs.element.StaticField;
import pascal.taie.analysis.pta.core.cs.selector.ContextSelector;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.core.heap.MockObj;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.analysis.pta.plugin.taint.TaintAnalysiss;
import pascal.taie.analysis.pta.plugin.taint.TaintFlow;
import pascal.taie.analysis.pta.pts.PointsToSet;
import pascal.taie.analysis.pta.pts.PointsToSetFactory;
import pascal.taie.config.AnalysisOptions;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;
import pascal.taie.util.collection.Maps;
import pascal.taie.util.collection.Sets;

import java.lang.invoke.CallSite;
import java.util.*;
import java.util.stream.Stream;

public class Solver {

    private static final Logger logger = LogManager.getLogger(Solver.class);

    private final AnalysisOptions options;

    private final HeapModel heapModel;

    private final ContextSelector contextSelector;

    private CSManager csManager;

    private CSCallGraph callGraph;

    private PointerFlowGraph pointerFlowGraph;

    private TaintFlowGraph taintFlowGraph;

    private WorkList workList;

    private TaintAnalysiss taintAnalysis;

    private PointerAnalysisResult result;

    private ArrayList<CSMethod> methods = new ArrayList<>();

    Solver(AnalysisOptions options, HeapModel heapModel,
           ContextSelector contextSelector) {
        this.options = options;
        this.heapModel = heapModel;
        this.contextSelector = contextSelector;
    }

    public AnalysisOptions getOptions() {
        return options;
    }

    public ContextSelector getContextSelector() {
        return contextSelector;
    }

    public CSManager getCSManager() {
        return csManager;
    }

    public CSCallGraph getCallGraph(){return callGraph;}

    public ArrayList<CSMethod> getMethods(){return methods;}

    void solve() {
        initialize();
        analyze();
        //analyze();
        taintAnalysis.onFinish();
    }

    private void initialize() {
        csManager = new MapBasedCSManager();
        callGraph = new CSCallGraph(csManager);
        pointerFlowGraph = new PointerFlowGraph();
        taintFlowGraph = new TaintFlowGraph();
        workList = new WorkList();
        taintAnalysis = new TaintAnalysiss(this);
        // process program entry, i.e., main method
        Context defContext = contextSelector.getEmptyContext();
        JMethod main = World.getMainMethod();
        CSMethod csMethod = csManager.getCSMethod(defContext, main);
        callGraph.addEntryMethod(csMethod);
        addReachable(csMethod);
    }

    /**
     * Processes new reachable context-sensitive method.
     */
    private void addReachable(CSMethod csMethod) {
        // TODO - finish me
        methods.add(csMethod);
        if(!callGraph.contains(csMethod)){
            callGraph.addReachableMethod(csMethod);
            /*
            List<Stmt> stmtList = csMethod.getMethod().getIR().getStmts();
            for(Stmt stmt:stmtList){
            }*/
            StmtProcessor stmtProcessor = new StmtProcessor(csMethod);
            csMethod.getMethod().getIR().forEach(stmt->{
                if(stmt instanceof New){
                    stmtProcessor.visit((New) stmt);
                }else if(stmt instanceof Copy){
                    stmtProcessor.visit((Copy) stmt);
                }else if(stmt instanceof StoreField&& ((StoreField) stmt).isStatic()){
                    stmtProcessor.visit((StoreField) stmt);
                }else if(stmt instanceof LoadField&&((LoadField) stmt).isStatic()){
                    stmtProcessor.visit((LoadField) stmt);
                }else if(stmt instanceof Invoke&& ((Invoke) stmt).isStatic()){
                    stmtProcessor.visit((Invoke) stmt);
                }
            });
        }
    }

    public void visitMethod(CSMethod csMethod, Set<TaintFlow> taintFlows) {
        /*
        StmtProcessor stmtProcessor = new StmtProcessor(csMethod);
        csMethod.getMethod().getIR().forEach(stmt-> {
            if(stmt instanceof Invoke&& ((Invoke) stmt).isStatic()){
                stmtProcessor.visit((Invoke) stmt);
            }
        });*/

        Context context = csMethod.getContext();
        csMethod.getMethod().getIR().forEach(stmt -> {
            if(stmt instanceof Invoke && ((Invoke) stmt).isStatic()) {
                for (int i = 0; i < ((Invoke)stmt).getInvokeExp().getArgCount(); ++i) {
                    JMethod callee = resolveCallee(null,(Invoke) stmt);
                    if (taintAnalysis.isSink(callee, i)) {
                        Var var = ((Invoke)stmt).getInvokeExp().getArg(i);
                        CSVar var_ai = csManager.getCSVar(context, var);
                        PointsToSet pointsToSet = var_ai.getPointsToSet();
                        for (CSObj tmp : pointsToSet) {
                            if (taintAnalysis.isTaintObj(tmp.getObject())) {
                                //taintFlows.add(new TaintFlow((Invoke) tmp.getObject().getAllocation(), (Invoke) stmt, i));
                            }
                        }
                    }

                }
            }
        });

    }


    private class TaintFlowGraph {

        /**
         * Map from a pointer (node) to its successors in PFG.
         */
        private final Map<Pointer, Set<Pointer>> successors = Maps.newMap();

        /**
         * Adds an edge (source -> target) to this PFG.
         *
         * @return true if this PFG changed as a result of the call,
         * otherwise false.
         */
        boolean addEdge(Pointer source, Pointer target) {
            return successors.computeIfAbsent(source, p -> Sets.newHybridSet())
                    .add(target);
        }

        /**
         * @return successors of given pointer in the PFG.
         */
        Stream<Pointer> succsOf(Pointer pointer) {
            return successors.getOrDefault(pointer, Set.of()).stream();
        }
    }
    /**
     * Processes the statements in context-sensitive new reachable methods.
     */
    private class StmtProcessor implements StmtVisitor<Void> {

        private final CSMethod csMethod;

        private final Context context;

        private StmtProcessor(CSMethod csMethod) {
            this.csMethod = csMethod;
            this.context = csMethod.getContext();
        }

        // TODO - if you choose to implement addReachable()
        //  via visitor pattern, then finish me
        @Override
        public Void visit(New stmt) {
            Context heapContext = contextSelector.selectHeapContext(csMethod, heapModel.getObj(stmt));
            LValue lValue = stmt.getLValue();
            //x = new T
            CSVar csVar = csManager.getCSVar(context,(Var) lValue);
            Obj obj = heapModel.getObj(stmt);
            CSObj csObj = csManager.getCSObj(heapContext,obj);
            PointsToSet pointsToSet = PointsToSetFactory.make(csObj);
            workList.addEntry(csVar,pointsToSet);

            return null;
        }

        @Override
        public Void visit(Copy stmt) {

            //x = y
            LValue lValue = stmt.getLValue();
            RValue rValue = stmt.getRValue();

            CSVar cslVar = csManager.getCSVar(context,(Var) lValue);
            CSVar csrVar = csManager.getCSVar(context,(Var) rValue);

            addPFGEdge(csrVar,cslVar);

            return null;

        }

        @Override
        public Void visit(LoadField stmt) {

            //T.f
            JField field = stmt.getFieldRef().resolve();
            StaticField staticField = csManager.getStaticField(field);

            //y
            LValue lValue = stmt.getLValue();
            CSVar y = csManager.getCSVar(context,(Var)lValue);

            addPFGEdge(staticField,y);

            return null;
        }

        @Override
        public Void visit(StoreField stmt) {

            JField field = stmt.getFieldRef().resolve();
            StaticField staticField = csManager.getStaticField(field);
            //T.f = y
            RValue rValue = stmt.getRValue();
            CSVar y = csManager.getCSVar(context,(Var)rValue);

            addPFGEdge(y,staticField);

            return null;
        }

        @Override
        public Void visit(Invoke stmt) {

            JMethod callee = resolveCallee(null, stmt);
            //TODO  这里要加进去吗？还有ct的获得没写

            //workList.addEntry(callee.getIR().getThis(),);
            CallKind callKind = CallKind.STATIC;

            CSCallSite csCallSite = csManager.getCSCallSite(context, stmt);
            Context ct = contextSelector.selectContext(csCallSite, callee);
            CSMethod csMethod = csManager.getCSMethod(ct, callee);


            Edge newEdge = new Edge(callKind, csCallSite, csMethod);

            //如果不包含
            if (callGraph.addEdge(newEdge)) {
                addReachable(csMethod);
                for (int i = 0; i < stmt.getInvokeExp().getArgCount(); ++i) {

                    //实参 a1...
                    Var var = stmt.getInvokeExp().getArg(i);
                    CSVar csVar = csManager.getCSVar(context, var);

                    //形参 m...
                    var targetVar = callee.getIR().getParam(i);
                    CSVar csTargetVar = csManager.getCSVar(ct, targetVar);

                    addPFGEdge(csVar, csTargetVar);

                }

                List<Var> varList = callee.getIR().getReturnVars();
                Var r = stmt.getResult();
                if (r != null) {
                    CSVar csVar = csManager.getCSVar(context, r);
                    for (Var var : varList) {
                        CSVar mRet = csManager.getCSVar(ct, var);
                        addPFGEdge(mRet, csVar);
                    }
                }

            }
            //else {


                Var res = stmt.getLValue();
                Type type = stmt.getInvokeExp().getType();
                if (res != null) {
                    //source
                    if (taintAnalysis.isSource(callee, type)) {
                        //确实是Obj，但是Obj需要type和l
                        //Obj obj = t ul
                        Obj obj = taintAnalysis.getTaintObj(stmt, type);
                        CSObj csObj = csManager.getCSObj(taintAnalysis.getEmptyContext(), obj);
                        csManager.getCSVar(context, res).getPointsToSet().addObject(csObj);
                        //workList.addEntry();
                        PointsToSet pointsToSet = PointsToSetFactory.make(csObj);
                        workList.addEntry(csManager.getCSVar(context,res), pointsToSet);
                    }
                    //args to result
                    if (taintAnalysis.isArg2Result(callee, type)) {
                        for (int i = 0; i < stmt.getInvokeExp().getArgCount(); ++i) {
                            //c:ai
                            Var var = stmt.getInvokeExp().getArg(i);
                            CSVar var_ai = csManager.getCSVar(context, var);
                            /*
                            PointsToSet pointsToSet = var_ai.getPointsToSet();
                            for (CSObj tmp : pointsToSet) {
                                if (taintAnalysis.isTaintObj(tmp.getObject())) {
                                    //j, u
                                    Obj obj = taintAnalysis.getTaintObj((Invoke) tmp.getObject().getAllocation(), res.getType());
                                    CSObj csObj = csManager.getCSObj(taintAnalysis.getEmptyContext(), obj);
                                    //c:r
                                    csManager.getCSVar(context, res).getPointsToSet().addObject(csObj);

                                }
                            }*/
                            addPFGEdge(var_ai, csManager.getCSVar(context,res));
                        }
                    }
                }

                /*
                //TODO 这里不用考虑-1 -2吗？
                for (int i = 0; i < stmt.getInvokeExp().getArgCount(); ++i) {

                    if (taintAnalysis.isSink(callee, i)) {
                        Var var = stmt.getInvokeExp().getArg(i);
                        CSVar var_ai = csManager.getCSVar(context, var);
                        PointsToSet pointsToSet = var_ai.getPointsToSet();
                        for (CSObj tmp : pointsToSet) {
                            if (taintAnalysis.isTaintObj(tmp.getObject())) {
                                taintAnalysis.addTaintFlows((Invoke) tmp.getObject().getAllocation(), stmt, i);
                            }
                        }
                    }

                }*/



            //}
            return null;
        }
    }



    /**
     * Adds an edge "source -> target" to the PFG.
     */
    private void addPFGEdge(Pointer source, Pointer target) {
        // TODO - finish me
        final boolean[] flag = {false};
        pointerFlowGraph.succsOf(source).forEach(succ->{
            if(succ.equals(target)){
                flag[0] =true;
            }
        });
        if(flag[0]==false){
            pointerFlowGraph.addEdge(source,target);
            if(!source.getPointsToSet().isEmpty()){
                workList.addEntry(target, source.getPointsToSet());
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
            PointsToSet delta = propagate(entry.pointer, entry.pointsToSet);

            if(entry.pointer instanceof CSVar){
                delta.forEach(o->{
                    CSVar csVar = (CSVar) entry.pointer;
                    Var var = csVar.getVar();

                    var.getLoadArrays().forEach(stmt->{
                        //y=x[i]
                        LValue lValue = stmt.getLValue();
                        CSVar y = csManager.getCSVar(csVar.getContext(),(Var)lValue);
                        ArrayIndex arrayIndex = csManager.getArrayIndex(o);
                        addPFGEdge(arrayIndex,y);
                    });

                    var.getStoreArrays().forEach(stmt->{
                        ArrayIndex arrayIndex = csManager.getArrayIndex(o);
                        RValue rValue = stmt.getRValue();
                        CSVar y = csManager.getCSVar(csVar.getContext(),(Var)rValue);
                        addPFGEdge(y,arrayIndex);

                    });

                    var.getLoadFields().forEach(stmt->{
                        JField field = stmt.getFieldRef().resolve();
                        InstanceField instanceField = csManager.getInstanceField(o,field);
                        LValue lValue = stmt.getLValue();
                        //y=x.f
                        CSVar y = csManager.getCSVar(csVar.getContext(),(Var)lValue);
                        addPFGEdge(instanceField,y);
                    });

                    var.getStoreFields().forEach(stmt->{
                        //x.f = y
                        JField field = stmt.getFieldRef().resolve();
                        InstanceField instanceField = csManager.getInstanceField(o,field);
                        RValue rValue = stmt.getRValue();
                        CSVar y = csManager.getCSVar(csVar.getContext(),(Var)rValue);
                        addPFGEdge(y,instanceField);

                    });
                    if(!taintAnalysis.isTaintObj(o.getObject())) {
                        processCall(csVar, o);
                    }

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
        PointsToSet ptn = pointer.getPointsToSet();
        PointsToSet delta = PointsToSetFactory.make();

        for(CSObj obj : pointsToSet){
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
        return delta;
    }

    /**
     * Processes instance calls when points-to set of the receiver variable changes.
     *
     * @param recv    the receiver variable
     * @param recvObj set of new discovered objects pointed by the variable.
     */
    private void processCall(CSVar recv, CSObj recvObj) {
        // TODO - finish me
        //if(!(taintAnalysis.isTaintObj(recvObj.getObject()))) {
            Var var = recv.getVar();
            var.getInvokes().forEach(invoke -> {
                JMethod m = resolveCallee(recvObj, invoke);
                //m = recvObj.getObject() instanceof MockObj ?invoke.getMethodRef().resolve():resolveCallee(recvObj,invoke);
                if (m != null) {
                /*
                if(invoke.isInterface()||invoke.isSpecial()){
                    m = resolveCallee(recvObj,invoke);
                }*/

                    CSCallSite csCallSite = csManager.getCSCallSite(recv.getContext(), invoke);
                    Context ct = contextSelector.selectContext(csCallSite, recvObj, m);
                    CSVar mThis = csManager.getCSVar(ct, m.getIR().getThis());
                    PointsToSet pointsToSet = PointsToSetFactory.make(recvObj);
                    workList.addEntry(mThis, pointsToSet);

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
                    CSMethod csMethod = csManager.getCSMethod(ct, m);
                    Edge newEdge = new Edge(kind, csCallSite, csMethod);
                    if (callGraph.addEdge(newEdge)) {
                        //CSMethod csMethod = csManager.getCSMethod(ct, m);
                        addReachable(csMethod);

                        for (int i = 0; i < invoke.getInvokeExp().getArgCount(); ++i) {
                            Var v = invoke.getInvokeExp().getArg(i);
                            CSVar csVar = csManager.getCSVar(recv.getContext(), v);

                            var targetVar = m.getIR().getParam(i);
                            CSVar csTargetVar = csManager.getCSVar(ct, targetVar);

                            addPFGEdge(csVar, csTargetVar);
                        }

                        List<Var> varList = m.getIR().getReturnVars();
                        Var r = invoke.getResult();
                        if (r != null) {
                            CSVar csVar = csManager.getCSVar(recv.getContext(), r);
                            for (Var var1 : varList) {
                                CSVar mRet = csManager.getCSVar(ct, var1);
                                addPFGEdge(mRet, csVar);
                            }
                        }
                    }

                    //else {
                    Var res = invoke.getLValue();
                    Type type = invoke.getInvokeExp().getType();
                    Context context = recv.getContext();
                    if (res != null) {
                        //source
                        //if (taintAnalysis.isSource(m, res.getType())) {
                        if (taintAnalysis.isSource(m, type)) {
                            //确实是Obj，但是Obj需要type和l
                            Obj obj = taintAnalysis.getTaintObj(invoke, res.getType());
                            CSObj csObj = csManager.getCSObj(taintAnalysis.getEmptyContext(), obj);
                            //c:r
                            csManager.getCSVar(recv.getContext(), res).getPointsToSet().addObject(csObj);
                            PointsToSet pointsToSet1 = PointsToSetFactory.make(csObj);
                            workList.addEntry(csManager.getCSVar(context,res), pointsToSet1);
                        }
                        //if (taintAnalysis.isBase2Result(m, res.getType())) {
                        if (taintAnalysis.isBase2Result(m, type)) {
                            //c:x
                            CSVar methodBase = csManager.getCSVar(context, recv.getVar());

                            addPFGEdge(methodBase, csManager.getCSVar(context, res));
                        }

                        //if (taintAnalysis.isArg2Base(m, var.getType())) {
                        //if (taintAnalysis.isArg2Base(m, var.getType())) {
                            for (int i = 0; i < invoke.getInvokeExp().getArgCount(); ++i) {
                                //c:ai
                                if (taintAnalysis.isArg2Base(m, var.getType())) {
                                Var v = invoke.getInvokeExp().getArg(i);
                                CSVar var_ai = csManager.getCSVar(context, v);
                                InvokeInstanceExp exp = (InvokeInstanceExp) invoke.getInvokeExp();
                                addPFGEdge(var_ai, csManager.getCSVar(context, exp.getBase()));
                            }
                        }

                        //if (taintAnalysis.isArg2Result(m, res.getType())) {
                        if (taintAnalysis.isArg2Result(m, type)) {
                            for (int i = 0; i < invoke.getInvokeExp().getArgCount(); ++i) {
                                Var v = invoke.getInvokeExp().getArg(i);
                                CSVar var_ai = csManager.getCSVar(context, v);
                                addPFGEdge(var_ai, csManager.getCSVar(context, res));
                            }
                        }

                    //}

                }
                }
            });
            //}
        //}
    }

    /**
     * Resolves the callee of a call site with the receiver object.
     *
     * @param recv the receiver object of the method call. If the callSite
     *             is static, this parameter is ignored (i.e., can be null).
     * @param callSite the call site to be resolved.
     * @return the resolved callee.
     */
    private JMethod resolveCallee(CSObj recv, Invoke callSite) {
        Type type = recv != null ? recv.getObject().getType() : null;
        return CallGraphs.resolveCallee(type, callSite);
    }

    public PointerAnalysisResult getResult() {
        if (result == null) {
            result = new PointerAnalysisResultImpl(csManager, callGraph);
        }
        return result;
    }
}
