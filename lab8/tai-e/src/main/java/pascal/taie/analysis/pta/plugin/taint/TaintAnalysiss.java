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

package pascal.taie.analysis.pta.plugin.taint;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.CallKind;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.core.cs.CSCallGraph;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.element.*;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.analysis.pta.cs.Solver;
import pascal.taie.analysis.pta.pts.PointsToSet;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;

import java.util.ArrayList;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;
import java.util.stream.Stream;

public class TaintAnalysiss {

    private static final Logger logger = LogManager.getLogger(TaintAnalysiss.class);

    private final TaintManager manager;

    private final TaintConfig config;

    private final Solver solver;

    private final CSManager csManager;

    private final Context emptyContext;

    private CSCallGraph callGraph;

    private Set<Source> sources;
    private Set<TaintTransfer> transfers;
    private Set<Sink> sinks;
    //private Set<TaintFlow> taintFlows = new TreeSet<>();

    public TaintAnalysiss(Solver solver) {
        manager = new TaintManager();
        this.solver = solver;
        csManager = solver.getCSManager();
        emptyContext = solver.getContextSelector().getEmptyContext();
        config = TaintConfig.readConfig(
                solver.getOptions().getString("taint-config"),
                World.getClassHierarchy(),
                World.getTypeManager());
        logger.info(config);
        sources = config.getSources();
        transfers = config.getTransfers();
        sinks = config.getSinks();

    }

    /*获得不了stmt的信息，因此要
    void addSource(){
        Set<Source>  sources = config.getSources();
        for(Source s : sources){

        }
    }*/

    // TODO - finish me
    //solver分析完之后调用onFinish
    public void onFinish() {
        //solver分析完之后加入信息
        callGraph = solver.getCallGraph();
        /*
        callGraph.edges().forEach(edge->{
            CSCallSite callSite = edge.getCallSite();
            //invoke: l;
            //context c;
            Invoke invoke = callSite.getCallSite();
            Context context = callSite.getContext();
            CSMethod callee = edge.getCallee();
            //ct:
            //m
            JMethod m = callee.getMethod();
            if(edge.getKind().equals(CallKind.STATIC)) {
                Var res = invoke.getLValue();
                if (res != null) {
                    //source
                    if (isSource(m, res.getType())) {
                        //确实是Obj，但是Obj需要type和l
                        //Obj obj = t ul
                        Obj obj = getTaintObj(invoke, res.getType());
                        CSObj csObj = csManager.getCSObj(emptyContext, obj);
                        csManager.getCSVar(context, res).getPointsToSet().addObject(csObj);
                    }
                    //args to result
                    if (isArg2Result(m, res.getType())) {
                        for (int i = 0; i < invoke.getInvokeExp().getArgCount(); ++i) {
                            //c:ai
                            Var var = invoke.getInvokeExp().getArg(i);
                            CSVar var_ai = csManager.getCSVar(context, var);
                            PointsToSet pointsToSet = var_ai.getPointsToSet();
                            for (CSObj tmp : pointsToSet) {
                                if (isTaintObj(tmp.getObject())) {
                                    //j, u
                                    Obj obj = getTaintObj((Invoke) tmp.getObject().getAllocation(), res.getType());
                                    CSObj csObj = csManager.getCSObj(emptyContext, obj);
                                    //c:r
                                    csManager.getCSVar(context, res).getPointsToSet().addObject(csObj);
                                }
                            }
                        }
                    }
                }
            }else{
                Var res = invoke.getLValue();
                if (res != null) {
                    //source
                    if (isSource(m, res.getType())) {
                        //确实是Obj，但是Obj需要type和l
                        //Obj obj = t ul
                        Obj obj = getTaintObj(invoke, res.getType());
                        CSObj csObj = csManager.getCSObj(emptyContext, obj);
                        csManager.getCSVar(context, res).getPointsToSet().addObject(csObj);
                    }
                    //if()
                }
            }


        });*/
        Set<TaintFlow> taintFlows = collectTaintFlows();
        solver.getResult().storeResult(getClass().getName(), taintFlows);
    }

    //TODO：处理soureces and taint transfers 的逻辑
    public Set<Source> getSource(){
        return config.getSources();
    }

    public Set<TaintTransfer> getTransfer(){
        return config.getTransfers();
    }

    public Set<Sink> getSink(){
        return config.getSinks();
    }

    public boolean isSource(JMethod method, Type type){
        if(type==null) return false;
        for(Source source : sources){
            if(method.equals(source.getMethod())&&type.equals(source.getType())){
                return true;
            }
        }
        return false;
    }

    public Context getEmptyContext() {
        return emptyContext;
    }

    //base -1 result -2
    public boolean isBase2Result(JMethod method,Type type){
        if(type==null) return false;
        for(TaintTransfer transfer : transfers){
            if(method.equals(transfer.getMethod())&&transfer.getFrom()==-1&&transfer.getTo()==-2&&type.equals(transfer.getType())){
                return true;
            }
        }
        return false;
    }

    //<m, i, base, u>
    public boolean isArg2Base(JMethod method, Type type){
        if(type==null) return false;
        for (TaintTransfer transfer : transfers){
            if(method.equals(transfer.getMethod())&&transfer.getFrom()>=0&&transfer.getTo()==-1&&type.equals(transfer.getType())){
                return true;
            }
        }
        return false;
    }

    //<m, i, result, u>
    public boolean isArg2Result(JMethod method, Type type){
        for (TaintTransfer transfer : transfers){
            if(method.equals(transfer.getMethod())&&transfer.getFrom()>=0&&transfer.getTo()==-2&&type.equals(transfer.getType())){
                return true;
            }
        }
        return false;
    }

    public boolean isSink(JMethod method, int index){
        for(Sink sink : sinks){
            if(method.equals(sink.getMethod())&&index == sink.getIndex()){
                return true;
            }
        }
        return false;
    }

    public Obj getTaintObj(Invoke l, Type u){
        return manager.makeTaint(l,u);
    }
    public boolean isTaintObj(Obj obj){
        return manager.isTaint(obj);
    }

    /*
    public void addTaintFlows(Invoke source, Invoke sink, int index){
        taintFlows.add(new TaintFlow(source,sink,index));
    }*/

    private Set<TaintFlow> collectTaintFlows() {
        Set<TaintFlow> taintFlows = new TreeSet<>();
        PointerAnalysisResult result = solver.getResult();
        // TODO - finish me
        // You could query pointer analysis results you need via variable result.
        //TODO：需要处理sink的逻辑


        result.getCSCallGraph().edges().forEach(edge->{
            CSCallSite callSite = edge.getCallSite();
            //invoke: l;
            //context c;
            Invoke invoke = callSite.getCallSite();
            Context context = callSite.getContext();
            CSMethod callee = edge.getCallee();
            //ct:
            //m
            JMethod m = callee.getMethod();

            for (int i = 0; i < invoke.getInvokeExp().getArgCount(); ++i) {
                if (isSink(m, i)) {
                    Var var = invoke.getInvokeExp().getArg(i);
                    CSVar var_ai = csManager.getCSVar(context, var);
                    PointsToSet pointsToSet = var_ai.getPointsToSet();
                    for (CSObj tmp : pointsToSet) {
                        if (isTaintObj(tmp.getObject())) {
                            taintFlows.add(new TaintFlow((Invoke) tmp.getObject().getAllocation(), invoke, i));
                        }
                    }
                }
            }
        });

        return taintFlows;
    }
}
