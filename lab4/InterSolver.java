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

import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.graph.callgraph.CallGraph;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.graph.icfg.ICFG;
import pascal.taie.analysis.graph.icfg.ICFGEdge;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.util.collection.SetQueue;
import polyglot.ast.Call;

import java.util.LinkedList;
import java.util.Queue;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.Stream;

/**
 * Solver for inter-procedural data-flow analysis.
 * The workload of inter-procedural analysis is heavy, thus we always
 * adopt work-list algorithm for efficiency.
 */
class InterSolver<Method, Node, Fact> {

    private final InterDataflowAnalysis<Node, Fact> analysis;

    private final ICFG<Method, Node> icfg;

    private DataflowResult<Node, Fact> result;

    private Queue<Node> workList;

    InterSolver(InterDataflowAnalysis<Node, Fact> analysis,
                ICFG<Method, Node> icfg) {
        this.analysis = analysis;
        this.icfg = icfg;
    }

    DataflowResult<Node, Fact> solve() {
        result = new DataflowResult<>();
        initialize();
        doSolve();
        return result;
    }

    private void initialize() {
        // TODO - finish me
        icfg.entryMethods().forEach(method -> {
            Node entryNode = icfg.getEntryOf(method);
            result.setOutFact(entryNode,analysis.newBoundaryFact(entryNode));
        });
        for(Node node : icfg){
            if(result.getOutFact(node) == null)
                result.setOutFact(node, analysis.newInitialFact());
        }

    }

    private void doSolve() {
        // TODO - finish me
        /*
        CallGraph callIcfg = null;
        if(icfg instanceof CallGraph){
            callIcfg = (CallGraph) icfg;
        }else{
            System.out.println("Error: doSolve is wrong. Cannot transfer icfg to call graph!");
        }

        InterConstantPropagation interAnalysis = null;
        if(analysis instanceof InterConstantPropagation) {
            interAnalysis = (InterConstantPropagation) analysis;
        }else{
            System.out.println("Error: doSolve is wrong. Cannot transfer analysis to interConstantPropagation!");
        }
        */
        workList = new LinkedList<Node>();
        for(Node node : icfg){
            workList.add(node);
        }
        while(!workList.isEmpty()){
            Node tmpNode = workList.peek();
            workList.remove();
            icfg.predsOf(tmpNode).forEach(pre->{

                if(result.getInFact(tmpNode) == null) {
                    result.setInFact(tmpNode, analysis.newInitialFact());
                }
                //??????pre????????????transfer

                //??????????????????????????? ??????????????????????????????node
                Stream<ICFGEdge<Node>> outEdges = icfg.outEdgesOf(pre);
                outEdges.forEach(outEdge->{
                    if(outEdge.getTarget() == tmpNode){
                        Fact outFact = analysis.transferEdge(outEdge, result.getOutFact(pre));
                        //analysis.meetInto(result.getInFact(pre), outFact);
                        analysis.meetInto(outFact, result.getInFact(tmpNode));
                    }
                });
            });

            boolean flag = analysis.transferNode(tmpNode, result.getInFact(tmpNode), result.getOutFact(tmpNode));
            if(flag){
                icfg.succsOf(tmpNode).forEach(succ->{
                    workList.add(succ);
                });
            }

        }

    }
}
