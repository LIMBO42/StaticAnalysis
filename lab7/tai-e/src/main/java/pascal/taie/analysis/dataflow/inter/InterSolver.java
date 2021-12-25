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

import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.graph.icfg.ICFG;
import pascal.taie.analysis.graph.icfg.ICFGEdge;
import pascal.taie.util.collection.SetQueue;

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
        for(Node node : icfg){
            if(result.getOutFact(node) == null)
                result.setOutFact(node, analysis.newInitialFact());
        }
        for(Node node : icfg){
            if(result.getInFact(node) == null)
                result.setInFact(node, analysis.newInitialFact());
        }
        icfg.entryMethods().forEach(method -> {
            Node entryNode = icfg.getEntryOf(method);
            result.setOutFact(entryNode,analysis.newBoundaryFact(entryNode));
        });
    }

    private void doSolve() {
        // TODO - finish me
        workList = new LinkedList<Node>();
        for(Node node : icfg){
            workList.add(node);
        }

        for(Node node : icfg){
            workList.add(node);
        }

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
                //要对pre的边进行transfer

                //遍历所有前驱的出边 看目的地是不是当前的node
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
