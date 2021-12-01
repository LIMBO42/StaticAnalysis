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

package pascal.taie.analysis.dataflow.solver;

import pascal.taie.analysis.dataflow.analysis.DataflowAnalysis;
import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.graph.cfg.CFG;

import java.util.LinkedList;

class WorkListSolver<Node, Fact> extends Solver<Node, Fact> {

    WorkListSolver(DataflowAnalysis<Node, Fact> analysis) {
        super(analysis);
    }

    @Override
    protected void doSolveForward(CFG<Node> cfg, DataflowResult<Node, Fact> result) {
        // TODO - finish me
        // add all blocks to work list
        LinkedList<Node> workList = new LinkedList<Node>();
        for(Node node : cfg)
            workList.add(node);

        //while(list not empty)
        while(!workList.isEmpty()){
            //get last
            Node tmpNode = workList.getFirst();
            workList.removeFirst();
            // in[B] = U out[p]
            cfg.predsOf(tmpNode).forEach(pre -> {
                //if(!cfg.isEntry(tmpNode)) {
                if (result.getInFact(tmpNode) == null)
                    result.setInFact(tmpNode, analysis.newInitialFact());
                //}
                analysis.meetInto(result.getOutFact(pre),result.getInFact(tmpNode));
            });
            boolean flag = analysis.transferNode(tmpNode, result.getInFact(tmpNode), result.getOutFact(tmpNode) );
            if(flag){
                cfg.succsOf(tmpNode).forEach(succ->{
                    workList.add(succ);
                });
            }
        }
    }

    @Override
    protected void doSolveBackward(CFG<Node> cfg, DataflowResult<Node, Fact> result) {
        // TODO - finish me

        //add all nodes
        /*
        LinkedList<Node> workList = new LinkedList<Node>();
        for(Node node : cfg)
            workList.add(node);

        while(!workList.isEmpty()){
            Node tmpNode = workList.getFirst();
            workList.removeFirst();

            cfg.succsOf(tmpNode).forEach(succ ->{
                if (result.getOutFact(tmpNode) == null) {
                    result.setOutFact(tmpNode, analysis.newInitialFact());
                }
                analysis.meetInto(result.getInFact(succ), result.getOutFact(tmpNode));
            });

            boolean flag = analysis.transferNode(tmpNode, result.getInFact(tmpNode), result.getOutFact(tmpNode));

            if(flag){
                cfg.succsOf(tmpNode).forEach(succ->{
                    workList.add(succ);
                });
            }

        }
        */
        boolean flag = true;
        while(flag){
            flag = false;
            for(Node node : cfg ) {
                cfg.succsOf(node).forEach(succ -> {
                    if (!cfg.isExit(node)) {
                        if (result.getOutFact(node) == null) {
                            result.setOutFact(node, analysis.newInitialFact());
                        }
                        analysis.meetInto(result.getInFact(succ), result.getOutFact(node));
                    }
                });
                if (!cfg.isExit(node)) {
                    boolean isChanged = analysis.transferNode(node, result.getInFact(node), result.getOutFact(node));
                    if (isChanged) flag = true;
                }
            }
        }

    }
}
