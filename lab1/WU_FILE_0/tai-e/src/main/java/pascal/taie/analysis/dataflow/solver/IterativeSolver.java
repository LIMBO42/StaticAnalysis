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
import pascal.taie.analysis.dataflow.fact.SetFact;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.ir.exp.Var;

class IterativeSolver<Node, Fact> extends Solver<Node, Fact> {

    public IterativeSolver(DataflowAnalysis<Node, Fact> analysis) {
        super(analysis);
    }

    @Override
    protected void doSolveForward(CFG<Node> cfg, DataflowResult<Node, Fact> result) {
        throw new UnsupportedOperationException();
    }

    @Override
    protected void doSolveBackward(CFG<Node> cfg, DataflowResult<Node, Fact> result) {
        // TODO - finish me
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
