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

package pascal.taie.analysis.dataflow.analysis;

import pascal.taie.analysis.dataflow.fact.SetFact;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.exp.LValue;
import pascal.taie.ir.exp.RValue;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.Stmt;

import java.util.Collection;

/**
 * Implementation of classic live variable analysis.
 */
public class LiveVariableAnalysis extends
        AbstractDataflowAnalysis<Stmt, SetFact<Var>> {

    public static final String ID = "livevar";

    public LiveVariableAnalysis(AnalysisConfig config) {
        super(config);
    }

    @Override
    public boolean isForward() {
        return false;
    }

    @Override
    public SetFact<Var> newBoundaryFact(CFG<Stmt> cfg) {
        // TODO - finish me
        return new SetFact<Var>();
    }

    @Override
    public SetFact<Var> newInitialFact() {
        // TODO - finish me
        return new SetFact<Var>();
    }

    @Override
    public void meetInto(SetFact<Var> fact, SetFact<Var> target) {
        // TODO - finish me
        target.union(fact);
    }

    @Override
    public boolean transferNode(Stmt stmt, SetFact<Var> in, SetFact<Var> out) {
        // TODO - finish me

        //useB
        SetFact<Var> tmp = new SetFact<Var>();
        for(RValue v : stmt.getUses()){
            if(v instanceof Var){
                Var tmpV = (Var) v;
                tmp.add(tmpV);
            }
        }

        //outB-defB
        SetFact<Var> tmpOut = new SetFact<>();
        tmpOut.set(out);

        if(stmt.getDef().isPresent()) {
            LValue tmpDef = stmt.getDef().get();
            if (tmpDef instanceof Var) {
                tmpOut.remove((Var) tmpDef);
            }
        }


        SetFact<Var> oldIn = new SetFact<>();
        oldIn.set(in);
        in.set(tmp.unionWith(tmpOut));
        boolean flag = !in.equals(oldIn);
        return flag;
    }
}
