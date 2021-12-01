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

import fj.data.fingertrees.Node;
import pascal.taie.Assignment;
import pascal.taie.analysis.IntraproceduralAnalysis;
import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.analysis.constprop.Value;
import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.dataflow.fact.SetFact;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.analysis.graph.cfg.CFGBuilder;
import pascal.taie.analysis.graph.cfg.Edge;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.*;
import soot.jimple.IfStmt;

import java.util.*;

public class DeadCodeDetection extends IntraproceduralAnalysis {

    public static final String ID = "deadcode";

    public DeadCodeDetection(AnalysisConfig config) {
        super(config);
    }

    @Override
    public Set<Stmt> analyze(IR ir) {
        // obtain CFG
        CFG<Stmt> cfg = ir.getResult(CFGBuilder.ID);
        // obtain result of constant propagation
        DataflowResult<Stmt, CPFact> constants =
                ir.getResult(ConstantPropagation.ID);
        // obtain result of live variable analysis
        DataflowResult<Stmt, SetFact<Var>> liveVars =
                ir.getResult(LiveVariableAnalysis.ID);
        // keep statements (dead code) sorted in the resulting set
        Set<Stmt> deadCode = new TreeSet<>(Comparator.comparing(Stmt::getIndex));
        // TODO - finish me
        // Your task is to recognize dead code in ir and add it to deadCode

        //unreached stmts : control flow
        Set<Stmt> unreachStmts = new TreeSet<>(Comparator.comparing(Stmt::getIndex));
        //ArrayList<Stmt> unreachStmts = new ArrayList<Stmt>();
        //怎么样获得所有stmt 感觉 这样不对 会多
        //可能得按照
        for(Stmt stmt : cfg){
            //if(!unreachStmts.contains(stmt))
            unreachStmts.add(stmt);
        }

        //ArrayList<Stmt> reachedStmts = new ArrayList<Stmt>();
        Set<Stmt> reachedStmts = new TreeSet<>(Comparator.comparing(Stmt::getIndex));
        //DFS
        Stmt entryStmt = cfg.getEntry();
        DFSCfg(cfg, reachedStmts,entryStmt);

        //unreached = all minus reached stmts
        for(Stmt stmt : reachedStmts){
            unreachStmts.remove(stmt);
        }

        for(Stmt stmt : unreachStmts){
            deadCode.add(stmt);
        }

        //unreached stmts : branch flow

        //ArrayList<Stmt> unreachStmts1 = new ArrayList<Stmt>();
        Set<Stmt> unreachStmts1 = new TreeSet<>(Comparator.comparing(Stmt::getIndex));
        //System.out.println("all ------------------------stmts");
        //System.out.println("Entry:---------"+cfg.getEntry());
        for(Stmt stmt : cfg){
            if(!unreachStmts1.contains(stmt))
                //System.out.println(cfg.getMethod()+"___"+stmt.getLineNumber()+": "+ stmt);
                unreachStmts1.add(stmt);
        }
        //System.out.println("all ------------------------stmts");
        //ArrayList<Stmt> visitedStmt = new ArrayList<Stmt>();
        Set<Stmt> visitedStmt = new TreeSet<>(Comparator.comparing(Stmt::getIndex));
        entryStmt = cfg.getEntry();
        DFSBranch(cfg,visitedStmt,entryStmt,constants);
        //System.out.println("--------------------------visited stmt------------------");
        for(Stmt stmt : visitedStmt){
            //System.out.println(cfg.getMethod()+"___"+stmt.getLineNumber()+": "+ stmt);
            unreachStmts1.remove(stmt);
            reachedStmts.remove(stmt);
        }
        //System.out.println("--------------------------deadcode stmt------------------");

        //for(Stmt stmt : unreachStmts1 ){
        for(Stmt stmt : reachedStmts){
            //System.out.println(cfg.getMethod()+"___"+stmt.getLineNumber()+": "+stmt);
            deadCode.add(stmt);
        }
        //System.out.println("--------------------------deadcode stmt end------------------");
        //Dead assignment

        //getIn
        //System.out.println("&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&");
        for(Stmt stmt: cfg){
            //System.out.println(cfg.getMethod()+"___"+stmt.getLineNumber()+"-----"+stmt);
            if(stmt instanceof AssignStmt){
                AssignStmt assignStmt = (AssignStmt) stmt;
                //SetFact liveVar = liveVars.getInFact(assignStmt);
                if(assignStmt.getDef().isPresent()){
                    LValue lValue = assignStmt.getLValue();
                    RValue rValue = assignStmt.getRValue();

                    SetFact liveVar = liveVars.getOutFact(assignStmt);
                    if(lValue instanceof Var){
                        //如果不是活跃变量
                        //if(!judge(cfg,assignStmt,liveVars,(Var) lValue,deadCode)){
                            if(!liveVar.contains(lValue)){
                            if(hasNoSideEffect(rValue)){
                                deadCode.add(stmt);
                            }
                        }
                    }
                }
            }
        }


        return deadCode;
    }

    private  static boolean judge(CFG<Stmt> cfg, Stmt curStmt,DataflowResult<Stmt, SetFact<Var>> liveVars, Var lvar,Set<Stmt> deadCode){
        SetFact liveVar = liveVars.getInFact(curStmt);
        if(liveVar.contains(lvar)) return true;
        final boolean[] flag = {false};
        cfg.outEdgesOf(curStmt).forEach(out->{
            //后继
            if(!deadCode.contains(curStmt)) {
                if (judge(cfg, out.getTarget(), liveVars, lvar,deadCode)) flag[0] = true;
            }

        });
        return flag[0];
    }
    private static void DFSCfg(CFG<Stmt> cfg, Set<Stmt> stmts, Stmt curStmt){
        //here may be not right fallthrough understanding
        //curStmt can fall through
        //if(curStmt == cfg.getExit()) return;
        //if(curStmt.canFallThrough()) {
        //add curStmt
        if (!stmts.contains(curStmt)) {
            //if(!cfg.isEntry(curStmt))
            stmts.add(curStmt);
                /*
                cfg.succsOf(curStmt).forEach(succ -> {
                    DFSCfg(cfg, stmts, succ);
                });*/
            cfg.outEdgesOf(curStmt).forEach(out->{
                //后继
                DFSCfg(cfg,stmts,out.getTarget());
            });

        }
        //}
    }
    private static void ProcessIf(If ifStmt, Value varLValue, Value varRValue, CFG<Stmt> cfg, Set<Stmt> stmts, Stmt curStmt, DataflowResult<Stmt, CPFact> constants, ConditionExp.Op op){
        boolean flag=false;
        if(op==ConditionExp.Op.EQ){
            if(varLValue.getConstant()==varRValue.getConstant())
                flag = true;
        }else if(op == ConditionExp.Op.NE){
            if(varLValue.getConstant()!=varRValue.getConstant())
                flag = true;
        }
        else if(op == ConditionExp.Op.GT){
            if(varLValue.getConstant()>varRValue.getConstant())
                flag = true;
        }else if(op == ConditionExp.Op.GE){
            if(varLValue.getConstant()>=varRValue.getConstant())
                flag = true;
        }else if(op == ConditionExp.Op.LT){
            if(varLValue.getConstant()<varRValue.getConstant())
                flag = true;
        }else if(op == ConditionExp.Op.LE){
            if(varLValue.getConstant()!=varRValue.getConstant())
                flag = true;
        }
        if(flag){
            cfg.outEdgesOf(curStmt).forEach(out->{
                //true,将true跳转到的加入
                if(out.getKind() == Edge.Kind.IF_TRUE){
                    stmts.add(curStmt);
                    //System.out.println("true jump: "+curStmt+"------------------------"+ifStmt.getTarget());
                    DFSBranch(cfg, stmts, ifStmt.getTarget(), constants);
                }
            });
        }else{
            /*
            cfg.succsOf(curStmt).forEach(succ -> {
                //排除掉true跳转到的目标
                if(succ != ifStmt.getTarget()){
                    stmts.add(succ);
                    DFSBranch(cfg,stmts,succ,constants);
                }
            });*/
            cfg.outEdgesOf(curStmt).forEach(out->{
                if(out.getTarget() != ifStmt.getTarget()){
                    stmts.add(out.getTarget());
                    System.out.println("false jump: "+ curStmt+"------------------" +ifStmt.getTarget());
                    DFSBranch(cfg,stmts,out.getTarget(),constants);
                }
            });
        }
    }

    private static void ProcessSwitch(SwitchStmt switchstmt,Value conditionValue,CFG<Stmt> cfg, Set<Stmt> stmts, Stmt curStmt, DataflowResult<Stmt, CPFact> constants){
        //怎么处理fall through呢？

        int index = switchstmt.getCaseValues().indexOf(conditionValue.getConstant());
        //System.out.println("*********************************************");
        //System.out.println(switchstmt.getCaseValues());
        if(index != -1){
            //有跳转目标
            cfg.outEdgesOf(curStmt).forEach(out->{
                if(out.getKind()==Edge.Kind.SWITCH_CASE){
                    if(!stmts.contains(curStmt)) {
                        stmts.add(curStmt);
                        DFSBranch(cfg, stmts, switchstmt.getTarget(index), constants);
                    }
                }
            });
        }else{
            //default
            cfg.outEdgesOf(curStmt).forEach(out->{
                if(out.getKind()==Edge.Kind.SWITCH_DEFAULT){
                    if(!stmts.contains(curStmt)) {
                        stmts.add(curStmt);
                        DFSBranch(cfg, stmts, switchstmt.getDefaultTarget(), constants);
                    }
                }
            });
        }

    }

    //dfs 将能reach的stmt加入ArrayList
    private static void DFSBranch(CFG<Stmt> cfg, Set<Stmt> stmts, Stmt curStmt,DataflowResult<Stmt, CPFact> constants){
        //if(curStmt == cfg.getEntry()) return;
        boolean flag=false;
        if(curStmt instanceof If) {
            If ifStmt = (If) curStmt;
            ConditionExp conditionExp = ifStmt.getCondition();
            //question: is here get in correct?
            CPFact inConstant = constants.getOutFact(curStmt);

            Var varL = conditionExp.getOperand1();
            Var varR = conditionExp.getOperand2();
            Value varLValue = inConstant.get(varL);
            Value varRValue = inConstant.get(varR);

            ConditionExp.Op op =conditionExp.getOperator();

            if(varLValue.isConstant()&&varRValue.isConstant()){
                ProcessIf(ifStmt,varLValue,varRValue,cfg,stmts,curStmt,constants,op);
                flag = true;
            }
            //如果不是constant呢，遍历所有可能的结果


        }else if(curStmt instanceof SwitchStmt){
            SwitchStmt switchStmt = (SwitchStmt) curStmt;
            Var conditionVar = switchStmt.getVar();
            CPFact inConstant = constants.getOutFact(curStmt);
            Value conditionValue = inConstant.get(conditionVar);
            if(conditionValue.isConstant()){
                ProcessSwitch(switchStmt,conditionValue,cfg,stmts,curStmt,constants);
                flag = true;
            }
            //如果不是constant呢

        }

        //如果既不是if也不是switch，要将后继所有的可能加入
        if(flag == false){
            //if(curStmt.canFallThrough()) {
            //add curStmt
            //not contain DFSCfg
            if (!stmts.contains(curStmt)) {
                //System.out.println("normal: "+cfg.getMethod()+"___"+curStmt.getLineNumber()+"------"+curStmt);
                stmts.add(curStmt);
                    /*
                    cfg.succsOf(curStmt).forEach(succ -> {
                        DFSBranch(cfg,stmts,succ,constants);
                    });*/
                cfg.outEdgesOf(curStmt).forEach(out->{
                    //System.out.println("normal: "+cfg.getMethod()+"___"+curStmt.getLineNumber()+"------"+curStmt+"----------------"+out.getTarget());
                    DFSBranch(cfg,stmts,out.getTarget(),constants);
                });
            }
            //}
        }
    }

    /**
     * @return true if given RValue has no side effect, otherwise false.
     */
    private static boolean hasNoSideEffect(RValue rvalue) {
        // new expression modifies the heap
        if (rvalue instanceof NewExp ||
                // cast may trigger ClassCastException
                rvalue instanceof CastExp ||
                // static field access may trigger class initialization
                // instance field access may trigger NPE
                rvalue instanceof FieldAccess ||
                // array access may trigger NPE
                rvalue instanceof ArrayAccess) {
            return false;
        }
        if (rvalue instanceof ArithmeticExp) {
            ArithmeticExp.Op op = ((ArithmeticExp) rvalue).getOperator();
            // may trigger DivideByZeroException
            return op != ArithmeticExp.Op.DIV && op != ArithmeticExp.Op.REM;
        }
        return true;
    }
}
