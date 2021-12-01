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

package pascal.taie.analysis.dataflow.analysis.constprop;

import pascal.taie.analysis.dataflow.analysis.AbstractDataflowAnalysis;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.DefinitionStmt;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.type.PrimitiveType;
import pascal.taie.language.type.Type;
import pascal.taie.util.AnalysisException;

import java.util.Optional;

public class ConstantPropagation extends
        AbstractDataflowAnalysis<Stmt, CPFact> {

    public static final String ID = "constprop";

    public ConstantPropagation(AnalysisConfig config) {
        super(config);
    }

    @Override
    public boolean isForward() {
        return true;
    }

    @Override
    public CPFact newBoundaryFact(CFG<Stmt> cfg) {
        // TODO - finish me
        CPFact resCPF = new CPFact();

        //initialize the parameters to NAC
        for(Var var : cfg.getMethod().getIR().getParams()){
            if(canHoldInt(var))
                resCPF.update(var, Value.getNAC());
        }

        return resCPF;
    }

    @Override
    public CPFact newInitialFact() {
        //maybe need to initial later
        //in theory all stmt needs to initialize with undefine
        return new CPFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        // TODO - finish me
        fact.forEach((key,value)->{
            target.update(key,meetValue(value,target.get(key)));
                }
        );
        
    }

    /**
     * Meets two Values.
     */
    public Value meetValue(Value v1, Value v2) {
        //question do we need to new a value and copy?
        if(v1.isNAC()||v2.isNAC()) return Value.getNAC();
        else if(v1.isUndef()){
            if(v2.isConstant()) return Value.makeConstant(v2.getConstant());
            else if(v2.isUndef()) return Value.getUndef();
        }
        else if(v2.isUndef()){
            if(v1.isConstant()) return Value.makeConstant(v1.getConstant());
            else if(v1.isUndef()) return Value.getUndef();
        }
        else if(v1.isConstant()&&v2.isConstant()){
            if(v1.getConstant()==v2.getConstant()){
                return Value.makeConstant(v1.getConstant());
            }else return Value.getNAC();
        }

        System.out.println("meetValue error");
        return null;

    }

    @Override
    public boolean transferNode(Stmt stmt, CPFact in, CPFact out) {
        // TODO - finish me

        if(stmt instanceof DefinitionStmt){
            DefinitionStmt defStmt = (DefinitionStmt) stmt;

            //System.out.println(defStmt);

            LValue lValue = defStmt.getLValue();
            RValue rValue = defStmt.getRValue();
            //in[s] - x
            Var xValue = null;
            if(lValue instanceof  Var)
                xValue = (Var) lValue;

            //in.remove(xValue);

            //gen
            Exp rExp = null;
            if(rValue instanceof Exp)
                rExp = (Exp)rValue;
            Value gen = evaluate(rExp,in);
            in.remove(xValue);

            //gen U (in[s]-x)
            CPFact tmpFact = new CPFact();
            tmpFact.copyFrom(in);
            if(xValue!=null&&canHoldInt(xValue))
                tmpFact.update(xValue,gen);

            return out.copyFrom(tmpFact);
        }
        else{
            if(in!=null)
                return out.copyFrom(in);
        }
        // if not definition; return false;
        return false;
    }

    /**
     * @return true if the given variable can hold integer value, otherwise false.
     */
    public static boolean canHoldInt(Var var) {
        Type type = var.getType();
        if (type instanceof PrimitiveType) {
            switch ((PrimitiveType) type) {
                case BYTE:
                case SHORT:
                case INT:
                case CHAR:
                case BOOLEAN:
                    return true;
            }
        }
        return false;
    }

    /**
     * Evaluates the {@link Value} of given expression.
     *
     * @param exp the expression to be evaluated
     * @param in  IN fact of the statement
     * @return the resulting {@link Value}
     */
    public static Value evaluate(Exp exp, CPFact in) {
        // TODO - finish me

        if(exp instanceof Var){
            Var tmpExp = (Var) exp;
            //may be question
            if(canHoldInt(tmpExp))
                return in.get(tmpExp);

        }else if(exp instanceof IntLiteral){
            IntLiteral tmpExp = (IntLiteral) exp;
            return Value.makeConstant(tmpExp.getValue());
        }
        //binary exp
        else if(exp instanceof BinaryExp){
            if(exp instanceof ArithmeticExp){
                ArithmeticExp tmpExp = (ArithmeticExp) exp;
                Var operand1 = tmpExp.getOperand1();
                Var operand2 = tmpExp.getOperand2();
                if(canHoldInt(operand1)&&canHoldInt(operand2)){
                Value operand1Value = in.get(operand1);
                Value operand2Value = in.get(operand2);
                if(operand1Value.isConstant()&&operand2Value.isConstant()){
                    ArithmeticExp.Op op = tmpExp.getOperator();
                    if(op == ArithmeticExp.Op.ADD){
                        return Value.makeConstant(operand1Value.getConstant() + operand2Value.getConstant());
                    }else if(op == ArithmeticExp.Op.SUB){
                        return Value.makeConstant(operand1Value.getConstant() - operand2Value.getConstant());
                    }else if(op == ArithmeticExp.Op.MUL){
                        return Value.makeConstant(operand1Value.getConstant() * operand2Value.getConstant());
                    }else if(op == ArithmeticExp.Op.DIV){
                        if(operand2Value.getConstant()==0)
                            return Value.getUndef();
                        return Value.makeConstant(operand1Value.getConstant() / operand2Value.getConstant());
                    }else if(op == ArithmeticExp.Op.REM){
                        if(operand2Value.getConstant()==0)
                            return Value.getUndef();
                        return Value.makeConstant(operand1Value.getConstant() % operand2Value.getConstant());
                    }
                }
                else if(operand1Value.isNAC()||operand2Value.isNAC()){
                    if(operand1Value.isNAC()&&operand2Value.isConstant()&&operand2Value.getConstant()==0){
                        ArithmeticExp.Op op = tmpExp.getOperator();
                        if(op == ArithmeticExp.Op.DIV){
                            if(operand2Value.getConstant()==0)
                                return Value.getUndef();
                        }else if(op == ArithmeticExp.Op.REM){
                            if(operand2Value.getConstant()==0)
                                return Value.getUndef();
                        }
                    }
                    return Value.getNAC();
                }else{
                    return Value.getUndef();
                }
                }
            }else if(exp instanceof ConditionExp){
                ConditionExp tmpExp = (ConditionExp) exp;
                Var operand1 = tmpExp.getOperand1();
                Var operand2 = tmpExp.getOperand2();
                Value operand1Value = in.get(operand1);
                Value operand2Value = in.get(operand2);
                if(operand1Value.isConstant()&&operand2Value.isConstant()){
                    ConditionExp.Op op = tmpExp.getOperator();
                    if(op == ConditionExp.Op.EQ){
                        if(operand1Value.getConstant()== operand2Value.getConstant())
                            return Value.makeConstant(1);
                        else return Value.makeConstant(0);
                    }else if(op == ConditionExp.Op.GE){
                        if(operand1Value.getConstant()>= operand2Value.getConstant())
                            return Value.makeConstant(1);
                        else return Value.makeConstant(0);
                    }else if(op == ConditionExp.Op.GT){
                        if(operand1Value.getConstant() > operand2Value.getConstant())
                            return Value.makeConstant(1);
                        else return Value.makeConstant(0);
                    }else if(op == ConditionExp.Op.LE){
                        if(operand1Value.getConstant()<= operand2Value.getConstant())
                            return Value.makeConstant(1);
                        else return Value.makeConstant(0);
                    }else if(op == ConditionExp.Op.LT){
                        if(operand1Value.getConstant() < operand2Value.getConstant())
                            return Value.makeConstant(1);
                        else return Value.makeConstant(0);
                    }else if(op == ConditionExp.Op.NE){
                        if(operand1Value.getConstant()!= operand2Value.getConstant())
                            return Value.makeConstant(1);
                        else return Value.makeConstant(0);
                    }

                }
                else if(operand1Value.isNAC()||operand2Value.isNAC()){
                    return Value.getNAC();
                }else{
                    return Value.getUndef();
                }
            }else if(exp instanceof ShiftExp){
                ShiftExp tmpExp = (ShiftExp) exp;
                Var operand1 = tmpExp.getOperand1();
                Var operand2 = tmpExp.getOperand2();
                Value operand1Value = in.get(operand1);
                Value operand2Value = in.get(operand2);
                if(operand1Value.isConstant()&&operand2Value.isConstant()){
                    ShiftExp.Op op = tmpExp.getOperator();
                    if(op== ShiftExp.Op.SHL){
                        return Value.makeConstant(operand1Value.getConstant()<< operand2Value.getConstant());
                    }else if(op == ShiftExp.Op.SHR){
                        return Value.makeConstant(operand1Value.getConstant()>> operand2Value.getConstant());
                    }else if(op == ShiftExp.Op.USHR){
                        return Value.makeConstant(operand1Value.getConstant() >>> operand2Value.getConstant());
                    }
                }
                else if(operand1Value.isNAC()||operand2Value.isNAC()){
                    return Value.getNAC();
                }else{
                    return Value.getUndef();
                }
            }else if(exp instanceof BitwiseExp){
                BitwiseExp tmpExp = (BitwiseExp) exp;
                Var operand1 = tmpExp.getOperand1();
                Var operand2 = tmpExp.getOperand2();
                Value operand1Value = in.get(operand1);
                Value operand2Value = in.get(operand2);
                if(operand1Value.isConstant()&&operand2Value.isConstant()){
                    BitwiseExp.Op op = tmpExp.getOperator();
                    if(op == BitwiseExp.Op.OR){
                        return Value.makeConstant(operand1Value.getConstant() | operand2Value.getConstant());
                    }else if(op == BitwiseExp.Op.AND){
                        return Value.makeConstant(operand1Value.getConstant() & operand2Value.getConstant());
                    }else if(op == BitwiseExp.Op.XOR){
                        return Value.makeConstant(operand1Value.getConstant() ^ operand2Value.getConstant());
                    }
                }
                else if(operand1Value.isNAC()||operand2Value.isNAC()){
                    return Value.getNAC();
                }else{
                    return Value.getUndef();
                }
            }
        }
        //System.out.println("evaluate error");
        return Value.getNAC();
    }
}
