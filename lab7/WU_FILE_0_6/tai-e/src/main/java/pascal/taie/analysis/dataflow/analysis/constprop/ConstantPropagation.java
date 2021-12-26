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
        CPFact entryFact = new CPFact();
        cfg.getIR().getParams()
                .stream()
                .filter(ConstantPropagation::canHoldInt)
                .forEach(p -> entryFact.update(p, Value.getNAC()));
        return entryFact;
    }

    @Override
    public CPFact newInitialFact() {
        // TODO - finish me
        return new CPFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        // TODO - finish me
        fact.forEach((var, value) ->
                target.update(var, meetValue(target.get(var), value)));
    }

    /**
     * Meets two Values.
     */
    public Value meetValue(Value v1, Value v2) {
        // TODO - finish me
        if (v1.isUndef()) {
            return v2;
        }
        if (v2.isUndef()) {
            return v1;
        }
        if (v1.isNAC() || v2.isNAC()) {
            return Value.getNAC();
        }
        if (!v1.equals(v2)) {
            return Value.getNAC();
        }
        return v1;
    }

    @Override
    public boolean transferNode(Stmt stmt, CPFact in, CPFact out) {
        // TODO - finish me
        if (stmt instanceof DefinitionStmt) {
            DefinitionStmt<?, ?> defStmt = (DefinitionStmt<?, ?>) stmt;
            LValue lVal = defStmt.getLValue();
            if (lVal instanceof Var) {
                Var var = (Var) lVal;
                boolean changed = false;
                for (Var inVar : in.keySet()) {
                    if (!inVar.equals(var)) {
                        changed |= out.update(inVar, in.get(inVar));
                    }
                }
                if (canHoldInt(var)) {
                    changed |= out.update(var, evaluate(defStmt.getRValue(), in));
                }
                return changed;
            }
        }
        return out.copyFrom(in);
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
        if (exp instanceof Var) {
            return in.get((Var) exp);
        } else if (exp instanceof IntLiteral) {
            return Value.makeConstant(((IntLiteral) exp).getValue());
        } else if (exp instanceof BinaryExp) {
            return evaluateBinaryExp((BinaryExp) exp, in);
        }
        return Value.getNAC();
    }

    private static Value evaluateBinaryExp(BinaryExp exp, CPFact in) {
        Value v1 = evaluate(exp.getOperand1(), in);
        Value v2 = evaluate(exp.getOperand2(), in);
        if (exp instanceof ArithmeticExp) {
            ArithmeticExp.Op op = ((ArithmeticExp) exp).getOperator();
            if ((op == ArithmeticExp.Op.DIV || op == ArithmeticExp.Op.REM)
                    && v2.isConstant() && v2.getConstant() == 0) {
                return Value.getUndef();
            }
        }
        if (v1.isConstant() && v2.isConstant()) {
            int c1 = v1.getConstant();
            int c2 = v2.getConstant();
            if (exp instanceof ArithmeticExp) {
                switch (((ArithmeticExp) exp).getOperator()) {
                    case ADD:
                        return Value.makeConstant(c1 + c2);
                    case SUB:
                        return Value.makeConstant(c1 - c2);
                    case MUL:
                        return Value.makeConstant(c1 * c2);
                    case DIV:
                        return Value.makeConstant(c1 / c2);
                    case REM:
                        return Value.makeConstant(c1 % c2);
                }
            } else if (exp instanceof ConditionExp) {
                switch (((ConditionExp) exp).getOperator()) {
                    case EQ:
                        return Value.makeConstant(c1 == c2 ? 1 : 0);
                    case NE:
                        return Value.makeConstant(c1 != c2 ? 1 : 0);
                    case GE:
                        return Value.makeConstant(c1 >= c2 ? 1 : 0);
                    case GT:
                        return Value.makeConstant(c1 > c2 ? 1 : 0);
                    case LE:
                        return Value.makeConstant(c1 <= c2 ? 1 : 0);
                    case LT:
                        return Value.makeConstant(c1 < c2 ? 1 : 0);
                }
            } else if (exp instanceof ShiftExp) {
                switch (((ShiftExp) exp).getOperator()) {
                    case SHL:
                        return Value.makeConstant(c1 << c2);
                    case SHR:
                        return Value.makeConstant(c1 >> c2);
                    case USHR:
                        return Value.makeConstant(c1 >>> c2);
                }
            } else if (exp instanceof BitwiseExp) {
                switch (((BitwiseExp) exp).getOperator()) {
                    case OR:
                        return Value.makeConstant(c1 | c2);
                    case AND:
                        return Value.makeConstant(c1 & c2);
                    case XOR:
                        return Value.makeConstant(c1 ^ c2);
                }
            }
        } else if (v1.isNAC() || v2.isNAC()) {
            return Value.getNAC();
        }
        return Value.getUndef();
    }
}
