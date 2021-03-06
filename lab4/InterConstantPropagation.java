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
 import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
 import pascal.taie.analysis.dataflow.analysis.constprop.Value;
 import pascal.taie.analysis.graph.cfg.CFG;
 import pascal.taie.analysis.graph.cfg.CFGBuilder;
 import pascal.taie.analysis.graph.icfg.CallEdge;
 import pascal.taie.analysis.graph.icfg.CallToReturnEdge;
 import pascal.taie.analysis.graph.icfg.NormalEdge;
 import pascal.taie.analysis.graph.icfg.ReturnEdge;
 import pascal.taie.config.AnalysisConfig;
 import pascal.taie.ir.IR;
 import pascal.taie.ir.exp.InvokeExp;
 import pascal.taie.ir.exp.LValue;
 import pascal.taie.ir.exp.RValue;
 import pascal.taie.ir.exp.Var;
 import pascal.taie.ir.stmt.Invoke;
 import pascal.taie.ir.stmt.Stmt;
 import pascal.taie.language.classes.JMethod;

 import java.util.List;

 /**
  * Implementation of interprocedural constant propagation for int values.
  */
 public class InterConstantPropagation extends
         AbstractInterDataflowAnalysis<JMethod, Stmt, CPFact> {

     public static final String ID = "inter-constprop";

     private final ConstantPropagation cp;

     public InterConstantPropagation(AnalysisConfig config) {
         super(config);
         cp = new ConstantPropagation(new AnalysisConfig(ConstantPropagation.ID));
     }

     @Override
     public boolean isForward() {
         return cp.isForward();
     }

     @Override
     public CPFact newBoundaryFact(Stmt boundary) {
         IR ir = icfg.getContainingMethodOf(boundary).getIR();
         return cp.newBoundaryFact(ir.getResult(CFGBuilder.ID));
     }

     @Override
     public CPFact newInitialFact() {
         return cp.newInitialFact();
     }

     @Override
     public void meetInto(CPFact fact, CPFact target) {
         cp.meetInto(fact, target);
     }

     @Override
     protected boolean transferCallNode(Stmt stmt, CPFact in, CPFact out) {
         // TODO - finish me
         CPFact tmpFact = new CPFact();
         tmpFact.copyFrom(in);
         return out.copyFrom(tmpFact);
     }

     @Override
     protected boolean transferNonCallNode(Stmt stmt, CPFact in, CPFact out) {
         // TODO - finish me
         return cp.transferNode(stmt,in,out);
         //return false;
     }

     @Override
     protected CPFact transferNormalEdge(NormalEdge<Stmt> edge, CPFact out) {
         // TODO - finish me
         CPFact tmpFact = new CPFact();
         tmpFact.copyFrom(out);
         return tmpFact;

     }

     @Override
     protected CPFact transferCallToReturnEdge(CallToReturnEdge<Stmt> edge, CPFact out) {
         // TODO - finish me
         Stmt source = edge.getSource();
         Stmt target = edge.getTarget();
         //?????????????????????
         if(source.getDef().isPresent()) {
             LValue lValue = source.getDef().get();
             Var xValue = null;
             if(lValue instanceof  Var)
                 xValue = (Var) lValue;
             CPFact tmpFact = new CPFact();
             tmpFact.copyFrom(out);
             tmpFact.remove(xValue);
             return tmpFact;
         }else{
             //???????????????
             CPFact tmpFact = new CPFact();
             tmpFact.copyFrom(out);
             return tmpFact;
         }
     }

     @Override
     protected CPFact transferCallEdge(CallEdge<Stmt> edge, CPFact callSiteOut) {
         // TODO - finish me

         //TODO question: ????????????
         List<Var> methodParams = edge.getCallee().getIR().getParams();
         List<RValue> useParams = edge.getSource().getUses();
         //edge.getSource().
         CPFact tmpFact = new CPFact();
         /*
         if(methodParams.size() != useParams.size()){
             System.out.println("Error : params is not the same, CallEdge is wrong!");
         }*/
         //TODO ???????????????instance of
         for(int i = 0; i < methodParams.size(); ++i){
             tmpFact.update(methodParams.get(i), callSiteOut.get((Var)useParams.get(i)));
         }
         return tmpFact;
     }

     @Override
     protected CPFact transferReturnEdge(ReturnEdge<Stmt> edge, CPFact returnOut) {
         // TODO - finish me
         CPFact tmpFact = new CPFact();
         Stmt callStmt = edge.getCallSite();
         if(callStmt.getDef().isPresent()){
             //TODO ???????????? ??????????????????????????????????????????NAC
             LValue lValue = callStmt.getDef().get();
             Var xValue = null;
             if(lValue instanceof  Var)
                 xValue = (Var) lValue;

             final Var[] pre = {null};
             final boolean[] flag = {true};

             edge.returnVars().forEach(var -> {
                 //if(returnOut.get(var).isConstant()){
                     if(pre[0] == null){
                         pre[0] = var;
                     }else{
                         if(returnOut.get(var).isConstant()) {
                             if (returnOut.get(var).getConstant() != returnOut.get(pre[0]).getConstant()) {
                                 flag[0] = false;
                             }
                         }else{
                             flag[0] = false;
                         }
                     }
                 //}else{
                   //  flag[0] = false;
                 //}
             });
             if(flag[0] == false) {
                 tmpFact.update(xValue, Value.getNAC());
             }else{
                 tmpFact.update(xValue, returnOut.get(pre[0]));
             }
         }

         return tmpFact;


     }
 }
