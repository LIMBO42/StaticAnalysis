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

package pascal.taie.analysis.pta.ci;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.analysis.graph.callgraph.CallGraph;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;
import pascal.taie.util.collection.Maps;
import pascal.taie.util.collection.Pair;
import pascal.taie.util.collection.Sets;

import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.Stream;

class CIPTAResult implements PointerAnalysisResult {

    private static final Logger logger = LogManager.getLogger(CIPTAResult.class);

    private final PointerFlowGraph pointerFlowGraph;

    private final CallGraph<Invoke, JMethod> callGraph;

    /**
     * Points-to sets of field expressions, e.g., v.f.
     */
    private final Map<Pair<Var, JField>, Set<Obj>> fieldPointsTo = Maps.newMap();

    private Set<Obj> objects;

    CIPTAResult(PointerFlowGraph pointerFlowGraph,
                CallGraph<Invoke, JMethod> callGraph) {
        this.pointerFlowGraph = pointerFlowGraph;
        this.callGraph = callGraph;
    }

    @Override
    public Stream<Var> vars() {
        return pointerFlowGraph.pointers()
                .filter(p -> p instanceof VarPtr)
                .map(p -> ((VarPtr) p).getVar());
    }

    @Override
    public Stream<Obj> objects() {
        if (objects == null) {
            objects = pointerFlowGraph.pointers()
                    .map(Pointer::getPointsToSet)
                    .flatMap(PointsToSet::objects)
                    .collect(Collectors.toUnmodifiableSet());
        }
        return objects.stream();
    }

    @Override
    public Set<Obj> getPointsToSet(Var var) {
        return pointerFlowGraph.getVarPtr(var)
                .getPointsToSet()
                .getObjects();
    }

    @Override
    public Set<Obj> getPointsToSet(Var base, JField field) {
        if (field.isStatic()) {
            logger.warn("{} is not instance field", field);
        }
        return fieldPointsTo.computeIfAbsent(new Pair<>(base, field), p -> {
            Set<Obj> pts = Sets.newHybridSet();
            getPointsToSet(base).forEach(o -> {
                InstanceField fieldPtr = pointerFlowGraph
                        .getInstanceField(o, field);
                pts.addAll(fieldPtr.getPointsToSet().getObjects());
            });
            return pts;
        });
    }


    @Override
    public Set<Obj> getPointsToSet(JField field) {
        if (!field.isStatic()) {
            logger.warn("{} is not static field", field);
        }
        return pointerFlowGraph.getStaticField(field)
                .getPointsToSet()
                .getObjects();
    }

    @Override
    public CallGraph<Invoke, JMethod> getCallGraph() {
        return callGraph;
    }

    PointerFlowGraph getPointerFlowGraph() {
        return pointerFlowGraph;
    }
}
