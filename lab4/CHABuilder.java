package pascal.taie.analysis.graph.callgraph;

import pascal.taie.World;
import pascal.taie.ir.proginfo.MethodRef;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JClass;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.classes.Subsignature;

import java.util.*;

/**
 * Implementation of the CHA algorithm.
 */
class CHABuilder implements CGBuilder<Invoke, JMethod> {

    private ClassHierarchy hierarchy;

    @Override
    public CallGraph<Invoke, JMethod> build() {
        hierarchy = World.getClassHierarchy();
        return buildCallGraph(World.getMainMethod());
    }

    private CallGraph<Invoke, JMethod> buildCallGraph(JMethod entry) {
        DefaultCallGraph callGraph = new DefaultCallGraph();
        callGraph.addEntryMethod(entry);
        // TODO -finish me
        Queue<JMethod> workList = new LinkedList<JMethod>();
        workList.add(entry);
        while(!workList.isEmpty()){
            JMethod tmpMethod = workList.peek();
            workList.remove();
            if(!callGraph.contains(tmpMethod)){
                callGraph.addReachableMethod(tmpMethod);
                callGraph.callSitesIn(tmpMethod).forEach(callSite->{
                        Set<JMethod> Target = resolve(callSite);
                        for(JMethod method : Target){
                            //TODO which type?
                            CallKind kind = CallKind.STATIC;
                            if(callSite.isVirtual()){
                                kind = CallKind.VIRTUAL;
                            }else if(callSite.isStatic()){
                                kind = CallKind.STATIC;
                            }else if(callSite.isInterface()){
                                kind = CallKind.INTERFACE;
                            }else if(callSite.isSpecial()){
                                kind = CallKind.SPECIAL;
                            }else if(callSite.isDynamic()){
                                kind = CallKind.DYNAMIC;
                            }
                            if(method!=null) {
                                Edge newEdge = new Edge(kind, callSite, method);
                                callGraph.addEdge(newEdge);
                                workList.add(method);
                            }
                        }
                    }
                );
            }
        }

        return callGraph;
    }

    /**
     * Resolves call targets (callees) of a call site via CHA.
     */
    private Set<JMethod> resolve(Invoke callSite) {
        // TODO - finish me
        //目标函数集合；question：new treeSet的比较
        Set<JMethod> targetMethod = new HashSet<JMethod>();
        MethodRef callSiteRef = callSite.getMethodRef();
        if(callSite.isStatic()){
            //要找到调用该函数的类，找到声明的函数
            //调用的静态函数，T为该类中的静态函数
            JMethod mMethod = callSiteRef.getDeclaringClass().getDeclaredMethod(callSiteRef.getSubsignature());
            targetMethod.add(mMethod);
        }else if(callSite.isSpecial()){
            //special
            JMethod mMethod = dispatch(callSiteRef.getDeclaringClass(),callSiteRef.getSubsignature());
            targetMethod.add(mMethod);
        }else if(callSite.isInterface()||callSite.isVirtual()){
            //get receiver variable's type
            //怎么获得 变量的声明类
            JClass cClass = callSiteRef.getDeclaringClass();
            //这里是只用subClass还是都要
            Queue<JClass> containList = new LinkedList<JClass>();
            containList.add(cClass);
            while(!containList.isEmpty()){
                //dispatch
                JClass firstClass = containList.peek();
                JMethod mMethod = dispatch(firstClass,callSiteRef.getSubsignature());
                targetMethod.add(mMethod);
                containList.remove();
                //找子类
                //TODO 是只要subclass还是所有
                if(firstClass.isInterface()){
                    Collection<JClass> tmpCollection = hierarchy.getDirectImplementorsOf(firstClass);
                    for(JClass tmpClass : tmpCollection){
                        containList.add(tmpClass);
                    }
                    Collection<JClass> tmpCollection1 = hierarchy.getDirectSubinterfacesOf(firstClass);
                    for(JClass tmpClass : tmpCollection1){
                        containList.add(tmpClass);
                    }
                }else {
                    Collection<JClass> tmpCollection = hierarchy.getDirectSubclassesOf(firstClass);
                    for (JClass tmpClass : tmpCollection) {
                        containList.add(tmpClass);
                    }
                }
            }
        }
        return targetMethod;
    }

    /**
     * Looks up the target method based on given class and method subsignature.
     *
     * @return the dispatched target method, or null if no satisfying method
     * can be found.
     */
    private JMethod dispatch(JClass jclass, Subsignature subsignature) {
        // TODO - finish me

        JMethod search = jclass.getDeclaredMethod(subsignature);

        //不为空且不是虚函数
        if(search != null && !search.isAbstract()) return search;

        //递归去找
        JClass superClass = jclass.getSuperClass();
        if(superClass != null){
            return dispatch(superClass,subsignature);
        }

        return null;
    }
}
