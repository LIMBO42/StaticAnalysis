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

package pascal.taie.analysis.pta;

import org.junit.Test;
import pascal.taie.analysis.Tests;

public class CIPTATest {

    static final String DIR = "cipta";

    @Test
    public void testExample() {
        Tests.testPTA(DIR, "Example");
    }

    @Test
    public void testArray() {
        Tests.testPTA(DIR, "Array");
    }

    @Test
    public void testAssign() {
        Tests.testPTA(DIR, "Assign");
    }

    @Test
    public void testAssign2() {
        Tests.testPTA(DIR, "Assign2");
    }

    @Test
    public void testStoreLoad() {
        Tests.testPTA(DIR, "StoreLoad");
    }

    @Test
    public void testCall() {
        Tests.testPTA(DIR, "Call");
    }

    @Test
    public void testInstanceField() {
        Tests.testPTA(DIR, "InstanceField");
    }

    @Test
    public void testStaticField() {
        Tests.testPTA(DIR, "StaticField");
    }

    @Test
    public void testStaticCall() {
        Tests.testPTA(DIR, "StaticCall");
    }

    @Test
    public void testMergeParam() {
        Tests.testPTA(DIR, "MergeParam");
    }
}
