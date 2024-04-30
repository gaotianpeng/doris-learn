// Licensed to the Apache Software Foundation (ASF) under one
// or more contributor license agreements.  See the NOTICE file
// distributed with this work for additional information
// regarding copyright ownership.  The ASF licenses this file
// to you under the Apache License, Version 2.0 (the
// "License"); you may not use this file except in compliance
// with the License.  You may obtain a copy of the License at
//
//   http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing,
// software distributed under the License is distributed on an
// "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY
// KIND, either express or implied.  See the License for the
// specific language governing permissions and limitations
// under the License.

package org.apache.doris.statistics;

import java.util.List;

/**
 * Used to abstract a common operator interface for statistics deduction to fit both optimizers.
 */
// 用于抽象一个通用的操作符接口，用于统计信息推导，以适配两种不同的查询优化器。
public interface PlanStats {

    List<StatsDeriveResult> getChildrenStats();

    StatsDeriveResult getStatsDeriveResult();

    StatisticalType getStatisticalType();

    void setStatsDeriveResult(StatsDeriveResult result);

    long getLimit();

    List<? extends ExprStats> getConjuncts();

}
