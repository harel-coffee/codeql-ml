/**
 * @name over_sampling Leakage Potential
 * @description This query detects potential train-test leakage in your code.
 * @kind path-problem
 * @problem.severity warning
 * @id python/ml/leakage
 * @language python
 */

import python
import semmle.python.dataflow.new.TaintTracking
import semmle.python.ApiGraphs
import semmle.python.dataflow.new.DataFlow
import DataFlow::PathGraph

class StartFromOverSampling extends TaintTracking::TaintTracking {
    StartFromOverSampling() { this = "StartFromOverSampling" }

    override predicate isSource(DataFlow::Node source) {
        exists(DataFlow::CallCfgNode call |
            call.getFunction().(DataFlow::AttrRead).getObject().getALocalSource() = 
            API::moduleImport("imblearn").getMember("over_sampling").getAMember().getReturn().getAUse() and
            source = call
        )
    }

    private predicate isSklearnModelSelectionFunction(string funcName) {
        funcName in ["GroupKFold", "GroupShuffleSplit", "KFold", "LeaveOneGroupOut", "LeavePGroupsOut", "LeaveOneOut", "LeavePOut", "PredefinedSplit", "RepeatedKFold", "RepeatedStratifiedKFold", "ShuffleSplit", "StratifiedKFold", "StratifiedShuffleSplit", "StratifiedGroupKFold", "TimeSeriesSplit", "check_cv", "train_test_split", "GridSearchCV", "HalvingGridSearchCV", "ParameterGrid", "ParameterSampler", "RandomizedSearchCV", "HalvingRandomSearchCV", "cross_validate", "cross_val_predict", "cross_val_score", "learning_curve", "permutation_test_score", "validation_curve", "LearningCurveDisplay", "ValidationCurveDisplay"]
    }

    override predicate isSink(DataFlow::Node sink) {
        exists(DataFlow::CallCfgNode call |
            (
                call.getFunction().(DataFlow::AttrRead).getObject().getALocalSource() = 
                    API::moduleImport("sklearn").getMember("model_selection").getAMember().getReturn().getAUse()
                or
                isSklearnModelSelectionFunction(call.getFunction().asExpr().(Name).getId())
            ) 
            and 
            sink = call
        )
    }
}

from DataFlow::PathElement source, DataFlow::PathElement sink, StartFromOverSampling config
where config.hasFlowPath(source, sink)
select sink.getNode(), source, sink, "Token built from $@.", source.getNode(), "predictable value"
