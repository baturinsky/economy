/*global describe*/
/*global require*/
/*global module*/
/*global it*/
/*global console*/
/*global process*/

import Tableau from "./Tableau/Tableau.js";
import { Constraint, Equality, Variable, IntegerVariable } from "./expressions.js";

/*************************************************************
 * Class: Model
 * Description: Holds the model of a linear optimisation problem
 **************************************************************/
function Model(precision, name) {
    this.tableau = new Tableau(precision);

    this.name = name;

    this.variables = [];

    this.integerVariables = [];

    this.unrestrictedVariables = {};

    this.constraints = [];

    this.nConstraints = 0;

    this.nVariables = 0;

    this.isMinimization = true;

    this.tableauInitialized = false;
    
    this.relaxationIndex = 1;

    this.useMIRCuts = false;

    this.checkForCycles = true;
    
    //
    // Quick and dirty way to leave useful information
    // for the end user without hitting the console
    // or modifying the primary return object...
    //
    this.messages = [];
}
export default Model;

Model.prototype.minimize = function () {
    this.isMinimization = true;
    return this;
};

Model.prototype.maximize = function () {
    this.isMinimization = false;
    return this;
};

// Model.prototype.addConstraint = function (constraint) {
//     // TODO: make sure that the constraint does not belong do another model
//     // and make
//     this.constraints.push(constraint);
//     return this;
// };

Model.prototype._getNewElementIndex = function () {
    if (this.availableIndexes.length > 0) {
        return this.availableIndexes.pop();
    }

    var index = this.lastElementIndex;
    this.lastElementIndex += 1;
    return index;
};

Model.prototype._addConstraint = function (constraint) {
    var slackVariable = constraint.slack;
    this.tableau.variablesPerIndex[slackVariable.index] = slackVariable;
    this.constraints.push(constraint);
    this.nConstraints += 1;
    if (this.tableauInitialized === true) {
        this.tableau.addConstraint(constraint);
    }
};

Model.prototype.smallerThan = function (rhs) {
    var constraint = new Constraint(rhs, true, this.tableau.getNewElementIndex(), this);
    this._addConstraint(constraint);
    return constraint;
};

Model.prototype.greaterThan = function (rhs) {
    var constraint = new Constraint(rhs, false, this.tableau.getNewElementIndex(), this);
    this._addConstraint(constraint);
    return constraint;
};

Model.prototype.equal = function (rhs) {
    var constraintUpper = new Constraint(rhs, true, this.tableau.getNewElementIndex(), this);
    this._addConstraint(constraintUpper);

    var constraintLower = new Constraint(rhs, false, this.tableau.getNewElementIndex(), this);
    this._addConstraint(constraintLower);

    return new Equality(constraintUpper, constraintLower);
};

Model.prototype.addVariable = function (cost, id, isInteger, isUnrestricted, priority) {
    if (typeof priority === "string") {
        switch (priority) {
        case "required":
            priority = 0;
            break;
        case "strong":
            priority = 1;
            break;
        case "medium":
            priority = 2;
            break;
        case "weak":
            priority = 3;
            break;
        default:
            priority = 0;
            break;
        }
    }

    var varIndex = this.tableau.getNewElementIndex();
    if (id === null || id === undefined) {
        id = "v" + varIndex;
    }

    if (cost === null || cost === undefined) {
        cost = 0;
    }

    if (priority === null || priority === undefined) {
        priority = 0;
    }

    var variable;
    if (isInteger) {
        variable = new IntegerVariable(id, cost, varIndex, priority);
        this.integerVariables.push(variable);
    } else {
        variable = new Variable(id, cost, varIndex, priority);
    }

    this.variables.push(variable);
    this.tableau.variablesPerIndex[varIndex] = variable;

    if (isUnrestricted) {
        this.unrestrictedVariables[varIndex] = true;
    }

    this.nVariables += 1;

    if (this.tableauInitialized === true) {
        this.tableau.addVariable(variable);
    }

    return variable;
};

Model.prototype._removeConstraint = function (constraint) {
    var idx = this.constraints.indexOf(constraint);
    if (idx === -1) {
        console.warn("[Model.removeConstraint] Constraint not present in model");
        return;
    }

    this.constraints.splice(idx, 1);
    this.nConstraints -= 1;

    if (this.tableauInitialized === true) {
        this.tableau.removeConstraint(constraint);
    }

    if (constraint.relaxation) {
        this.removeVariable(constraint.relaxation);
    }
};

//-------------------------------------------------------------------
// For dynamic model modification
//-------------------------------------------------------------------
Model.prototype.removeConstraint = function (constraint) {
    if (constraint.isEquality) {
        this._removeConstraint(constraint.upperBound);
        this._removeConstraint(constraint.lowerBound);
    } else {
        this._removeConstraint(constraint);
    }

    return this;
};

Model.prototype.removeVariable = function (variable) {
    var idx = this.variables.indexOf(variable);
    if (idx === -1) {
        console.warn("[Model.removeVariable] Variable not present in model");
        return;
    }
    this.variables.splice(idx, 1);

    if (this.tableauInitialized === true) {
        this.tableau.removeVariable(variable);
    }

    return this;
};

Model.prototype.updateRightHandSide = function (constraint, difference) {
    if (this.tableauInitialized === true) {
        this.tableau.updateRightHandSide(constraint, difference);
    }
    return this;
};

Model.prototype.updateConstraintCoefficient = function (constraint, variable, difference) {
    if (this.tableauInitialized === true) {
        this.tableau.updateConstraintCoefficient(constraint, variable, difference);
    }
    return this;
};


Model.prototype.setCost = function (cost, variable) {
    var difference = cost - variable.cost;
    if (this.isMinimization === false) {
        difference = -difference;
    }

    variable.cost = cost;
    this.tableau.updateCost(variable, difference);
    return this;
};

//-------------------------------------------------------------------
//-------------------------------------------------------------------
Model.prototype.loadJson = function (jsonModel) {
    this.isMinimization = (jsonModel.opType !== "max");

    var variables = jsonModel.variables;
    var constraints = jsonModel.constraints;

    var constraintsMin = {};
    var constraintsMax = {};

    // Instantiating constraints
    var constraintIds = Object.keys(constraints);
    var nConstraintIds = constraintIds.length;

    for (var c = 0; c < nConstraintIds; c += 1) {
        var constraintId = constraintIds[c];
        var constraint = constraints[constraintId];
        var equal = constraint.equal;

        var weight = constraint.weight;
        var priority = constraint.priority;
        var relaxed = weight !== undefined || priority !== undefined;

        var lowerBound, upperBound;
        if (equal === undefined) {
            var min = constraint.min;
            if (min !== undefined) {
                lowerBound = this.greaterThan(min);
                constraintsMin[constraintId] = lowerBound;
                if (relaxed) { lowerBound.relax(weight, priority); }
            }

            var max = constraint.max;
            if (max !== undefined) {
                upperBound = this.smallerThan(max);
                constraintsMax[constraintId] = upperBound;
                if (relaxed) { upperBound.relax(weight, priority); }
            }
        } else {
            lowerBound = this.greaterThan(equal);
            constraintsMin[constraintId] = lowerBound;

            upperBound = this.smallerThan(equal);
            constraintsMax[constraintId] = upperBound;

            var equality = new Equality(lowerBound, upperBound);
            if (relaxed) { equality.relax(weight, priority); }
        }
    }

    var variableIds = Object.keys(variables);
    var nVariables = variableIds.length;
    
    
    
//
//
// *** OPTIONS ***
//
//

    this.tolerance = jsonModel.tolerance || 0;
    
    if(jsonModel.timeout){
        this.timeout = jsonModel.timeout;
    }
    
    //
    //
    // The model is getting too sloppy with options added to it...
    // mebe it needs an "options" option...?
    //
    // YES! IT DOES!
    // DO IT!
    // NOW!
    // HERE!!!
    //
    if(jsonModel.options){
        
        //
        // TIMEOUT
        //
        if(jsonModel.options.timeout){
            this.timeout = jsonModel.options.timeout;
        }
        
        //
        // TOLERANCE
        //
        if(this.tolerance === 0){
            this.tolerance = jsonModel.options.tolerance || 0;
        }
        
        //
        // MIR CUTS - (NOT WORKING)
        //
        if(jsonModel.options.useMIRCuts){
            this.useMIRCuts = jsonModel.options.useMIRCuts;
        }
        
        //
        // CYCLE CHECK...tricky because it defaults to false
        //
        //
        // This should maybe be on by default...
        //
        if(typeof jsonModel.options.exitOnCycles === "undefined"){
            this.checkForCycles = true;
        } else {
            this.checkForCycles = jsonModel.options.exitOnCycles;
        }
        
        //
        // STORE MILP MODELS
        //
        if(jsonModel.options.keep_solutions){
            this.keep_solutions = jsonModel.options.keep_solutions;
        } else {
            this.keep_solutions = false;
        }

        
    }
    
    
//
//
// /// OPTIONS \\\
//
//
    
    var integerVarIds = jsonModel.ints || {};
    var binaryVarIds = jsonModel.binaries || {};
    var unrestrictedVarIds = jsonModel.unrestricted || {};

    // Instantiating variables and constraint terms
    var objectiveName = jsonModel.optimize;
    for (var v = 0; v < nVariables; v += 1) {
        // Creation of the variables
        var variableId = variableIds[v];
        var variableConstraints = variables[variableId];
        var cost = variableConstraints[objectiveName] || 0;
        var isBinary = !!binaryVarIds[variableId];
        var isInteger = !!integerVarIds[variableId] || isBinary;
        var isUnrestricted = !!unrestrictedVarIds[variableId];
        var variable = this.addVariable(cost, variableId, isInteger, isUnrestricted);

        if (isBinary) {
            // Creating an upperbound constraint for this variable
            this.smallerThan(1).addTerm(1, variable);
        }

        var constraintNames = Object.keys(variableConstraints);
        for (c = 0; c < constraintNames.length; c += 1) {
            var constraintName = constraintNames[c];
            if (constraintName === objectiveName) {
                continue;
            }

            var coefficient = variableConstraints[constraintName];

            var constraintMin = constraintsMin[constraintName];
            if (constraintMin !== undefined) {
                constraintMin.addTerm(coefficient, variable);
            }

            var constraintMax = constraintsMax[constraintName];
            if (constraintMax !== undefined) {
                constraintMax.addTerm(coefficient, variable);
            }
        }
    }

    return this;
};

//-------------------------------------------------------------------
//-------------------------------------------------------------------
Model.prototype.getNumberOfIntegerVariables = function () {
    return this.integerVariables.length;
};

Model.prototype.solve = function () {
    // Setting tableau if not done
    if (this.tableauInitialized === false) {
        this.tableau.setModel(this);
        this.tableauInitialized = true;
    }

    return this.tableau.solve();
};

Model.prototype.isFeasible = function () {
    return this.tableau.feasible;
};

Model.prototype.save = function () {
    return this.tableau.save();
};

Model.prototype.restore = function () {
    return this.tableau.restore();
};

Model.prototype.activateMIRCuts = function (useMIRCuts) {
    this.useMIRCuts = useMIRCuts;
};

Model.prototype.debug = function (debugCheckForCycles) {
    this.checkForCycles = debugCheckForCycles;
};

Model.prototype.log = function (message) {
    return this.tableau.log(message);
};
