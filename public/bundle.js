(() => {
  var __defProp = Object.defineProperty;
  var __markAsModule = (target) => __defProp(target, "__esModule", { value: true });

  // src/lp-solver/Tableau/Solution.js
  function Solution(tableau, evaluation, feasible, bounded) {
    this.feasible = feasible;
    this.evaluation = evaluation;
    this.bounded = bounded;
    this._tableau = tableau;
  }
  var Solution_default = Solution;
  Solution.prototype.generateSolutionSet = function() {
    var solutionSet = {};
    var tableau = this._tableau;
    var varIndexByRow = tableau.varIndexByRow;
    var variablesPerIndex = tableau.variablesPerIndex;
    var matrix = tableau.matrix;
    var rhsColumn = tableau.rhsColumn;
    var lastRow = tableau.height - 1;
    var roundingCoeff = Math.round(1 / tableau.precision);
    for (var r = 1; r <= lastRow; r += 1) {
      var varIndex = varIndexByRow[r];
      var variable = variablesPerIndex[varIndex];
      if (variable === void 0 || variable.isSlack === true) {
        continue;
      }
      var varValue = matrix[r][rhsColumn];
      solutionSet[variable.id] = Math.round((Number.EPSILON + varValue) * roundingCoeff) / roundingCoeff;
    }
    return solutionSet;
  };

  // src/lp-solver/Tableau/MilpSolution.js
  function MilpSolution(tableau, evaluation, feasible, bounded, branchAndCutIterations) {
    Solution_default.call(this, tableau, evaluation, feasible, bounded);
    this.iter = branchAndCutIterations;
  }
  var MilpSolution_default = MilpSolution;
  MilpSolution.prototype = Object.create(Solution_default.prototype);
  MilpSolution.constructor = MilpSolution;

  // src/lp-solver/Tableau/Tableau.js
  function Tableau(precision) {
    this.model = null;
    this.matrix = null;
    this.width = 0;
    this.height = 0;
    this.costRowIndex = 0;
    this.rhsColumn = 0;
    this.variablesPerIndex = [];
    this.unrestrictedVars = null;
    this.feasible = true;
    this.evaluation = 0;
    this.simplexIters = 0;
    this.varIndexByRow = null;
    this.varIndexByCol = null;
    this.rowByVarIndex = null;
    this.colByVarIndex = null;
    this.precision = precision || 1e-8;
    this.optionalObjectives = [];
    this.objectivesByPriority = {};
    this.savedState = null;
    this.availableIndexes = [];
    this.lastElementIndex = 0;
    this.variables = null;
    this.nVars = 0;
    this.bounded = true;
    this.unboundedVarIndex = null;
    this.branchAndCutIterations = 0;
  }
  var Tableau_default = Tableau;
  Tableau.prototype.solve = function() {
    if (this.model.getNumberOfIntegerVariables() > 0) {
      this.branchAndCut();
    } else {
      this.simplex();
    }
    this.updateVariableValues();
    return this.getSolution();
  };
  function OptionalObjective(priority, nColumns) {
    this.priority = priority;
    this.reducedCosts = new Array(nColumns);
    for (var c = 0; c < nColumns; c += 1) {
      this.reducedCosts[c] = 0;
    }
  }
  OptionalObjective.prototype.copy = function() {
    var copy = new OptionalObjective(this.priority, this.reducedCosts.length);
    copy.reducedCosts = this.reducedCosts.slice();
    return copy;
  };
  Tableau.prototype.setOptionalObjective = function(priority, column, cost) {
    var objectiveForPriority = this.objectivesByPriority[priority];
    if (objectiveForPriority === void 0) {
      var nColumns = Math.max(this.width, column + 1);
      objectiveForPriority = new OptionalObjective(priority, nColumns);
      this.objectivesByPriority[priority] = objectiveForPriority;
      this.optionalObjectives.push(objectiveForPriority);
      this.optionalObjectives.sort(function(a, b) {
        return a.priority - b.priority;
      });
    }
    objectiveForPriority.reducedCosts[column] = cost;
  };
  Tableau.prototype.initialize = function(width, height, variables, unrestrictedVars) {
    this.variables = variables;
    this.unrestrictedVars = unrestrictedVars;
    this.width = width;
    this.height = height;
    var tmpRow = new Array(width);
    for (var i = 0; i < width; i++) {
      tmpRow[i] = 0;
    }
    this.matrix = new Array(height);
    for (var j = 0; j < height; j++) {
      this.matrix[j] = tmpRow.slice();
    }
    this.varIndexByRow = new Array(this.height);
    this.varIndexByCol = new Array(this.width);
    this.varIndexByRow[0] = -1;
    this.varIndexByCol[0] = -1;
    this.nVars = width + height - 2;
    this.rowByVarIndex = new Array(this.nVars);
    this.colByVarIndex = new Array(this.nVars);
    this.lastElementIndex = this.nVars;
  };
  Tableau.prototype._resetMatrix = function() {
    var variables = this.model.variables;
    var constraints = this.model.constraints;
    var nVars = variables.length;
    var nConstraints = constraints.length;
    var v, varIndex;
    var costRow = this.matrix[0];
    var coeff = this.model.isMinimization === true ? -1 : 1;
    for (v = 0; v < nVars; v += 1) {
      var variable = variables[v];
      var priority = variable.priority;
      var cost = coeff * variable.cost;
      if (priority === 0) {
        costRow[v + 1] = cost;
      } else {
        this.setOptionalObjective(priority, v + 1, cost);
      }
      varIndex = variables[v].index;
      this.rowByVarIndex[varIndex] = -1;
      this.colByVarIndex[varIndex] = v + 1;
      this.varIndexByCol[v + 1] = varIndex;
    }
    var rowIndex = 1;
    for (var c = 0; c < nConstraints; c += 1) {
      var constraint = constraints[c];
      var constraintIndex = constraint.index;
      this.rowByVarIndex[constraintIndex] = rowIndex;
      this.colByVarIndex[constraintIndex] = -1;
      this.varIndexByRow[rowIndex] = constraintIndex;
      var t, term, column;
      var terms = constraint.terms;
      var nTerms = terms.length;
      var row = this.matrix[rowIndex++];
      if (constraint.isUpperBound) {
        for (t = 0; t < nTerms; t += 1) {
          term = terms[t];
          column = this.colByVarIndex[term.variable.index];
          row[column] = term.coefficient;
        }
        row[0] = constraint.rhs;
      } else {
        for (t = 0; t < nTerms; t += 1) {
          term = terms[t];
          column = this.colByVarIndex[term.variable.index];
          row[column] = -term.coefficient;
        }
        row[0] = -constraint.rhs;
      }
    }
  };
  Tableau.prototype.setModel = function(model) {
    this.model = model;
    var width = model.nVariables + 1;
    var height = model.nConstraints + 1;
    this.initialize(width, height, model.variables, model.unrestrictedVariables);
    this._resetMatrix();
    return this;
  };
  Tableau.prototype.getNewElementIndex = function() {
    if (this.availableIndexes.length > 0) {
      return this.availableIndexes.pop();
    }
    var index = this.lastElementIndex;
    this.lastElementIndex += 1;
    return index;
  };
  Tableau.prototype.density = function() {
    var density = 0;
    var matrix = this.matrix;
    for (var r = 0; r < this.height; r++) {
      var row = matrix[r];
      for (var c = 0; c < this.width; c++) {
        if (row[c] !== 0) {
          density += 1;
        }
      }
    }
    return density / (this.height * this.width);
  };
  Tableau.prototype.setEvaluation = function() {
    var roundingCoeff = Math.round(1 / this.precision);
    var evaluation = this.matrix[this.costRowIndex][this.rhsColumn];
    var roundedEvaluation = Math.round((Number.EPSILON + evaluation) * roundingCoeff) / roundingCoeff;
    this.evaluation = roundedEvaluation;
    if (this.simplexIters === 0) {
      this.bestPossibleEval = roundedEvaluation;
    }
  };
  Tableau.prototype.getSolution = function() {
    var evaluation = this.model.isMinimization === true ? this.evaluation : -this.evaluation;
    if (this.model.getNumberOfIntegerVariables() > 0) {
      return new MilpSolution_default(this, evaluation, this.feasible, this.bounded, this.branchAndCutIterations);
    } else {
      return new Solution_default(this, evaluation, this.feasible, this.bounded);
    }
  };

  // src/lp-solver/Tableau/simplex.js
  Tableau_default.prototype.simplex = function() {
    this.bounded = true;
    this.phase1();
    if (this.feasible === true) {
      this.phase2();
    }
    return this;
  };
  Tableau_default.prototype.phase1 = function() {
    var debugCheckForCycles = this.model.checkForCycles;
    var varIndexesCycle = [];
    var matrix = this.matrix;
    var rhsColumn = this.rhsColumn;
    var lastColumn = this.width - 1;
    var lastRow = this.height - 1;
    var unrestricted;
    var iterations = 0;
    while (true) {
      var leavingRowIndex = 0;
      var rhsValue = -this.precision;
      for (var r = 1; r <= lastRow; r++) {
        unrestricted = this.unrestrictedVars[this.varIndexByRow[r]] === true;
        var value = matrix[r][rhsColumn];
        if (value < rhsValue) {
          rhsValue = value;
          leavingRowIndex = r;
        }
      }
      if (leavingRowIndex === 0) {
        this.feasible = true;
        return iterations;
      }
      var enteringColumn = 0;
      var maxQuotient = -Infinity;
      var costRow = matrix[0];
      var leavingRow = matrix[leavingRowIndex];
      for (var c = 1; c <= lastColumn; c++) {
        var coefficient = leavingRow[c];
        unrestricted = this.unrestrictedVars[this.varIndexByCol[c]] === true;
        if (unrestricted || coefficient < -this.precision) {
          var quotient = -costRow[c] / coefficient;
          if (maxQuotient < quotient) {
            maxQuotient = quotient;
            enteringColumn = c;
          }
        }
      }
      if (enteringColumn === 0) {
        this.feasible = false;
        return iterations;
      }
      if (debugCheckForCycles) {
        varIndexesCycle.push([this.varIndexByRow[leavingRowIndex], this.varIndexByCol[enteringColumn]]);
        var cycleData = this.checkForCycles(varIndexesCycle);
        if (cycleData.length > 0) {
          this.model.messages.push("Cycle in phase 1");
          this.model.messages.push("Start :" + cycleData[0]);
          this.model.messages.push("Length :" + cycleData[1]);
          this.feasible = false;
          return iterations;
        }
      }
      this.pivot(leavingRowIndex, enteringColumn);
      iterations += 1;
    }
  };
  Tableau_default.prototype.phase2 = function() {
    var debugCheckForCycles = this.model.checkForCycles;
    var varIndexesCycle = [];
    var matrix = this.matrix;
    var rhsColumn = this.rhsColumn;
    var lastColumn = this.width - 1;
    var lastRow = this.height - 1;
    var precision = this.precision;
    var nOptionalObjectives = this.optionalObjectives.length;
    var optionalCostsColumns = null;
    var iterations = 0;
    var reducedCost, unrestricted;
    while (true) {
      var costRow = matrix[this.costRowIndex];
      if (nOptionalObjectives > 0) {
        optionalCostsColumns = [];
      }
      var enteringColumn = 0;
      var enteringValue = precision;
      var isReducedCostNegative = false;
      for (var c = 1; c <= lastColumn; c++) {
        reducedCost = costRow[c];
        unrestricted = this.unrestrictedVars[this.varIndexByCol[c]] === true;
        if (nOptionalObjectives > 0 && -precision < reducedCost && reducedCost < precision) {
          optionalCostsColumns.push(c);
          continue;
        }
        if (unrestricted && reducedCost < 0) {
          if (-reducedCost > enteringValue) {
            enteringValue = -reducedCost;
            enteringColumn = c;
            isReducedCostNegative = true;
          }
          continue;
        }
        if (reducedCost > enteringValue) {
          enteringValue = reducedCost;
          enteringColumn = c;
          isReducedCostNegative = false;
        }
      }
      if (nOptionalObjectives > 0) {
        var o = 0;
        while (enteringColumn === 0 && optionalCostsColumns.length > 0 && o < nOptionalObjectives) {
          var optionalCostsColumns2 = [];
          var reducedCosts = this.optionalObjectives[o].reducedCosts;
          enteringValue = precision;
          for (var i = 0; i < optionalCostsColumns.length; i++) {
            c = optionalCostsColumns[i];
            reducedCost = reducedCosts[c];
            unrestricted = this.unrestrictedVars[this.varIndexByCol[c]] === true;
            if (-precision < reducedCost && reducedCost < precision) {
              optionalCostsColumns2.push(c);
              continue;
            }
            if (unrestricted && reducedCost < 0) {
              if (-reducedCost > enteringValue) {
                enteringValue = -reducedCost;
                enteringColumn = c;
                isReducedCostNegative = true;
              }
              continue;
            }
            if (reducedCost > enteringValue) {
              enteringValue = reducedCost;
              enteringColumn = c;
              isReducedCostNegative = false;
            }
          }
          optionalCostsColumns = optionalCostsColumns2;
          o += 1;
        }
      }
      if (enteringColumn === 0) {
        this.setEvaluation();
        this.simplexIters += 1;
        return iterations;
      }
      var leavingRow = 0;
      var minQuotient = Infinity;
      var varIndexByRow = this.varIndexByRow;
      for (var r = 1; r <= lastRow; r++) {
        var row = matrix[r];
        var rhsValue = row[rhsColumn];
        var colValue = row[enteringColumn];
        if (-precision < colValue && colValue < precision) {
          continue;
        }
        if (colValue > 0 && precision > rhsValue && rhsValue > -precision) {
          minQuotient = 0;
          leavingRow = r;
          break;
        }
        var quotient = isReducedCostNegative ? -rhsValue / colValue : rhsValue / colValue;
        if (quotient > precision && minQuotient > quotient) {
          minQuotient = quotient;
          leavingRow = r;
        }
      }
      if (minQuotient === Infinity) {
        this.evaluation = -Infinity;
        this.bounded = false;
        this.unboundedVarIndex = this.varIndexByCol[enteringColumn];
        return iterations;
      }
      if (debugCheckForCycles) {
        varIndexesCycle.push([this.varIndexByRow[leavingRow], this.varIndexByCol[enteringColumn]]);
        var cycleData = this.checkForCycles(varIndexesCycle);
        if (cycleData.length > 0) {
          this.model.messages.push("Cycle in phase 2");
          this.model.messages.push("Start :" + cycleData[0]);
          this.model.messages.push("Length :" + cycleData[1]);
          this.feasible = false;
          return iterations;
        }
      }
      this.pivot(leavingRow, enteringColumn, true);
      iterations += 1;
    }
  };
  var nonZeroColumns = [];
  Tableau_default.prototype.pivot = function(pivotRowIndex, pivotColumnIndex) {
    var matrix = this.matrix;
    var quotient = matrix[pivotRowIndex][pivotColumnIndex];
    var lastRow = this.height - 1;
    var lastColumn = this.width - 1;
    var leavingBasicIndex = this.varIndexByRow[pivotRowIndex];
    var enteringBasicIndex = this.varIndexByCol[pivotColumnIndex];
    this.varIndexByRow[pivotRowIndex] = enteringBasicIndex;
    this.varIndexByCol[pivotColumnIndex] = leavingBasicIndex;
    this.rowByVarIndex[enteringBasicIndex] = pivotRowIndex;
    this.rowByVarIndex[leavingBasicIndex] = -1;
    this.colByVarIndex[enteringBasicIndex] = -1;
    this.colByVarIndex[leavingBasicIndex] = pivotColumnIndex;
    var pivotRow = matrix[pivotRowIndex];
    var nNonZeroColumns = 0;
    for (var c = 0; c <= lastColumn; c++) {
      if (!(pivotRow[c] >= -1e-16 && pivotRow[c] <= 1e-16)) {
        pivotRow[c] /= quotient;
        nonZeroColumns[nNonZeroColumns] = c;
        nNonZeroColumns += 1;
      } else {
        pivotRow[c] = 0;
      }
    }
    pivotRow[pivotColumnIndex] = 1 / quotient;
    var coefficient, i, v0;
    var precision = this.precision;
    for (var r = 0; r <= lastRow; r++) {
      if (r !== pivotRowIndex) {
        if (!(matrix[r][pivotColumnIndex] >= -1e-16 && matrix[r][pivotColumnIndex] <= 1e-16)) {
          var row = matrix[r];
          coefficient = row[pivotColumnIndex];
          if (!(coefficient >= -1e-16 && coefficient <= 1e-16)) {
            for (i = 0; i < nNonZeroColumns; i++) {
              c = nonZeroColumns[i];
              v0 = pivotRow[c];
              if (!(v0 >= -1e-16 && v0 <= 1e-16)) {
                row[c] = row[c] - coefficient * v0;
              } else {
                if (v0 !== 0) {
                  pivotRow[c] = 0;
                }
              }
            }
            row[pivotColumnIndex] = -coefficient / quotient;
          } else {
            if (coefficient !== 0) {
              row[pivotColumnIndex] = 0;
            }
          }
        }
      }
    }
    var nOptionalObjectives = this.optionalObjectives.length;
    if (nOptionalObjectives > 0) {
      for (var o = 0; o < nOptionalObjectives; o += 1) {
        var reducedCosts = this.optionalObjectives[o].reducedCosts;
        coefficient = reducedCosts[pivotColumnIndex];
        if (coefficient !== 0) {
          for (i = 0; i < nNonZeroColumns; i++) {
            c = nonZeroColumns[i];
            v0 = pivotRow[c];
            if (v0 !== 0) {
              reducedCosts[c] = reducedCosts[c] - coefficient * v0;
            }
          }
          reducedCosts[pivotColumnIndex] = -coefficient / quotient;
        }
      }
    }
  };
  Tableau_default.prototype.checkForCycles = function(varIndexes) {
    for (var e1 = 0; e1 < varIndexes.length - 1; e1++) {
      for (var e2 = e1 + 1; e2 < varIndexes.length; e2++) {
        var elt1 = varIndexes[e1];
        var elt2 = varIndexes[e2];
        if (elt1[0] === elt2[0] && elt1[1] === elt2[1]) {
          if (e2 - e1 > varIndexes.length - e2) {
            break;
          }
          var cycleFound = true;
          for (var i = 1; i < e2 - e1; i++) {
            var tmp1 = varIndexes[e1 + i];
            var tmp2 = varIndexes[e2 + i];
            if (tmp1[0] !== tmp2[0] || tmp1[1] !== tmp2[1]) {
              cycleFound = false;
              break;
            }
          }
          if (cycleFound) {
            return [e1, e2 - e1];
          }
        }
      }
    }
    return [];
  };

  // src/lp-solver/expressions.js
  function Variable(id, cost, index, priority) {
    this.id = id;
    this.cost = cost;
    this.index = index;
    this.value = 0;
    this.priority = priority;
  }
  function IntegerVariable(id, cost, index, priority) {
    Variable.call(this, id, cost, index, priority);
  }
  IntegerVariable.prototype.isInteger = true;
  function SlackVariable(id, index) {
    Variable.call(this, id, 0, index, 0);
  }
  SlackVariable.prototype.isSlack = true;
  function Term(variable, coefficient) {
    this.variable = variable;
    this.coefficient = coefficient;
  }
  function createRelaxationVariable(model, weight, priority) {
    if (priority === 0 || priority === "required") {
      return null;
    }
    weight = weight || 1;
    priority = priority || 1;
    if (model.isMinimization === false) {
      weight = -weight;
    }
    return model.addVariable(weight, "r" + model.relaxationIndex++, false, false, priority);
  }
  function Constraint(rhs, isUpperBound, index, model) {
    this.slack = new SlackVariable("s" + index, index);
    this.index = index;
    this.model = model;
    this.rhs = rhs;
    this.isUpperBound = isUpperBound;
    this.terms = [];
    this.termsByVarIndex = {};
    this.relaxation = null;
  }
  Constraint.prototype.addTerm = function(coefficient, variable) {
    var varIndex = variable.index;
    var term = this.termsByVarIndex[varIndex];
    if (term === void 0) {
      term = new Term(variable, coefficient);
      this.termsByVarIndex[varIndex] = term;
      this.terms.push(term);
      if (this.isUpperBound === true) {
        coefficient = -coefficient;
      }
      this.model.updateConstraintCoefficient(this, variable, coefficient);
    } else {
      var newCoefficient = term.coefficient + coefficient;
      this.setVariableCoefficient(newCoefficient, variable);
    }
    return this;
  };
  Constraint.prototype.removeTerm = function(term) {
    return this;
  };
  Constraint.prototype.setRightHandSide = function(newRhs) {
    if (newRhs !== this.rhs) {
      var difference = newRhs - this.rhs;
      if (this.isUpperBound === true) {
        difference = -difference;
      }
      this.rhs = newRhs;
      this.model.updateRightHandSide(this, difference);
    }
    return this;
  };
  Constraint.prototype.setVariableCoefficient = function(newCoefficient, variable) {
    var varIndex = variable.index;
    if (varIndex === -1) {
      console.warn("[Constraint.setVariableCoefficient] Trying to change coefficient of inexistant variable.");
      return;
    }
    var term = this.termsByVarIndex[varIndex];
    if (term === void 0) {
      this.addTerm(newCoefficient, variable);
    } else {
      if (newCoefficient !== term.coefficient) {
        var difference = newCoefficient - term.coefficient;
        if (this.isUpperBound === true) {
          difference = -difference;
        }
        term.coefficient = newCoefficient;
        this.model.updateConstraintCoefficient(this, variable, difference);
      }
    }
    return this;
  };
  Constraint.prototype.relax = function(weight, priority) {
    this.relaxation = createRelaxationVariable(this.model, weight, priority);
    this._relax(this.relaxation);
  };
  Constraint.prototype._relax = function(relaxationVariable) {
    if (relaxationVariable === null) {
      return;
    }
    if (this.isUpperBound) {
      this.setVariableCoefficient(-1, relaxationVariable);
    } else {
      this.setVariableCoefficient(1, relaxationVariable);
    }
  };
  function Equality(constraintUpper, constraintLower) {
    this.upperBound = constraintUpper;
    this.lowerBound = constraintLower;
    this.model = constraintUpper.model;
    this.rhs = constraintUpper.rhs;
    this.relaxation = null;
  }
  Equality.prototype.isEquality = true;
  Equality.prototype.addTerm = function(coefficient, variable) {
    this.upperBound.addTerm(coefficient, variable);
    this.lowerBound.addTerm(coefficient, variable);
    return this;
  };
  Equality.prototype.removeTerm = function(term) {
    this.upperBound.removeTerm(term);
    this.lowerBound.removeTerm(term);
    return this;
  };
  Equality.prototype.setRightHandSide = function(rhs) {
    this.upperBound.setRightHandSide(rhs);
    this.lowerBound.setRightHandSide(rhs);
    this.rhs = rhs;
  };
  Equality.prototype.relax = function(weight, priority) {
    this.relaxation = createRelaxationVariable(this.model, weight, priority);
    this.upperBound.relaxation = this.relaxation;
    this.upperBound._relax(this.relaxation);
    this.lowerBound.relaxation = this.relaxation;
    this.lowerBound._relax(this.relaxation);
  };

  // src/lp-solver/Tableau/cuttingStrategies.js
  Tableau_default.prototype.addCutConstraints = function(cutConstraints) {
    var nCutConstraints = cutConstraints.length;
    var height = this.height;
    var heightWithCuts = height + nCutConstraints;
    for (var h = height; h < heightWithCuts; h += 1) {
      if (this.matrix[h] === void 0) {
        this.matrix[h] = this.matrix[h - 1].slice();
      }
    }
    this.height = heightWithCuts;
    this.nVars = this.width + this.height - 2;
    var c;
    var lastColumn = this.width - 1;
    for (var i = 0; i < nCutConstraints; i += 1) {
      var cut = cutConstraints[i];
      var r = height + i;
      var sign = cut.type === "min" ? -1 : 1;
      var varIndex = cut.varIndex;
      var varRowIndex = this.rowByVarIndex[varIndex];
      var constraintRow = this.matrix[r];
      if (varRowIndex === -1) {
        constraintRow[this.rhsColumn] = sign * cut.value;
        for (c = 1; c <= lastColumn; c += 1) {
          constraintRow[c] = 0;
        }
        constraintRow[this.colByVarIndex[varIndex]] = sign;
      } else {
        var varRow = this.matrix[varRowIndex];
        var varValue = varRow[this.rhsColumn];
        constraintRow[this.rhsColumn] = sign * (cut.value - varValue);
        for (c = 1; c <= lastColumn; c += 1) {
          constraintRow[c] = -sign * varRow[c];
        }
      }
      var slackVarIndex = this.getNewElementIndex();
      this.varIndexByRow[r] = slackVarIndex;
      this.rowByVarIndex[slackVarIndex] = r;
      this.colByVarIndex[slackVarIndex] = -1;
      this.variablesPerIndex[slackVarIndex] = new SlackVariable("s" + slackVarIndex, slackVarIndex);
      this.nVars += 1;
    }
  };
  Tableau_default.prototype._addLowerBoundMIRCut = function(rowIndex) {
    if (rowIndex === this.costRowIndex) {
      return false;
    }
    var model = this.model;
    var matrix = this.matrix;
    var intVar = this.variablesPerIndex[this.varIndexByRow[rowIndex]];
    if (!intVar.isInteger) {
      return false;
    }
    var d = matrix[rowIndex][this.rhsColumn];
    var frac_d = d - Math.floor(d);
    if (frac_d < this.precision || 1 - this.precision < frac_d) {
      return false;
    }
    var r = this.height;
    matrix[r] = matrix[r - 1].slice();
    this.height += 1;
    this.nVars += 1;
    var slackVarIndex = this.getNewElementIndex();
    this.varIndexByRow[r] = slackVarIndex;
    this.rowByVarIndex[slackVarIndex] = r;
    this.colByVarIndex[slackVarIndex] = -1;
    this.variablesPerIndex[slackVarIndex] = new SlackVariable("s" + slackVarIndex, slackVarIndex);
    matrix[r][this.rhsColumn] = Math.floor(d);
    for (var colIndex = 1; colIndex < this.varIndexByCol.length; colIndex += 1) {
      var variable = this.variablesPerIndex[this.varIndexByCol[colIndex]];
      if (!variable.isInteger) {
        matrix[r][colIndex] = Math.min(0, matrix[rowIndex][colIndex] / (1 - frac_d));
      } else {
        var coef = matrix[rowIndex][colIndex];
        var termCoeff = Math.floor(coef) + Math.max(0, coef - Math.floor(coef) - frac_d) / (1 - frac_d);
        matrix[r][colIndex] = termCoeff;
      }
    }
    for (var c = 0; c < this.width; c += 1) {
      matrix[r][c] -= matrix[rowIndex][c];
    }
    return true;
  };
  Tableau_default.prototype._addUpperBoundMIRCut = function(rowIndex) {
    if (rowIndex === this.costRowIndex) {
      return false;
    }
    var model = this.model;
    var matrix = this.matrix;
    var intVar = this.variablesPerIndex[this.varIndexByRow[rowIndex]];
    if (!intVar.isInteger) {
      return false;
    }
    var b = matrix[rowIndex][this.rhsColumn];
    var f = b - Math.floor(b);
    if (f < this.precision || 1 - this.precision < f) {
      return false;
    }
    var r = this.height;
    matrix[r] = matrix[r - 1].slice();
    this.height += 1;
    this.nVars += 1;
    var slackVarIndex = this.getNewElementIndex();
    this.varIndexByRow[r] = slackVarIndex;
    this.rowByVarIndex[slackVarIndex] = r;
    this.colByVarIndex[slackVarIndex] = -1;
    this.variablesPerIndex[slackVarIndex] = new SlackVariable("s" + slackVarIndex, slackVarIndex);
    matrix[r][this.rhsColumn] = -f;
    for (var colIndex = 1; colIndex < this.varIndexByCol.length; colIndex += 1) {
      var variable = this.variablesPerIndex[this.varIndexByCol[colIndex]];
      var aj = matrix[rowIndex][colIndex];
      var fj = aj - Math.floor(aj);
      if (variable.isInteger) {
        if (fj <= f) {
          matrix[r][colIndex] = -fj;
        } else {
          matrix[r][colIndex] = -(1 - fj) * f / fj;
        }
      } else {
        if (aj >= 0) {
          matrix[r][colIndex] = -aj;
        } else {
          matrix[r][colIndex] = aj * f / (1 - f);
        }
      }
    }
    return true;
  };
  Tableau_default.prototype.applyMIRCuts = function() {
  };

  // src/lp-solver/Tableau/dynamicModification.js
  Tableau_default.prototype._putInBase = function(varIndex) {
    var r = this.rowByVarIndex[varIndex];
    if (r === -1) {
      var c = this.colByVarIndex[varIndex];
      for (var r1 = 1; r1 < this.height; r1 += 1) {
        var coefficient = this.matrix[r1][c];
        if (coefficient < -this.precision || this.precision < coefficient) {
          r = r1;
          break;
        }
      }
      this.pivot(r, c);
    }
    return r;
  };
  Tableau_default.prototype._takeOutOfBase = function(varIndex) {
    var c = this.colByVarIndex[varIndex];
    if (c === -1) {
      var r = this.rowByVarIndex[varIndex];
      var pivotRow = this.matrix[r];
      for (var c1 = 1; c1 < this.height; c1 += 1) {
        var coefficient = pivotRow[c1];
        if (coefficient < -this.precision || this.precision < coefficient) {
          c = c1;
          break;
        }
      }
      this.pivot(r, c);
    }
    return c;
  };
  Tableau_default.prototype.updateVariableValues = function() {
    var nVars = this.variables.length;
    var roundingCoeff = Math.round(1 / this.precision);
    for (var v = 0; v < nVars; v += 1) {
      var variable = this.variables[v];
      var varIndex = variable.index;
      var r = this.rowByVarIndex[varIndex];
      if (r === -1) {
        variable.value = 0;
      } else {
        var varValue = this.matrix[r][this.rhsColumn];
        variable.value = Math.round((varValue + Number.EPSILON) * roundingCoeff) / roundingCoeff;
      }
    }
  };
  Tableau_default.prototype.updateRightHandSide = function(constraint, difference) {
    var lastRow = this.height - 1;
    var constraintRow = this.rowByVarIndex[constraint.index];
    if (constraintRow === -1) {
      var slackColumn = this.colByVarIndex[constraint.index];
      for (var r = 0; r <= lastRow; r += 1) {
        var row = this.matrix[r];
        row[this.rhsColumn] -= difference * row[slackColumn];
      }
      var nOptionalObjectives = this.optionalObjectives.length;
      if (nOptionalObjectives > 0) {
        for (var o = 0; o < nOptionalObjectives; o += 1) {
          var reducedCosts = this.optionalObjectives[o].reducedCosts;
          reducedCosts[this.rhsColumn] -= difference * reducedCosts[slackColumn];
        }
      }
    } else {
      this.matrix[constraintRow][this.rhsColumn] -= difference;
    }
  };
  Tableau_default.prototype.updateConstraintCoefficient = function(constraint, variable, difference) {
    if (constraint.index === variable.index) {
      throw new Error("[Tableau.updateConstraintCoefficient] constraint index should not be equal to variable index !");
    }
    var r = this._putInBase(constraint.index);
    var colVar = this.colByVarIndex[variable.index];
    if (colVar === -1) {
      var rowVar = this.rowByVarIndex[variable.index];
      for (var c = 0; c < this.width; c += 1) {
        this.matrix[r][c] += difference * this.matrix[rowVar][c];
      }
    } else {
      this.matrix[r][colVar] -= difference;
    }
  };
  Tableau_default.prototype.updateCost = function(variable, difference) {
    var varIndex = variable.index;
    var lastColumn = this.width - 1;
    var varColumn = this.colByVarIndex[varIndex];
    if (varColumn === -1) {
      var variableRow = this.matrix[this.rowByVarIndex[varIndex]];
      var c;
      if (variable.priority === 0) {
        var costRow = this.matrix[0];
        for (c = 0; c <= lastColumn; c += 1) {
          costRow[c] += difference * variableRow[c];
        }
      } else {
        var reducedCosts = this.objectivesByPriority[variable.priority].reducedCosts;
        for (c = 0; c <= lastColumn; c += 1) {
          reducedCosts[c] += difference * variableRow[c];
        }
      }
    } else {
      this.matrix[0][varColumn] -= difference;
    }
  };
  Tableau_default.prototype.addConstraint = function(constraint) {
    var sign = constraint.isUpperBound ? 1 : -1;
    var lastRow = this.height;
    var constraintRow = this.matrix[lastRow];
    if (constraintRow === void 0) {
      constraintRow = this.matrix[0].slice();
      this.matrix[lastRow] = constraintRow;
    }
    var lastColumn = this.width - 1;
    for (var c = 0; c <= lastColumn; c += 1) {
      constraintRow[c] = 0;
    }
    constraintRow[this.rhsColumn] = sign * constraint.rhs;
    var terms = constraint.terms;
    var nTerms = terms.length;
    for (var t = 0; t < nTerms; t += 1) {
      var term = terms[t];
      var coefficient = term.coefficient;
      var varIndex = term.variable.index;
      var varRowIndex = this.rowByVarIndex[varIndex];
      if (varRowIndex === -1) {
        constraintRow[this.colByVarIndex[varIndex]] += sign * coefficient;
      } else {
        var varRow = this.matrix[varRowIndex];
        var varValue = varRow[this.rhsColumn];
        for (c = 0; c <= lastColumn; c += 1) {
          constraintRow[c] -= sign * coefficient * varRow[c];
        }
      }
    }
    var slackIndex = constraint.index;
    this.varIndexByRow[lastRow] = slackIndex;
    this.rowByVarIndex[slackIndex] = lastRow;
    this.colByVarIndex[slackIndex] = -1;
    this.height += 1;
  };
  Tableau_default.prototype.removeConstraint = function(constraint) {
    var slackIndex = constraint.index;
    var lastRow = this.height - 1;
    var r = this._putInBase(slackIndex);
    var tmpRow = this.matrix[lastRow];
    this.matrix[lastRow] = this.matrix[r];
    this.matrix[r] = tmpRow;
    this.varIndexByRow[r] = this.varIndexByRow[lastRow];
    this.varIndexByRow[lastRow] = -1;
    this.rowByVarIndex[slackIndex] = -1;
    this.availableIndexes[this.availableIndexes.length] = slackIndex;
    constraint.slack.index = -1;
    this.height -= 1;
  };
  Tableau_default.prototype.addVariable = function(variable) {
    var lastRow = this.height - 1;
    var lastColumn = this.width;
    var cost = this.model.isMinimization === true ? -variable.cost : variable.cost;
    var priority = variable.priority;
    var nOptionalObjectives = this.optionalObjectives.length;
    if (nOptionalObjectives > 0) {
      for (var o = 0; o < nOptionalObjectives; o += 1) {
        this.optionalObjectives[o].reducedCosts[lastColumn] = 0;
      }
    }
    if (priority === 0) {
      this.matrix[0][lastColumn] = cost;
    } else {
      this.setOptionalObjective(priority, lastColumn, cost);
      this.matrix[0][lastColumn] = 0;
    }
    for (var r = 1; r <= lastRow; r += 1) {
      this.matrix[r][lastColumn] = 0;
    }
    var varIndex = variable.index;
    this.varIndexByCol[lastColumn] = varIndex;
    this.rowByVarIndex[varIndex] = -1;
    this.colByVarIndex[varIndex] = lastColumn;
    this.width += 1;
  };
  Tableau_default.prototype.removeVariable = function(variable) {
    var varIndex = variable.index;
    var c = this._takeOutOfBase(varIndex);
    var lastColumn = this.width - 1;
    if (c !== lastColumn) {
      var lastRow = this.height - 1;
      for (var r = 0; r <= lastRow; r += 1) {
        var row = this.matrix[r];
        row[c] = row[lastColumn];
      }
      var nOptionalObjectives = this.optionalObjectives.length;
      if (nOptionalObjectives > 0) {
        for (var o = 0; o < nOptionalObjectives; o += 1) {
          var reducedCosts = this.optionalObjectives[o].reducedCosts;
          reducedCosts[c] = reducedCosts[lastColumn];
        }
      }
      var switchVarIndex = this.varIndexByCol[lastColumn];
      this.varIndexByCol[c] = switchVarIndex;
      this.colByVarIndex[switchVarIndex] = c;
    }
    this.varIndexByCol[lastColumn] = -1;
    this.colByVarIndex[varIndex] = -1;
    this.availableIndexes[this.availableIndexes.length] = varIndex;
    variable.index = -1;
    this.width -= 1;
  };

  // src/lp-solver/Tableau/log.js
  Tableau_default.prototype.log = function(message, force) {
    if (false) {
      return;
    }
    console.log("****", message, "****");
    console.log("Nb Variables", this.width - 1);
    console.log("Nb Constraints", this.height - 1);
    console.log("Basic Indexes", this.varIndexByRow);
    console.log("Non Basic Indexes", this.varIndexByCol);
    console.log("Rows", this.rowByVarIndex);
    console.log("Cols", this.colByVarIndex);
    var digitPrecision = 5;
    var varNameRowString = "", spacePerColumn = [" "], j, c, s, r, variable, varIndex, varName, varNameLength, nSpaces, valueSpace, nameSpace;
    var row, rowString;
    for (c = 1; c < this.width; c += 1) {
      varIndex = this.varIndexByCol[c];
      variable = this.variablesPerIndex[varIndex];
      if (variable === void 0) {
        varName = "c" + varIndex;
      } else {
        varName = variable.id;
      }
      varNameLength = varName.length;
      nSpaces = Math.abs(varNameLength - 5);
      valueSpace = " ";
      nameSpace = "	";
      if (varNameLength > 5) {
        valueSpace += " ";
      } else {
        nameSpace += "	";
      }
      spacePerColumn[c] = valueSpace;
      varNameRowString += nameSpace + varName;
    }
    console.log(varNameRowString);
    var signSpace;
    var firstRow = this.matrix[this.costRowIndex];
    var firstRowString = "	";
    for (j = 1; j < this.width; j += 1) {
      signSpace = "	";
      firstRowString += signSpace;
      firstRowString += spacePerColumn[j];
      firstRowString += firstRow[j].toFixed(digitPrecision);
    }
    signSpace = "	";
    firstRowString += signSpace + spacePerColumn[0] + firstRow[0].toFixed(digitPrecision);
    console.log(firstRowString + "	Z");
    for (r = 1; r < this.height; r += 1) {
      row = this.matrix[r];
      rowString = "	";
      for (c = 1; c < this.width; c += 1) {
        signSpace = "	";
        rowString += signSpace + spacePerColumn[c] + row[c].toFixed(digitPrecision);
      }
      signSpace = "	";
      rowString += signSpace + spacePerColumn[0] + row[0].toFixed(digitPrecision);
      varIndex = this.varIndexByRow[r];
      variable = this.variablesPerIndex[varIndex];
      if (variable === void 0) {
        varName = "c" + varIndex;
      } else {
        varName = variable.id;
      }
      console.log(rowString + "	" + varName);
    }
    console.log("");
    var nOptionalObjectives = this.optionalObjectives.length;
    if (nOptionalObjectives > 0) {
      console.log("    Optional objectives:");
      for (var o = 0; o < nOptionalObjectives; o += 1) {
        var reducedCosts = this.optionalObjectives[o].reducedCosts;
        var reducedCostsString = "";
        for (j = 1; j < this.width; j += 1) {
          signSpace = reducedCosts[j] < 0 ? "" : " ";
          reducedCostsString += signSpace;
          reducedCostsString += spacePerColumn[j];
          reducedCostsString += reducedCosts[j].toFixed(digitPrecision);
        }
        signSpace = reducedCosts[0] < 0 ? "" : " ";
        reducedCostsString += signSpace + spacePerColumn[0] + reducedCosts[0].toFixed(digitPrecision);
        console.log(reducedCostsString + " z" + o);
      }
    }
    console.log("Feasible?", this.feasible);
    console.log("evaluation", this.evaluation);
    return this;
  };

  // src/lp-solver/Tableau/backup.js
  Tableau_default.prototype.copy = function() {
    var copy = new Tableau_default(this.precision);
    copy.width = this.width;
    copy.height = this.height;
    copy.nVars = this.nVars;
    copy.model = this.model;
    copy.variables = this.variables;
    copy.variablesPerIndex = this.variablesPerIndex;
    copy.unrestrictedVars = this.unrestrictedVars;
    copy.lastElementIndex = this.lastElementIndex;
    copy.varIndexByRow = this.varIndexByRow.slice();
    copy.varIndexByCol = this.varIndexByCol.slice();
    copy.rowByVarIndex = this.rowByVarIndex.slice();
    copy.colByVarIndex = this.colByVarIndex.slice();
    copy.availableIndexes = this.availableIndexes.slice();
    var optionalObjectivesCopy = [];
    for (var o = 0; o < this.optionalObjectives.length; o++) {
      optionalObjectivesCopy[o] = this.optionalObjectives[o].copy();
    }
    copy.optionalObjectives = optionalObjectivesCopy;
    var matrix = this.matrix;
    var matrixCopy = new Array(this.height);
    for (var r = 0; r < this.height; r++) {
      matrixCopy[r] = matrix[r].slice();
    }
    copy.matrix = matrixCopy;
    return copy;
  };
  Tableau_default.prototype.save = function() {
    this.savedState = this.copy();
  };
  Tableau_default.prototype.restore = function() {
    if (this.savedState === null) {
      return;
    }
    var save = this.savedState;
    var savedMatrix = save.matrix;
    this.nVars = save.nVars;
    this.model = save.model;
    this.variables = save.variables;
    this.variablesPerIndex = save.variablesPerIndex;
    this.unrestrictedVars = save.unrestrictedVars;
    this.lastElementIndex = save.lastElementIndex;
    this.width = save.width;
    this.height = save.height;
    var r, c;
    for (r = 0; r < this.height; r += 1) {
      var savedRow = savedMatrix[r];
      var row = this.matrix[r];
      for (c = 0; c < this.width; c += 1) {
        row[c] = savedRow[c];
      }
    }
    var savedBasicIndexes = save.varIndexByRow;
    for (c = 0; c < this.height; c += 1) {
      this.varIndexByRow[c] = savedBasicIndexes[c];
    }
    while (this.varIndexByRow.length > this.height) {
      this.varIndexByRow.pop();
    }
    var savedNonBasicIndexes = save.varIndexByCol;
    for (r = 0; r < this.width; r += 1) {
      this.varIndexByCol[r] = savedNonBasicIndexes[r];
    }
    while (this.varIndexByCol.length > this.width) {
      this.varIndexByCol.pop();
    }
    var savedRows = save.rowByVarIndex;
    var savedCols = save.colByVarIndex;
    for (var v = 0; v < this.nVars; v += 1) {
      this.rowByVarIndex[v] = savedRows[v];
      this.colByVarIndex[v] = savedCols[v];
    }
    if (save.optionalObjectives.length > 0 && this.optionalObjectives.length > 0) {
      this.optionalObjectives = [];
      this.optionalObjectivePerPriority = {};
      for (var o = 0; o < save.optionalObjectives.length; o++) {
        var optionalObjectiveCopy = save.optionalObjectives[o].copy();
        this.optionalObjectives[o] = optionalObjectiveCopy;
        this.optionalObjectivePerPriority[optionalObjectiveCopy.priority] = optionalObjectiveCopy;
      }
    }
  };

  // src/lp-solver/Tableau/branchingStrategies.js
  function VariableData(index, value) {
    this.index = index;
    this.value = value;
  }
  Tableau_default.prototype.getMostFractionalVar = function() {
    var biggestFraction = 0;
    var selectedVarIndex = null;
    var selectedVarValue = null;
    var mid = 0.5;
    var integerVariables = this.model.integerVariables;
    var nIntegerVars = integerVariables.length;
    for (var v = 0; v < nIntegerVars; v++) {
      var varIndex = integerVariables[v].index;
      var varRow = this.rowByVarIndex[varIndex];
      if (varRow === -1) {
        continue;
      }
      var varValue = this.matrix[varRow][this.rhsColumn];
      var fraction = Math.abs(varValue - Math.round(varValue));
      if (biggestFraction < fraction) {
        biggestFraction = fraction;
        selectedVarIndex = varIndex;
        selectedVarValue = varValue;
      }
    }
    return new VariableData(selectedVarIndex, selectedVarValue);
  };
  Tableau_default.prototype.getFractionalVarWithLowestCost = function() {
    var highestCost = Infinity;
    var selectedVarIndex = null;
    var selectedVarValue = null;
    var integerVariables = this.model.integerVariables;
    var nIntegerVars = integerVariables.length;
    for (var v = 0; v < nIntegerVars; v++) {
      var variable = integerVariables[v];
      var varIndex = variable.index;
      var varRow = this.rowByVarIndex[varIndex];
      if (varRow === -1) {
        continue;
      }
      var varValue = this.matrix[varRow][this.rhsColumn];
      if (Math.abs(varValue - Math.round(varValue)) > this.precision) {
        var cost = variable.cost;
        if (highestCost > cost) {
          highestCost = cost;
          selectedVarIndex = varIndex;
          selectedVarValue = varValue;
        }
      }
    }
    return new VariableData(selectedVarIndex, selectedVarValue);
  };

  // src/lp-solver/Tableau/integerProperties.js
  Tableau_default.prototype.countIntegerValues = function() {
    var count = 0;
    for (var r = 1; r < this.height; r += 1) {
      if (this.variablesPerIndex[this.varIndexByRow[r]].isInteger) {
        var decimalPart = this.matrix[r][this.rhsColumn];
        decimalPart = decimalPart - Math.floor(decimalPart);
        if (decimalPart < this.precision && -decimalPart < this.precision) {
          count += 1;
        }
      }
    }
    return count;
  };
  Tableau_default.prototype.isIntegral = function() {
    var integerVariables = this.model.integerVariables;
    var nIntegerVars = integerVariables.length;
    for (var v = 0; v < nIntegerVars; v++) {
      var varRow = this.rowByVarIndex[integerVariables[v].index];
      if (varRow === -1) {
        continue;
      }
      var varValue = this.matrix[varRow][this.rhsColumn];
      if (Math.abs(varValue - Math.round(varValue)) > this.precision) {
        return false;
      }
    }
    return true;
  };
  Tableau_default.prototype.computeFractionalVolume = function(ignoreIntegerValues) {
    var volume = -1;
    for (var r = 1; r < this.height; r += 1) {
      if (this.variablesPerIndex[this.varIndexByRow[r]].isInteger) {
        var rhs = this.matrix[r][this.rhsColumn];
        rhs = Math.abs(rhs);
        var decimalPart = Math.min(rhs - Math.floor(rhs), Math.floor(rhs + 1));
        if (decimalPart < this.precision) {
          if (!ignoreIntegerValues) {
            return 0;
          }
        } else {
          if (volume === -1) {
            volume = rhs;
          } else {
            volume *= rhs;
          }
        }
      }
    }
    if (volume === -1) {
      return 0;
    }
    return volume;
  };

  // src/lp-solver/Tableau/index.js
  var Tableau_default2 = Tableau_default;

  // src/lp-solver/Model.js
  function Model(precision, name) {
    this.tableau = new Tableau_default(precision);
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
    this.messages = [];
  }
  var Model_default = Model;
  Model.prototype.minimize = function() {
    this.isMinimization = true;
    return this;
  };
  Model.prototype.maximize = function() {
    this.isMinimization = false;
    return this;
  };
  Model.prototype._getNewElementIndex = function() {
    if (this.availableIndexes.length > 0) {
      return this.availableIndexes.pop();
    }
    var index = this.lastElementIndex;
    this.lastElementIndex += 1;
    return index;
  };
  Model.prototype._addConstraint = function(constraint) {
    var slackVariable = constraint.slack;
    this.tableau.variablesPerIndex[slackVariable.index] = slackVariable;
    this.constraints.push(constraint);
    this.nConstraints += 1;
    if (this.tableauInitialized === true) {
      this.tableau.addConstraint(constraint);
    }
  };
  Model.prototype.smallerThan = function(rhs) {
    var constraint = new Constraint(rhs, true, this.tableau.getNewElementIndex(), this);
    this._addConstraint(constraint);
    return constraint;
  };
  Model.prototype.greaterThan = function(rhs) {
    var constraint = new Constraint(rhs, false, this.tableau.getNewElementIndex(), this);
    this._addConstraint(constraint);
    return constraint;
  };
  Model.prototype.equal = function(rhs) {
    var constraintUpper = new Constraint(rhs, true, this.tableau.getNewElementIndex(), this);
    this._addConstraint(constraintUpper);
    var constraintLower = new Constraint(rhs, false, this.tableau.getNewElementIndex(), this);
    this._addConstraint(constraintLower);
    return new Equality(constraintUpper, constraintLower);
  };
  Model.prototype.addVariable = function(cost, id, isInteger, isUnrestricted, priority) {
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
    if (id === null || id === void 0) {
      id = "v" + varIndex;
    }
    if (cost === null || cost === void 0) {
      cost = 0;
    }
    if (priority === null || priority === void 0) {
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
  Model.prototype._removeConstraint = function(constraint) {
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
  Model.prototype.removeConstraint = function(constraint) {
    if (constraint.isEquality) {
      this._removeConstraint(constraint.upperBound);
      this._removeConstraint(constraint.lowerBound);
    } else {
      this._removeConstraint(constraint);
    }
    return this;
  };
  Model.prototype.removeVariable = function(variable) {
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
  Model.prototype.updateRightHandSide = function(constraint, difference) {
    if (this.tableauInitialized === true) {
      this.tableau.updateRightHandSide(constraint, difference);
    }
    return this;
  };
  Model.prototype.updateConstraintCoefficient = function(constraint, variable, difference) {
    if (this.tableauInitialized === true) {
      this.tableau.updateConstraintCoefficient(constraint, variable, difference);
    }
    return this;
  };
  Model.prototype.setCost = function(cost, variable) {
    var difference = cost - variable.cost;
    if (this.isMinimization === false) {
      difference = -difference;
    }
    variable.cost = cost;
    this.tableau.updateCost(variable, difference);
    return this;
  };
  Model.prototype.loadJson = function(jsonModel) {
    this.isMinimization = jsonModel.opType !== "max";
    var variables = jsonModel.variables;
    var constraints = jsonModel.constraints;
    var constraintsMin = {};
    var constraintsMax = {};
    var constraintIds = Object.keys(constraints);
    var nConstraintIds = constraintIds.length;
    for (var c = 0; c < nConstraintIds; c += 1) {
      var constraintId = constraintIds[c];
      var constraint = constraints[constraintId];
      var equal = constraint.equal;
      var weight = constraint.weight;
      var priority = constraint.priority;
      var relaxed = weight !== void 0 || priority !== void 0;
      var lowerBound, upperBound;
      if (equal === void 0) {
        var min = constraint.min;
        if (min !== void 0) {
          lowerBound = this.greaterThan(min);
          constraintsMin[constraintId] = lowerBound;
          if (relaxed) {
            lowerBound.relax(weight, priority);
          }
        }
        var max = constraint.max;
        if (max !== void 0) {
          upperBound = this.smallerThan(max);
          constraintsMax[constraintId] = upperBound;
          if (relaxed) {
            upperBound.relax(weight, priority);
          }
        }
      } else {
        lowerBound = this.greaterThan(equal);
        constraintsMin[constraintId] = lowerBound;
        upperBound = this.smallerThan(equal);
        constraintsMax[constraintId] = upperBound;
        var equality = new Equality(lowerBound, upperBound);
        if (relaxed) {
          equality.relax(weight, priority);
        }
      }
    }
    var variableIds = Object.keys(variables);
    var nVariables = variableIds.length;
    this.tolerance = jsonModel.tolerance || 0;
    if (jsonModel.timeout) {
      this.timeout = jsonModel.timeout;
    }
    if (jsonModel.options) {
      if (jsonModel.options.timeout) {
        this.timeout = jsonModel.options.timeout;
      }
      if (this.tolerance === 0) {
        this.tolerance = jsonModel.options.tolerance || 0;
      }
      if (jsonModel.options.useMIRCuts) {
        this.useMIRCuts = jsonModel.options.useMIRCuts;
      }
      if (typeof jsonModel.options.exitOnCycles === "undefined") {
        this.checkForCycles = true;
      } else {
        this.checkForCycles = jsonModel.options.exitOnCycles;
      }
      if (jsonModel.options.keep_solutions) {
        this.keep_solutions = jsonModel.options.keep_solutions;
      } else {
        this.keep_solutions = false;
      }
    }
    var integerVarIds = jsonModel.ints || {};
    var binaryVarIds = jsonModel.binaries || {};
    var unrestrictedVarIds = jsonModel.unrestricted || {};
    var objectiveName = jsonModel.optimize;
    for (var v = 0; v < nVariables; v += 1) {
      var variableId = variableIds[v];
      var variableConstraints = variables[variableId];
      var cost = variableConstraints[objectiveName] || 0;
      var isBinary = !!binaryVarIds[variableId];
      var isInteger = !!integerVarIds[variableId] || isBinary;
      var isUnrestricted = !!unrestrictedVarIds[variableId];
      var variable = this.addVariable(cost, variableId, isInteger, isUnrestricted);
      if (isBinary) {
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
        if (constraintMin !== void 0) {
          constraintMin.addTerm(coefficient, variable);
        }
        var constraintMax = constraintsMax[constraintName];
        if (constraintMax !== void 0) {
          constraintMax.addTerm(coefficient, variable);
        }
      }
    }
    return this;
  };
  Model.prototype.getNumberOfIntegerVariables = function() {
    return this.integerVariables.length;
  };
  Model.prototype.solve = function() {
    if (this.tableauInitialized === false) {
      this.tableau.setModel(this);
      this.tableauInitialized = true;
    }
    return this.tableau.solve();
  };
  Model.prototype.isFeasible = function() {
    return this.tableau.feasible;
  };
  Model.prototype.save = function() {
    return this.tableau.save();
  };
  Model.prototype.restore = function() {
    return this.tableau.restore();
  };
  Model.prototype.activateMIRCuts = function(useMIRCuts) {
    this.useMIRCuts = useMIRCuts;
  };
  Model.prototype.debug = function(debugCheckForCycles) {
    this.checkForCycles = debugCheckForCycles;
  };
  Model.prototype.log = function(message) {
    return this.tableau.log(message);
  };

  // src/lp-solver/Tableau/branchAndCut.js
  var branchAndCut_exports = {};
  __markAsModule(branchAndCut_exports);
  function Cut(type, varIndex, value) {
    this.type = type;
    this.varIndex = varIndex;
    this.value = value;
  }
  function Branch(relaxedEvaluation, cuts) {
    this.relaxedEvaluation = relaxedEvaluation;
    this.cuts = cuts;
  }
  function sortByEvaluation(a, b) {
    return b.relaxedEvaluation - a.relaxedEvaluation;
  }
  Tableau_default.prototype.applyCuts = function(branchingCuts) {
    this.restore();
    this.addCutConstraints(branchingCuts);
    this.simplex();
    if (this.model.useMIRCuts) {
      var fractionalVolumeImproved = true;
      while (fractionalVolumeImproved) {
        var fractionalVolumeBefore = this.computeFractionalVolume(true);
        this.applyMIRCuts();
        this.simplex();
        var fractionalVolumeAfter = this.computeFractionalVolume(true);
        if (fractionalVolumeAfter >= 0.9 * fractionalVolumeBefore) {
          fractionalVolumeImproved = false;
        }
      }
    }
  };
  Tableau_default.prototype.branchAndCut = function() {
    var branches = [];
    var iterations = 0;
    var tolerance = this.model.tolerance;
    var toleranceFlag = true;
    var terminalTime = 1e99;
    if (this.model.timeout) {
      terminalTime = Date.now() + this.model.timeout;
    }
    var bestEvaluation = Infinity;
    var bestBranch = null;
    var bestOptionalObjectivesEvaluations = [];
    for (var oInit = 0; oInit < this.optionalObjectives.length; oInit += 1) {
      bestOptionalObjectivesEvaluations.push(Infinity);
    }
    var branch = new Branch(-Infinity, []);
    var acceptableThreshold;
    branches.push(branch);
    while (branches.length > 0 && toleranceFlag === true && Date.now() < terminalTime) {
      if (this.model.isMinimization) {
        acceptableThreshold = this.bestPossibleEval * (1 + tolerance);
      } else {
        acceptableThreshold = this.bestPossibleEval * (1 - tolerance);
      }
      if (tolerance > 0) {
        if (bestEvaluation < acceptableThreshold) {
          toleranceFlag = false;
        }
      }
      branch = branches.pop();
      if (branch.relaxedEvaluation > bestEvaluation) {
        continue;
      }
      var cuts = branch.cuts;
      this.applyCuts(cuts);
      iterations++;
      if (this.feasible === false) {
        continue;
      }
      var evaluation = this.evaluation;
      if (evaluation > bestEvaluation) {
        continue;
      }
      if (evaluation === bestEvaluation) {
        var isCurrentEvaluationWorse = true;
        for (var o = 0; o < this.optionalObjectives.length; o += 1) {
          if (this.optionalObjectives[o].reducedCosts[0] > bestOptionalObjectivesEvaluations[o]) {
            break;
          } else if (this.optionalObjectives[o].reducedCosts[0] < bestOptionalObjectivesEvaluations[o]) {
            isCurrentEvaluationWorse = false;
            break;
          }
        }
        if (isCurrentEvaluationWorse) {
          continue;
        }
      }
      if (this.isIntegral() === true) {
        this.__isIntegral = true;
        if (iterations === 1) {
          this.branchAndCutIterations = iterations;
          return;
        }
        bestBranch = branch;
        bestEvaluation = evaluation;
        for (var oCopy = 0; oCopy < this.optionalObjectives.length; oCopy += 1) {
          bestOptionalObjectivesEvaluations[oCopy] = this.optionalObjectives[oCopy].reducedCosts[0];
        }
        if (this.model.keep_solutions) {
          var nowSolution = this.model.tableau.getSolution();
          var store = nowSolution.generateSolutionSet();
          store.result = nowSolution.evaluation;
          if (!this.model.solutions) {
            this.model.solutions = [];
          }
          this.model.solutions.push(store);
        }
      } else {
        if (iterations === 1) {
          this.save();
        }
        var variable = this.getMostFractionalVar();
        var varIndex = variable.index;
        var cutsHigh = [];
        var cutsLow = [];
        var nCuts = cuts.length;
        for (var c = 0; c < nCuts; c += 1) {
          var cut = cuts[c];
          if (cut.varIndex === varIndex) {
            if (cut.type === "min") {
              cutsLow.push(cut);
            } else {
              cutsHigh.push(cut);
            }
          } else {
            cutsHigh.push(cut);
            cutsLow.push(cut);
          }
        }
        var min = Math.ceil(variable.value);
        var max = Math.floor(variable.value);
        var cutHigh = new Cut("min", varIndex, min);
        cutsHigh.push(cutHigh);
        var cutLow = new Cut("max", varIndex, max);
        cutsLow.push(cutLow);
        branches.push(new Branch(evaluation, cutsHigh));
        branches.push(new Branch(evaluation, cutsLow));
        branches.sort(sortByEvaluation);
      }
    }
    if (bestBranch !== null) {
      this.applyCuts(bestBranch.cuts);
    }
    this.branchAndCutIterations = iterations;
  };

  // src/lp-solver/Validation.js
  var CleanObjectiveAttributes = function(model) {
    var fakeAttr, x, z;
    if (typeof model.optimize === "string") {
      if (model.constraints[model.optimize]) {
        fakeAttr = Math.random();
        for (x in model.variables) {
          if (model.variables[x][model.optimize]) {
            model.variables[x][fakeAttr] = model.variables[x][model.optimize];
          }
        }
        model.constraints[fakeAttr] = model.constraints[model.optimize];
        delete model.constraints[model.optimize];
        return model;
      } else {
        return model;
      }
    } else {
      for (z in model.optimize) {
        if (model.constraints[z]) {
          if (model.constraints[z] === "equal") {
            delete model.optimize[z];
          } else {
            fakeAttr = Math.random();
            for (x in model.variables) {
              if (model.variables[x][z]) {
                model.variables[x][fakeAttr] = model.variables[x][z];
              }
            }
            model.constraints[fakeAttr] = model.constraints[z];
            delete model.constraints[z];
          }
        }
      }
      return model;
    }
  };
  var Validation_default = { CleanObjectiveAttributes };

  // src/lp-solver/External/lpsolve/Reformat.js
  function to_JSON(input) {
    var rxo = {
      "is_blank": /^\W{0,}$/,
      "is_objective": /(max|min)(imize){0,}\:/i,
      "is_int": /^(?!\/\*)\W{0,}int/i,
      "is_bin": /^(?!\/\*)\W{0,}bin/i,
      "is_constraint": /(\>|\<){0,}\=/i,
      "is_unrestricted": /^\S{0,}unrestricted/i,
      "parse_lhs": /(\-|\+){0,1}\s{0,1}\d{0,}\.{0,}\d{0,}\s{0,}[A-Za-z]\S{0,}/gi,
      "parse_rhs": /(\-|\+){0,1}\d{1,}\.{0,}\d{0,}\W{0,}\;{0,1}$/i,
      "parse_dir": /(\>|\<){0,}\=/gi,
      "parse_int": /[^\s|^\,]+/gi,
      "parse_bin": /[^\s|^\,]+/gi,
      "get_num": /(\-|\+){0,1}(\W|^)\d+\.{0,1}\d{0,}/g,
      "get_word": /[A-Za-z].*/
    }, model = {
      "opType": "",
      "optimize": "_obj",
      "constraints": {},
      "variables": {}
    }, constraints = {
      ">=": "min",
      "<=": "max",
      "=": "equal"
    }, tmp = "", tst = 0, ary = null, hldr = "", hldr2 = "", constraint = "", rhs = 0;
    if (typeof input === "string") {
      input = input.split("\n");
    }
    for (var i = 0; i < input.length; i++) {
      constraint = "__" + i;
      tmp = input[i];
      tst = 0;
      ary = null;
      if (rxo.is_objective.test(tmp)) {
        model.opType = tmp.match(/(max|min)/gi)[0];
        ary = tmp.match(rxo.parse_lhs).map(function(d) {
          return d.replace(/\s+/, "");
        }).slice(1);
        ary.forEach(function(d) {
          hldr = d.match(rxo.get_num);
          if (hldr === null) {
            if (d.substr(0, 1) === "-") {
              hldr = -1;
            } else {
              hldr = 1;
            }
          } else {
            hldr = hldr[0];
          }
          hldr = parseFloat(hldr);
          hldr2 = d.match(rxo.get_word)[0].replace(/\;$/, "");
          model.variables[hldr2] = model.variables[hldr2] || {};
          model.variables[hldr2]._obj = hldr;
        });
      } else if (rxo.is_int.test(tmp)) {
        ary = tmp.match(rxo.parse_int).slice(1);
        model.ints = model.ints || {};
        ary.forEach(function(d) {
          d = d.replace(";", "");
          model.ints[d] = 1;
        });
      } else if (rxo.is_bin.test(tmp)) {
        ary = tmp.match(rxo.parse_bin).slice(1);
        model.binaries = model.binaries || {};
        ary.forEach(function(d) {
          d = d.replace(";", "");
          model.binaries[d] = 1;
        });
      } else if (rxo.is_constraint.test(tmp)) {
        var separatorIndex = tmp.indexOf(":");
        var constraintExpression = separatorIndex === -1 ? tmp : tmp.slice(separatorIndex + 1);
        ary = constraintExpression.match(rxo.parse_lhs).map(function(d) {
          return d.replace(/\s+/, "");
        });
        ary.forEach(function(d) {
          hldr = d.match(rxo.get_num);
          if (hldr === null) {
            if (d.substr(0, 1) === "-") {
              hldr = -1;
            } else {
              hldr = 1;
            }
          } else {
            hldr = hldr[0];
          }
          hldr = parseFloat(hldr);
          hldr2 = d.match(rxo.get_word)[0];
          model.variables[hldr2] = model.variables[hldr2] || {};
          model.variables[hldr2][constraint] = hldr;
        });
        rhs = parseFloat(tmp.match(rxo.parse_rhs)[0]);
        tmp = constraints[tmp.match(rxo.parse_dir)[0]];
        model.constraints[constraint] = model.constraints[constraint] || {};
        model.constraints[constraint][tmp] = rhs;
      } else if (rxo.is_unrestricted.test(tmp)) {
        ary = tmp.match(rxo.parse_int).slice(1);
        model.unrestricted = model.unrestricted || {};
        ary.forEach(function(d) {
          d = d.replace(";", "");
          model.unrestricted[d] = 1;
        });
      }
    }
    return model;
  }
  function from_JSON(model) {
    if (!model) {
      throw new Error("Solver requires a model to operate on");
    }
    var output = "", ary = [], norm = 1, lookup = {
      "max": "<=",
      "min": ">=",
      "equal": "="
    }, rxClean = new RegExp("[^A-Za-z0-9_[{}/.&#$%~'@^]", "gi");
    if (model.opType) {
      output += model.opType + ":";
      for (var x in model.variables) {
        model.variables[x][x] = model.variables[x][x] ? model.variables[x][x] : 1;
        if (model.variables[x][model.optimize]) {
          output += " " + model.variables[x][model.optimize] + " " + x.replace(rxClean, "_");
        }
      }
    } else {
      output += "max:";
    }
    output += ";\n\n";
    for (var xx in model.constraints) {
      for (var y in model.constraints[xx]) {
        if (typeof lookup[y] !== "undefined") {
          for (var z in model.variables) {
            if (typeof model.variables[z][xx] !== "undefined") {
              output += " " + model.variables[z][xx] + " " + z.replace(rxClean, "_");
            }
          }
          output += " " + lookup[y] + " " + model.constraints[xx][y];
          output += ";\n";
        }
      }
    }
    if (model.ints) {
      output += "\n\n";
      for (var xxx in model.ints) {
        output += "int " + xxx.replace(rxClean, "_") + ";\n";
      }
    }
    if (model.unrestricted) {
      output += "\n\n";
      for (var xxxx in model.unrestricted) {
        output += "unrestricted " + xxxx.replace(rxClean, "_") + ";\n";
      }
    }
    return output;
  }
  function Reformat_default(model) {
    if (model.length) {
      return to_JSON(model);
    } else {
      return from_JSON(model);
    }
  }

  // src/lp-solver/External/lpsolve/main.js
  var fs = { writeFile: () => {
    debugger;
  } };
  var exec = () => {
    debugger;
  };
  function clean_data(data) {
    data = data.replace("\\r\\n", "\r\n");
    data = data.split("\r\n");
    data = data.filter(function(x) {
      var rx;
      rx = new RegExp(" 0$", "gi");
      if (rx.test(x) === true) {
        return false;
      }
      rx = new RegExp("\\d$", "gi");
      if (rx.test(x) === false) {
        return false;
      }
      return true;
    }).map(function(x) {
      return x.split(/\:{0,1} +(?=\d)/);
    }).reduce(function(o, k, i) {
      o[k[0]] = k[1];
      return o;
    }, {});
    return data;
  }
  function solve(model) {
    return new Promise(function(res, rej) {
      if (typeof window !== "undefined") {
        rej("Function Not Available in Browser");
      }
      var data = Reformat_default(model);
      if (!model.external) {
        rej("Data for this function must be contained in the 'external' attribute. Not seeing anything there.");
      }
      if (!model.external.binPath) {
        rej("No Executable | Binary path provided in arguments as 'binPath'");
      }
      if (!model.external.args) {
        rej("No arguments array for cli | bash provided on 'args' attribute");
      }
      if (!model.external.tempName) {
        rej("No 'tempName' given. This is necessary to produce a staging file for the solver to operate on");
      }
      fs.writeFile(model.external.tempName, data, function(fe, fd) {
        if (fe) {
          rej(fe);
        } else {
          model.external.args.push(model.external.tempName);
          exec(model.external.binPath, model.external.args, function(e, data2) {
            if (e) {
              if (e.code === 1) {
                res(clean_data(data2));
              } else {
                var codes = {
                  "-2": "Out of Memory",
                  "1": "SUBOPTIMAL",
                  "2": "INFEASIBLE",
                  "3": "UNBOUNDED",
                  "4": "DEGENERATE",
                  "5": "NUMFAILURE",
                  "6": "USER-ABORT",
                  "7": "TIMEOUT",
                  "9": "PRESOLVED",
                  "25": "ACCURACY ERROR",
                  "255": "FILE-ERROR"
                };
                var ret_obj = {
                  "code": e.code,
                  "meaning": codes[e.code],
                  "data": data2
                };
                rej(ret_obj);
              }
            } else {
              res(clean_data(data2));
            }
          });
        }
      });
    });
  }

  // src/lp-solver/External/main.js
  var main_default = { lpsolve: solve };

  // src/lp-solver/Polyopt.js
  function Polyopt_default(solver, model) {
    var objectives = model.optimize, new_constraints = JSON.parse(JSON.stringify(model.optimize)), keys = Object.keys(model.optimize), tmp, counter = 0, vectors = {}, vector_key = "", obj = {}, pareto = [], i, j, x, y, z;
    delete model.optimize;
    for (i = 0; i < keys.length; i++) {
      new_constraints[keys[i]] = 0;
    }
    for (i = 0; i < keys.length; i++) {
      model.optimize = keys[i];
      model.opType = objectives[keys[i]];
      tmp = solver.Solve(model, void 0, void 0, true);
      for (y in keys) {
        if (!model.variables[keys[y]]) {
          tmp[keys[y]] = tmp[keys[y]] ? tmp[keys[y]] : 0;
          for (x in model.variables) {
            if (model.variables[x][keys[y]] && tmp[x]) {
              tmp[keys[y]] += tmp[x] * model.variables[x][keys[y]];
            }
          }
        }
      }
      vector_key = "base";
      for (j = 0; j < keys.length; j++) {
        if (tmp[keys[j]]) {
          vector_key += "-" + (tmp[keys[j]] * 1e3 | 0) / 1e3;
        } else {
          vector_key += "-0";
        }
      }
      if (!vectors[vector_key]) {
        vectors[vector_key] = 1;
        counter++;
        for (j = 0; j < keys.length; j++) {
          if (tmp[keys[j]]) {
            new_constraints[keys[j]] += tmp[keys[j]];
          }
        }
        delete tmp.feasible;
        delete tmp.result;
        pareto.push(tmp);
      }
    }
    for (i = 0; i < keys.length; i++) {
      model.constraints[keys[i]] = { "equal": new_constraints[keys[i]] / counter };
    }
    model.optimize = "cheater-" + Math.random();
    model.opType = "max";
    for (i in model.variables) {
      model.variables[i].cheater = 1;
    }
    for (i in pareto) {
      for (x in pareto[i]) {
        obj[x] = obj[x] || { min: 1e99, max: -1e99 };
      }
    }
    for (i in obj) {
      for (x in pareto) {
        if (pareto[x][i]) {
          if (pareto[x][i] > obj[i].max) {
            obj[i].max = pareto[x][i];
          }
          if (pareto[x][i] < obj[i].min) {
            obj[i].min = pareto[x][i];
          }
        } else {
          pareto[x][i] = 0;
          obj[i].min = 0;
        }
      }
    }
    tmp = solver.Solve(model, void 0, void 0, true);
    return {
      midpoint: tmp,
      vertices: pareto,
      ranges: obj
    };
  }

  // src/lp-solver/main.js
  var Solver = function() {
    "use strict";
    this.Model = Model_default;
    this.branchAndCut = branchAndCut_exports;
    this.Constraint = Constraint;
    this.Variable = Variable;
    this.Term = Term;
    this.Tableau = Tableau_default2;
    this.lastSolvedModel = null;
    this.External = main_default;
    this.Solve = function(model, precision, full, validate) {
      if (validate) {
        for (var test in Validation_default) {
          model = Validation_default[test](model);
        }
      }
      if (!model) {
        throw new Error("Solver requires a model to operate on");
      }
      if (typeof model.optimize === "object") {
        if (Object.keys(model.optimize > 1)) {
          return Polyopt_default(this, model);
        }
      }
      if (model.external) {
        var solvers = Object.keys(main_default);
        solvers = JSON.stringify(solvers);
        if (!model.external.solver) {
          throw new Error("The model you provided has an 'external' object that doesn't have a solver attribute. Use one of the following:" + solvers);
        }
        if (!main_default[model.external.solver]) {
          throw new Error("No support (yet) for " + model.external.solver + ". Please use one of these instead:" + solvers);
        }
        return main_default[model.external.solver].solve(model);
      } else {
        if (model instanceof Model_default === false) {
          model = new Model_default(precision).loadJson(model);
        }
        var solution = model.solve();
        this.lastSolvedModel = model;
        solution.solutionSet = solution.generateSolutionSet();
        if (full) {
          return solution;
        } else {
          var store = {};
          store.feasible = solution.feasible;
          store.result = solution.evaluation;
          store.bounded = solution.bounded;
          if (solution._tableau.__isIntegral) {
            store.isIntegral = true;
          }
          Object.keys(solution.solutionSet).forEach(function(d) {
            if (solution.solutionSet[d] !== 0) {
              store[d] = solution.solutionSet[d];
            }
          });
          return store;
        }
      }
    };
    this.ReformatLP = Reformat_default;
    this.MultiObjective = function(model) {
      return Polyopt_default(this, model);
    };
  };
  var main_default2 = Solver;

  // src/prog.ts
  {
    let toSolverModel = function(recipes, int = false) {
      let model = { optimize: "profit", opType: "max", constraints: {}, variables: {}, ints: {}, options: { tolerance: 0.01 } };
      for (let r of recipes) {
        for (let k of Object.keys(r.components)) {
          model.constraints[k] = { min: 0 };
        }
      }
      model.constraints["round"] = { min: -1 };
      for (let r of recipes) {
        if (r.text == "")
          continue;
        let v = {};
        for (let c in r.components) {
          v[c] = -r.components[c];
        }
        for (let c in r.result) {
          v[c] = r.result[c];
        }
        model.variables[r.text] = v;
        if (int)
          model.ints[r.text] = true;
      }
      return model;
    }, solve2 = function() {
      let recipes = IN.value.split(";").map((s) => new Recipe(s));
      const solver = new main_default2();
      let intModel;
      let result = [true, false].map((int) => {
        let model = toSolverModel(recipes, int);
        intModel != null ? intModel : intModel = model;
        let t0 = performance.now();
        let results = solver.Solve(model);
        let dt = performance.now() - t0;
        return `${int ? "integer" : "float"} solution in ${dt} ms:

${JSON.stringify(results, null, 2)}

`;
      }).join("") + `model for integer solution (float is the same without the ints block):
${JSON.stringify(intModel, null, 2)}`;
      OUT.value = result;
    };
    class Recipe {
      constructor(text2) {
        text2 = text2.replace(/[ =\r\n]/g, "");
        this.text = text2;
        let parts = text2.split(">").map((part) => {
          let o = Object.fromEntries(part.split("+").map((bit) => {
            let bs = bit.split("*");
            bs[1] = Number(bs[1] || "1");
            return bs;
          }));
          delete o[""];
          return o;
        });
        [this.components, this.result] = parts;
      }
      calculateProfit(prices) {
        let p = 0;
        for (let n in this.components) {
          p -= (prices[n] || 1) * this.components[n];
        }
        for (let n in this.result) {
          p += (prices[n] || 1) * this.result[n];
        }
        return p;
      }
    }
    let text = `round=>farmer*3+miner*2+hunter+crafter+farmland*3+ironMine*3+forest*5;
farmer=>worker;
miner=>worker;
hunter=>worker;
crafter=>worker;
worker=>mining*5;
worker=>farming*5;
worker=>hunting*5;
worker=>crafting*3;
miner=>mining*10;
farmer=>farming*10;
hunter=>hunting*10;
crafter=>crafting*10;
ironMine+mining*10+tool=>iron*10;
ironMine+mining*10=>iron*3;
iron*3+crafting=>tool;
farmland+farming*10=>grain*10;
farmland+farming*5+tool=>grain*15;
forest+hunting*10=>meat*5;
forest+hunting*10+tool=>meat*10;
grain=>profit;
meat=>profit*2;
tool=>profit*5;`;
    IN.value = text;
    for (let i = 0; i < 5; i++)
      solve2();
    IN.addEventListener("input", () => {
      solve2();
    });
  }
})();
