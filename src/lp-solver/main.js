/*global describe*/
/*global require*/
/*global module*/
/*global it*/
/*global console*/
/*global process*/
/*global setTimeout*/
/*global self*/


//-------------------------------------------------------------------
// SimplexJS
// https://github.com/
// An Object-Oriented Linear Programming Solver
//
// By Justin Wolcott (c)
// Licensed under the MIT License.
//-------------------------------------------------------------------

import Tableau from "./Tableau/index.js";
import Model from "./Model.js";
import * as branchAndCut from "./Tableau/branchAndCut.js";
import validation from "./Validation.js";
import { Constraint, Variable, Term } from "./expressions.js";
import External from "./External/main.js";
import ReformatLP from "./External/lpsolve/Reformat.js";
import Polyopt from "./Polyopt.js";

// Place everything under the Solver Name Space
var Solver = function () {

    "use strict";

    this.Model = Model;
    this.branchAndCut = branchAndCut;
    this.Constraint = Constraint;
    this.Variable = Variable;
    this.Term = Term;
    this.Tableau = Tableau;
    this.lastSolvedModel = null;

    this.External = External;

    /*************************************************************
     * Method: Solve
     * Scope: Public:
     * Agruments:
     *        model: The model we want solver to operate on
     *        precision: If we're solving a MILP, how tight
     *                   do we want to define an integer, given
     *                   that 20.000000000000001 is not an integer.
     *                   (defaults to 1e-9)
     *            full: *get better description*
     *        validate: if left blank, it will get ignored; otherwise
     *                  it will run the model through all validation
     *                  functions in the *Validate* module
     **************************************************************/
    this.Solve = function (model, precision, full, validate) {
        //
        // Run our validations on the model
        // if the model doesn't have a validate
        // attribute set to false
        //
        if(validate){
            for(var test in validation){
                model = validation[test](model);
            }
        }

        // Make sure we at least have a model
        if (!model) {
            throw new Error("Solver requires a model to operate on");
        }

        //
        // If the objective function contains multiple objectives,
        // pass it to the multi-solver thing...
        //
        if(typeof model.optimize === "object"){
            if(Object.keys(model.optimize > 1)){
                return Polyopt(this, model);
            }
        }

// /////////////////////////////////////////////////////////////////////
// *********************************************************************
// START
// Try our hand at handling external solvers...
// START
// *********************************************************************
// /////////////////////////////////////////////////////////////////////
        if(model.external){

            var solvers = Object.keys(External);
            solvers = JSON.stringify(solvers);
            
            //
            // The model needs to have a "solver" attribute if nothing else
            // for us to pass data into
            //
            if(!model.external.solver){
                throw new Error("The model you provided has an 'external' object that doesn't have a solver attribute. Use one of the following:" + solvers);
            }
            
            //
            // If the solver they request doesn't exist; provide them
            // with a list of possible options:
            //
            if(!External[model.external.solver]){
                throw new Error("No support (yet) for " + model.external.solver + ". Please use one of these instead:" + solvers);
            }
            
            return External[model.external.solver].solve(model);
            

// /////////////////////////////////////////////////////////////////////
// *********************************************************************
//  END
// Try our hand at handling external solvers...
//  END
// *********************************************************************
// /////////////////////////////////////////////////////////////////////

        } else {

            if (model instanceof Model === false) {
                model = new Model(precision).loadJson(model);
            }

            var solution = model.solve();
            this.lastSolvedModel = model;
            solution.solutionSet = solution.generateSolutionSet();

            // If the user asks for a full breakdown
            // of the tableau (e.g. full === true)
            // this will return it
            if (full) {
                return solution;
            } else {
                // Otherwise; give the user the bare
                // minimum of info necessary to carry on

                var store = {};

                // 1.) Add in feasibility to store;
                store.feasible = solution.feasible;

                // 2.) Add in the objective value
                store.result = solution.evaluation;

                store.bounded = solution.bounded;
                
                if(solution._tableau.__isIntegral){
                    store.isIntegral = true;
                }

                // 3.) Load all of the variable values
                Object.keys(solution.solutionSet)
                    .forEach(function (d) {
                        //
                        // When returning data in standard format,
                        // Remove all 0's
                        //
                        if(solution.solutionSet[d] !== 0){
                            store[d] = solution.solutionSet[d];
                        }
                        
                    });

                return store;
            }

        }

    };

    /*************************************************************
     * Method: ReformatLP
     * Scope: Public:
     * Agruments: model: The model we want solver to operate on
     * Purpose: Convert a friendly JSON model into a model for a
     *          real solving library...in this case
     *          lp_solver
     **************************************************************/
    this.ReformatLP = ReformatLP;


     /*************************************************************
     * Method: MultiObjective
     * Scope: Public:
     * Agruments:
     *        model: The model we want solver to operate on
     *        detail: if false, or undefined; it will return the
     *                result of using the mid-point formula; otherwise
     *                it will return an object containing:
     *
     *                1. The results from the mid point formula
     *                2. The solution for each objective solved
     *                   in isolation (pareto)
     *                3. The min and max of each variable along
     *                   the frontier of the polytope (ranges)
     * Purpose: Solve a model with multiple objective functions.
     *          Since a potential infinite number of solutions exist
     *          this naively returns the mid-point between
     *
     * Note: The model has to be changed a little to work with this.
     *       Before an *opType* was required. No more. The objective
     *       attribute of the model is now an object instead of a
     *       string.
     *
     *  *EXAMPLE MODEL*
     *
     *   model = {
     *       optimize: {scotch: "max", soda: "max"},
     *       constraints: {fluid: {equal: 100}},
     *       variables: {
     *           scotch: {fluid: 1, scotch: 1},
     *           soda: {fluid: 1, soda: 1}
     *       }
     *   }
     *
     **************************************************************/
    this.MultiObjective = function(model){
        return Polyopt(this, model);
    };
};

export default Solver;

