/*global module*/
/*global require*/
import Solution from "./Solution.js";

function MilpSolution(tableau, evaluation, feasible, bounded, branchAndCutIterations) {
    Solution.call(this, tableau, evaluation, feasible, bounded);
    this.iter = branchAndCutIterations;
}
export default MilpSolution;
MilpSolution.prototype = Object.create(Solution.prototype);
MilpSolution.constructor = MilpSolution;
