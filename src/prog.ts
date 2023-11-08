//import JSLPSolver from '@ellbur/javascript-lp-solver'
import JSLPSolver from './lp-solver/main'

{
  type Prices = { [name: string]: number };

  class Recipe {
    components: { [name: string]: number }
    result: { [name: string]: number }
    text: string

    constructor(text: string) {
      text = text.replace(/[ =\r\n]/g, "");
      this.text = text;
      let parts = text.split(">").map(part => {
        let o = Object.fromEntries(part.split("+").map(bit => {
          let bs = bit.split("*") as [string, number]
          bs[1] = Number(bs[1] || "1")
          return bs
        }))
        delete o[""]
        return o
      });
      [this.components, this.result] = parts
    }

    calculateProfit(prices: Prices) {
      let p = 0
      for (let n in this.components) {
        p -= (prices[n] || 1) * this.components[n]
      }
      for (let n in this.result) {
        p += (prices[n] || 1) * this.result[n]
      }
      return p
    }

  }

  function toSolverModel(recipes: Recipe[], int=false) {
    let model = { optimize: "profit", opType: "max", constraints: {}, variables: {}, ints: {}, options: { tolerance: 0.01 } };
    for (let r of recipes) {
      for (let k of Object.keys(r.components)) {
        model.constraints[k] = { min: 0 };
      }
    }
    model.constraints["round"] = { min: -1 };
    for (let r of recipes) {
      if(r.text=="")
        continue;
      let v = {}
      for (let c in r.components) {
        v[c] = -r.components[c];
      }
      for (let c in r.result) {
        v[c] = r.result[c];
      }
      model.variables[r.text] = v
      if(int)
        model.ints[r.text] = true
    }
    return model
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
tool=>profit*5;`
  IN.value = text;

  function solve() {
    let recipes = IN.value.split(";").map(s => new Recipe(s))

    //console.log(recipes)

    const solver = new JSLPSolver();

    let intModel;

    let result = [true, false].map(int=>{
      let model = toSolverModel(recipes, int);      
      intModel ??= model;

      let t0 = performance.now();
      let results = solver.Solve(model);
      let dt = performance.now() - t0
      return `${int?"integer":"float"} solution in ${dt} ms:\n\n${JSON.stringify(results, null, 2)}\n\n`
    }).join("") + `model for integer solution (float is the same without the ints block):\n${JSON.stringify(intModel, null, 2)}`

    OUT.value = result;
  }

  for(let i=0;i<5;i++)
    solve();

  IN.addEventListener("input", ()=>{
    solve()
  })
  
}