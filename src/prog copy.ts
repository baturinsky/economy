{
  type Prices = { [name: string]: number };

  function max<T>(a: { [ind: string]: T }, f: (a: T, i) => number) {
    let ind: string, v = Number.MIN_VALUE;
    for (let i in a) {
      let x = f(a[i], i)
      if (x > v) {
        ind = i
        v = x
      };
    }
    return ind;
  }

  class GoodKind {
    /**part of marginal utility formula mmul*x**mpow  */
    mpow: number
    /**part of marginal utility formula mmul*x**mpow  */
    mmul: number
    /**part of good's reserver consumed per round */
    consume = 0.25

    /**
     * 
     * @param pow part of utility formula mul*x**pow 
     * @param mul part of utility formula mul*x**pow 
     */
    constructor(public pow = 0.8, public mul = 1) {
      this.mpow = pow - 1;
      this.mmul = mul * pow
    }

    marginalValue(amount: number) {
      let v = this.mmul * ((amount + 0.5) ** this.mpow)
      return v
    }
  }

  let goods = {
    "grain": new GoodKind(0.25, 5),
    "iron": new GoodKind(0.45, 1),
    "tools": new GoodKind(0.4, 2)
  }

  class Clan {
    stocks: Object
    funds = 0
    fundsmpow = 1.1
    fundsmmul = 0.1
    capita = 1

    constructor() {
      this.stocks = Object.fromEntries(Object.keys(goods).map(k => [k, 0]))
    }

    bestBuy(prices: Prices) {
      let bestGood = max(prices, (p, i) => this.marginalValue(i, prices))
      if (this.marginalValue(bestGood, prices) < (this.fundsmpow ** (-this.fundsPerCapita)) * this.fundsmmul)
        return null
      return bestGood
    }

    marginalValue(i: string, prices: Prices) {
      let good = goods[i] as GoodKind;
      return good.marginalValue(this.stocksToBeConsumedPerCapita(i)) / prices[i]
    }

    get fundsPerCapita(){
      return this.funds / this.capita;
    }

    /** Amount of the stocks to be consumed per capita next round */
    stocksToBeConsumedPerCapita(i:string){
      return this.stocks[i] * goods[i].consume / this.capita
    }

    buy(prices: Prices) {
      let bestGood = this.bestBuy(prices)
      if (bestGood != null) {
        this.funds -= prices[bestGood]
        this.stocks[bestGood]++
      }
      return bestGood
    }

    consume(){
      for(let goodName in goods){
        let good = goods[goodName];
        let consumed = good.consume * this.stocks[goodName];
        this.stocks[goodName] -= consumed;
      }
    }

  }

  let c = new Clan()
  c.funds = 100
  let prices = { grain: 2, tools: 4, iron: 2 }
  for (let i = 0; i < 30; i++) {
    let bought = c.buy(prices)
    if (!bought)
      break
    console.log(JSON.stringify(c.stocks), c.funds)
  }
}