open ops

-- Reflexivity
pred reflexive(V: set univ, R: V->V) {
  all x:V | x->x in R
}

pred irreflexive(V: set univ, R: V->V) {
  all x:V | x->x not in R
}

-- Connexity
pred semi_connex(V: set univ, R: V->V) {
  all x,y:V {
    { x != y
    } implies {
      x->y in R or y->x in R
    }
  }
}

pred connex(V: set univ, R: V->V) {
  all x,y: V {
    x->y not in R
    implies
    y->x in R
  }
}
