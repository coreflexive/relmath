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


-- Symmetry
pred symmetric(V: set univ, R: V->V) {
  all x,y:V {
    x->y in R
    implies
    y->x in R
  }
}

pred asymmetric(V: set univ, R: V->V) {
  all x,y:V {
    x->y in R
		implies
    y->x not in R
  }
}

pred antisymmetric(V: set univ, R: V->V) {
  all x,y:V {
    x != y
    implies {
      x->y not in R or y->x not in R
    }
  }
}

fun AsymPt(V: set univ, R: V->V) : V->V {
  R & dual[V,V,R]
}

fun SymPt(V: set univ, R: V->V) : V->V {
  R & ~R
}

pred tournament(V: set univ, R: V->V) {
  asymmetric[V,R]
  semi_connex[V,R]
}
