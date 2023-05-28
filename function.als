open ops

pred univalent(X,Y: set univ, R: X->Y) {
  ~R.R in id[Y]
}

pred injective(X,Y: set univ, R: X->Y) {
  univalent[Y,X,~R]
}

pred matching(X,Y: set univ, R: X->Y) {
  univalent[Y,X,R]
  injective[Y,X,R]
}

pred total(X,Y: set univ, R: X->Y) {
  full[X,Y] in R.(full[Y,Y])
}

pred surjective(X,Y: set univ, R: X->Y) {
  total[Y,X,~R]
}

pred mapping(X,Y: set univ, R: X->Y) {
  total[X,Y,R]
  univalent[X,Y,R]
}

pred bijective(X,Y: set univ, R: X->Y) {
  surjective[X,Y,R]
  injective[X,Y,R]
}

pred row_constant(V,W: set univ, R: V->W) {
  R = R.(full[W,W])
}

pred vector(V,W: set univ, R: V->W) {
  row_constant[V,W,R]
}

pred point(V,W: set univ, R: V->W) {
  vector[V,W,R]
  injective[V,W,R]
  surjective[V,W,R]
}

-- Multivalency
pred multivalent(V,W: set univ, R: V->W) {
  R in R.(di[W])
}
