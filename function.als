open ops

pred univalent(X,Y: set univ, R: X->Y) {
  ~R.R in id[Y]
}

pred injective(X,Y: set univ, R: X->Y) {
  univalent[Y,X,~R]
}
