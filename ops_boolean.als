sig X { R,S: set Y }

sig Y {}

run {}

-- Definition 4.1
check {
	R + S = { x: X, y: Y | x->y in R or x->y in S }
} for 10

check {
	R & S = { x: X, y: Y | x->y in R and x->y in S }
} for 10

check {
	co[X,Y,R] = { x:X, y: Y | x->y not in R }
} for 10

check {
	null[X,Y] in X->Y
} for 10

check {
	full[X,Y] in X->Y
} for 10

check {
	id[X] = { x,y:X | x in X and x = y }
} for 10

fun co(X,Y: set univ, R: X->Y) : X->Y {
	X->Y - R
}

fun null(X,Y: set univ) : X->Y {
  none->none
}

fun full(X,Y: set univ) : X->Y {
	X->Y
}

fun id(X: set univ) : X->X {
	iden:>X
}
