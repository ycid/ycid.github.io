-- Function that computes mixed Segre classes
-- INPUT: A list of homogeneous ideals defining closed subschemes Z_1,...,Z_m in a projective space PP^n
-- OUTPUT: The mixed Segre class Z_1,...,Z_m pushed forward to the projective space PP^n
mixedSegre = L -> (
    R := ring(L_0);
    m := length L;
    L = join({ideal vars R}, apply(L, I -> ideal super basis(max flatten degrees I, I)));
    rr := apply(m+1, i -> numgens(L_i));
    ee := i -> join(toList((i-1):0), {1}, toList((m+1-i):0));
    ww := symbol ww, tt := symbol tt;
    wVars := flatten apply(m+1, i -> apply(numgens(L_i), j -> ww_(i,j)));
    wDegs := flatten apply(m+1, i -> apply(numgens(L_i), j -> ee(i+1)));
    W := (coefficientRing R)(monoid[wVars, Degrees => wDegs]);
    S := R[tt_1..tt_m];
    phi := map(S, W, join(flatten entries gens L_0, flatten apply(m, i -> flatten entries gens (tt_(i+1)*L_(i+1)))));
    Graph := ker phi;
    Covol := multidegree Graph;
    Covol = sub(Covol, (ring Covol)_0 => 1);
    Q := product(apply(m, i -> ((ring Covol)_(i+1))^(rr_(i+1)-1)));
    C := coefficients Covol;
    Vol := (matrix{apply(flatten entries C_0, v -> Q//v)} * C_1)_(0,0);
    H := symbol H, t := symbol t;
    A := ZZ(monoid[H,t_1..t_m]);
    A = A / ideal((A_0)^(rr_0));
    geom := apply(m, i -> sum apply(rr_(0), j -> ((-1)^j*(max flatten degrees(L_(i+1)))*A_0*A_(i+1))^j));
    F := map(A, ring Vol, join({1_A}, apply(m, i-> A_0*A_(i+1)*geom_i)));
    result := 1 - ((product geom) * F(Vol));
    result
)


--- Example 1 --- 
R = QQ[x_0..x_4]
I1 = ideal(x_0^2)
I2 = ideal(x_1^2, x_2^3)
mixedSegre {I1, I2}

--- Example 2 --- 
R = QQ[x_0..x_4]
I1 = ideal(x_0^2)
I2 = ideal(x_0^2, x_2^3)
mixedSegre {I1, I2}

--- Example 3 --- 
R = QQ[x_0..x_5]
I1 = ideal(x_0^2, x_1^2)
I2 = ideal(x_2^2, x_3^3)
mixedSegre {I1, I2}

--- Example 4 --- 
R = QQ[x_0..x_5]
I1 = ideal(x_0^2, x_1^2)
I2 = ideal(x_2^2, x_3^3, x_4^3)
mixedSegre {I1, I2}

--- Example 5 --- 
R = QQ[x_0..x_5]
I1 = ideal(x_0^2, x_1^2)
I2 = ideal(x_2^2, x_3^3, x_4^3+x_5^3)
mixedSegre {I1, I2}

--- Example 6 --- 
R = QQ[x_0..x_5]
I1 = ideal(x_0^2, x_1^2)
I2 = ideal(x_1^2, x_2^3, x_3^3, x_4^3)
mixedSegre {I1, I2}

--- Example 7 --- 
R = QQ[x_0..x_7]
I1 = ideal(x_0^2, x_1^2, x_2^3)
I2 = ideal(x_3^2, x_4^3, x_5^3)
mixedSegre {I1, I2}

--- Example 8 --- 
R = QQ[x_0..x_4]
I1 = ideal(x_0^2, x_1^2)
I2 = ideal(x_2^3, x_4^3)
mixedSegre {I1, I2}

--- Example 9 --- 
R = QQ[x_0..x_4]
I1 = ideal(x_0^2, x_1^2)
I2 = ideal(x_0^3, x_1^3)
mixedSegre {I1, I2}


--- Example 10 ---
R = QQ[x_0..x_5]
I1 = ideal(x_0, x_1^3)
I2 = ideal(x_2^2, x_3^3, x_4^4)
mixedSegre {I1, I2}


--- Example 11 ---
R = QQ[x_0..x_5]
I1 = ideal(x_0^2, x_1^3)
I2 = ideal(x_2^2, x_3^3, x_4^4)
mixedSegre {I1, I2}


--- Example 12 ---
R = QQ[x_0..x_5]
I1 = ideal(x_0^2, x_1^3, x_2^3)
I2 = ideal(x_3^2, x_4^3, x_5^4)
mixedSegre {I1, I2}
