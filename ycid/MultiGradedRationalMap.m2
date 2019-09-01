newPackage(
    "MultiGradedRationalMap",
    Headline => "Degree and birationality of multi-graded rational maps",
    Authors => {{ Name => "Yairon Cid Ruiz", 
		  Email => "ycid@ub.edu", 
		  HomePage => "http://www.ub.edu/arcades/ycid.html"}},
    Version => "0.001",
    Date => "2018",
    DebuggingMode => false,
    Configuration => {},
    Reload => true
)

export { 
    "degreeOfMap", 
    "jDRank", 
    "isBiratMap", 
    "satSpecialFiberIdeal",
    "satSpecialFiber",
    "gensSatSpecialFib",
    "upperBoundDegreeSingleGraded",
    "Hm1Rees0",
    "partialJDRs" 
}



--------------------
--------------------
---------- M2 code
--------------------
--------------------


------------------------------------------------------------------------------------------------------------------
------------------------------------------------------------------------------------------------------------------
    	    	   -- SOME TECHNICAL/AUXILIARY FUNCTIONS 
------------------------------------------------------------------------------------------------------------------
------------------------------------------------------------------------------------------------------------------


-- Computes the Rees algebra with emphasis on the R-grading.
-- It simply calls the package ``ReesAlgebras'' on Macaulay2.
RgradRees := (I) -> ( 
    R := ring I;
    n := numgens R;
    lvars := flatten entries vars R;   
    ReesEq := reesIdeal I;
    e := numgens ring ReesEq;
    K := coefficientRing R;
    Z := symbol Z;
    xxx := symbol xxx;
    AA := K[Z_1 .. Z_e][xxx_1 .. xxx_n, Degrees => degrees R]; --bigraded ring
    AA' := ring ReesEq;
    F := map(AA, AA', {Z_1 .. Z_e, xxx_1 .. xxx_n});
    F(ReesEq) 
)


-- This function tries to recover the multi-projective space encoded by R.
-- If R is not a multi-graded polynomial ring with weight 1 on each variable,
-- then it returns false.
getGrading := (R) -> (
    L := degrees R;    	    
    m := length L_0;
    D := new MutableList from toList(m:0);
    for i from 0 to length L - 1 do (
    	j := 0, s := 0;
	for k from 0 to m-1 do (
	    if L_i_k != 0 and L_i_k != 1 then return (, false);
	    s = s + L_i_k;
	    if L_i_k == 1 then j = k;
	);	
    	if s != 1 then return (, false);
	D#j = D#j + 1;
    );
    (toList D, true)
)


-- Checks if an ideal is homogeneous and equally generated
isEquallyGenerated := (I) -> (
    if not isHomogeneous I then return false;
    L := flatten entries gens I;
    f0 := L_0;
    all(L, f -> (degree f) == (degree f0))         
)


-- Makes some sannity checks in the multi-graded case
checkMultiGraded := (I) -> (
    if not isEquallyGenerated I 
       then error "The ideal needs to be homogeneous and equally generated.";
    R := ring I;
    grading := getGrading R;
    if not isPolynomialRing R or not grading_1 
       then error "The ring of the ideal needs to be a polynomial ring with standard multi-grading.";
       
    grading_0 
)


-- Makes some sannity checks in the single-graded case
checkSingleGraded := (I) -> (
    if not isEquallyGenerated I 
       then error "The ideal needs to be homogeneous and equally generated.";
    R := ring I;
    grading := getGrading R;
    if not isPolynomialRing R or not grading_1 or length grading_0 != 1 
       then error "The ring of the ideal needs to be a stantard single-graded polynomial ring.";
)


-- Emulates the action of the elements of R over H_m^n(R),
-- where m is the maximal irrelevant ideal of R
prod := (X, Lmono) -> (
    M := mutableMatrix(ring X, 1, numcols Lmono);
    for i from 0 to (numcols Lmono)-1 do M_(0,i) = X // Lmono_(0,i);
    matrix M       
)


-- Computes the multi-homogeneous irrelevant ideal of R
getIrrelevantIdeal := (R) ->(
    grading := getGrading R;
    m := length grading_0;
    NN := ideal(1_R);
    for i from 1 to m do (
    	deg := toList((i-1):0) | {1} | toList((m-i):0);
	NN = NN * ideal image super basis(deg, R); 
    );    
    NN
)

------------------------------------------------------------------------------------------------------------------
------------------------------------------------------------------------------------------------------------------
 
 
 
 
 
------------------------------------------------------------------------------------------------------------------
------------------------------------------------------------------------------------------------------------------
    	    	   -- FUNCTIONS RELATED TO THE SATURATED SPECIAL FIBER RING   
------------------------------------------------------------------------------------------------------------------
------------------------------------------------------------------------------------------------------------------


-- Given a map g: F --> G of free AA-modules, it gives the degree zero part in 
-- R-grading of the induced map in top local cohomology.
-- INPUT: F free AA-module of the source
-- INPUT: G free AA-module of the image
-- INPUT: the map g is represented by the matrix A
-- OUTPUT: the matrix M representing the degree zero part the R-grading of
--            the induced map $H_m^n(g): H_m^n(F) --> H_m^n(G)$
getMapInLocalCohom := (F, G, A) -> ( 
      AA := ring F;
      n := numgens AA;
           
      -- get the size of the matrix M
      colsM := 0;
      rowsM := 0;
      lMonoCols := ();
      lMonoRows  := (); 
      
      -- compute the form of the columns
      for i from 0 to (rank F)-1 do (
      	  di := (degree F_i)_0;
    	  lMonoCols = append(lMonoCols, 
	               flatten entries super basis(di-n, AA));
    	  colsM = colsM + length lMonoCols_i;        
      );
            
      -- compute the form of the rows
      for i from 0 to (rank G)-1 do (
      	  di := (degree G_i)_0;
    	  lMonoRows = append(lMonoRows, 
	               flatten entries super basis({di-n, 0}, AA));
      	  rowsM = rowsM + length lMonoRows_i;
      );
    
      -- the matrix representing the map in local cohomology     
      M := mutableMatrix(AA, rowsM, colsM);
      
      -- process of constructing the matrix M
      counterCols := 0;
      for j from 0 to (rank F)-1 do (
	  counterRows := 0;
	  for i from 0 to (rank G)-1 do ( 
	      a := A_(i,j);
	      if a != 0 and lMonoCols_j != {} and lMonoRows_i != {} then (
    	      	  (Ma, Ca) := coefficients a;
		  for l from 0 to (length lMonoCols_j)-1 do (
		      X := lMonoCols_j_l;		      
		      newMa := prod(X, Ma);
		      Y := newMa * Ca;
		      (Mres, Cres) := coefficients(Y, Monomials => lMonoRows_i);  
		      for k from 0 to (length lMonoRows_i)-1 do 
		          M_(counterRows + k, counterCols + l) = Cres_(k, 0); 
		  );	                    	      
	      );
	      counterRows = counterRows + length lMonoRows_i;
	  );
    	  counterCols = counterCols + length lMonoCols_j;     	    	  
       ); 
       
       matrix M
)


-- Computes the module $[H_m^1(Rees(I))]_0$ in Corollary 2.12     
--INPUT: the defining equations of Rees(I)
localHm1Rees0 := (ReesEq) -> (
    AA := ring ReesEq;
    n := numgens AA;
    e := numgens coefficientRing AA;  
    K := coefficientRing coefficientRing AA;
    Z := symbol Z;
    kkZ := K[Z_1 .. Z_e];
        
    -- It is computed by means of the spectral sequences coming from the double complex
    -- obtained by the tensor product of a resolution of ReesEq and the Cech complex.
    -- (check Proposition 2.7(i) for more details)	
    rs := res ReesEq;
    mapAAtokkZ := map(kkZ, AA, join(toList(n:0), {Z_1 .. Z_e}));
    M1 := mapAAtokkZ(getMapInLocalCohom(rs_(n-1), rs_(n-2), rs.dd_(n-1)));
    M2 := mapAAtokkZ(getMapInLocalCohom(rs_n, rs_(n-1), rs.dd_(n)));
   
    (ker M1) / (image M2)        
)



-- It simply calls localHm1Rees0 after a sannity check.
-- INPUT: A homogeneous ideal I.
-- OUTPUT: it computes the module  $[H_m^1(Rees(I))]_0$.
-- CAVEAT: For the momment, it only supports single-graded ideals on a polynomial ring.
Hm1Rees0 = method()
Hm1Rees0(Ideal) := (I) -> (
    checkSingleGraded(I);
        	    
    localHm1Rees0 RgradRees I 
)


-- By considering the powers {I^1, I^2, ..., I^nsteps} of I, it computes a set of generators of the saturated special fiber ring.
-- The algorithm is correct only if nsteps is big enough to obtain all the generators.
-- INPUT: A multi-homogeneous ideal.
-- INPUT: The number of steps.
-- OUTPUT: Computes the possible generators of the saturated special fiber ring in the graded parts  
--          given by [(I^1)^sat]_d, [(I^2)^sat]_2d, ..., [(I^nsteps)^sat]_nsteps*d.
gensSatSpecialFib = method()
gensSatSpecialFib(Ideal, ZZ) := (I, nsteps) -> (    
    checkMultiGraded(I);
    d := degree (gens I)_(0,0);
    NN := getIrrelevantIdeal ring I;
    satIpow := saturate(I, NN);
    tot := flatten entries super basis(d, satIpow);
    L := { ideal tot };
    	
    for i from 2 to nsteps do (
        satIpow = saturate(I * satIpow, NN);
   	curr := ideal image super basis(i*d, satIpow);
	   
	-- delete those that can be also obtained by multiplication of lower graded parts
	toDel := ideal();
	for j from 1 to i - 1 do toDel = toDel + (L_(j-1) * L_(i-j-1));
	toAdd := flatten entries mingens (curr / toDel);
	   	     
        tot = join(tot, toAdd);
        L = append(L, curr);
    );

    tot
)


-- Tries to compute the defining ideal of the saturated special fiber ring.
-- INPUT: A multi-homogeneous ideal.
-- INPUT: nsteps is the number of steps used in the process of obtaining a set of generators.
-- OUTPUT: returns the ideal defining the saturated special fiber ring.
-- CAVEAT: It only gives a correct answer if nsteps is bigger than the highest degree of the generators of the 
--       saturated special fiber ring.
satSpecialFiberIdeal = method()
satSpecialFiberIdeal(Ideal, ZZ) := (I, nsteps) -> (
    checkMultiGraded(I);
    R := ring I;
    d := degree (gens I)_(0,0);
    
    lGens := gensSatSpecialFib(I, nsteps);
    lDegs := apply(lGens, G -> (degree G)_0 // d_0);
          	   
    K := coefficientRing R;	    	
    Z := symbol Z;		
    B := K[Z_1 .. Z_(length lGens), Degrees => lDegs]; 
    F := map(R, B, lGens);
      
    ker F
)


-- It simply calls the method satSpecialFiberIdeal
-- INPUT: A multi-homogeneous ideal.
-- INPUT: nsteps is the number of steps used in the process of obtaining a set of generators.
-- OUTPUT: returns the saturated special fiber ring.
-- CAVEAT: It only gives a correct answer if nsteps is bigger than the highest degree of the generators of the 
--       saturated special fiber ring.
satSpecialFiber = method()
satSpecialFiber(Ideal, ZZ) := (I, nsteps) -> (
    checkMultiGraded(I);
    satFibEq := satSpecialFiberIdeal(I, nsteps);
    (ring satFibEq) / satFibEq
)


------------------------------------------------------------------------------------------------------------------
------------------------------------------------------------------------------------------------------------------
 
 
 
 
 
------------------------------------------------------------------------------------------------------------------
------------------------------------------------------------------------------------------------------------------
    	    	   -- FUNCTIONS RELATED TO THE DEGREE AND BIRATIONALITY OF RATIONAL MAPS
------------------------------------------------------------------------------------------------------------------
------------------------------------------------------------------------------------------------------------------


degreeOfMap = method()

-- Computes the degree of the rational represented by the generators of the ideal I.
-- It contains a computational implementation of Corollary 2.12.
-- CAVEAT: For the momment, it only supports porjective spaces.
-- INPUT: An ideal representing a rational map.
-- OUTPUT: Returns the degree of the rational map.
--         If the map is not generically finite then the output is 0.
degreeOfMap(Ideal) := (I) -> (
    checkSingleGraded(I);
    R := ring I;
    ReesEq := RgradRees(I); -- equations of Rees(I)
    AA := ring ReesEq;
            
    -- computes degree of the image of phi
    mm := ideal vars AA; 
    S := AA / (mm + ReesEq); 
    degIm := degree S;
    
    -- if the map is not genericaly finite, then return 0   
    if dim S < dim R then return 0;
        
    -- computes multiplicity of $[H_m^1(Rees(I))]_0$ in Corollary 2.12     
    L := localHm1Rees0(ReesEq);    
    if dim L < dim S then return 1;
    mult := degree L;     
            
    -- the degree of phi      
    1 + mult//degIm    
)



-- This map compute the degree of rational map by computing the multiplicity of the saturated special fiber ring (see Theorem 2.4).
-- It also works in the multi-homogeneous setting. 
-- INPUT: A multi-homogeneous ideal. 
-- INPUT: The number of steps for computing the saturated special fiber ring.
-- OUTPUT: The degree of the rational map.
-- CAVEAT: It only gives a correct answer if nsteps is bigger than the highest degree of the generators of the 
--       saturated special fiber ring.
degreeOfMap(Ideal, ZZ) := (I, nsteps) -> (
    checkMultiGraded(I);
    satFib := satSpecialFiber(I, nsteps);
    N := numerator reduceHilbert hilbertSeries satFib;
    mult := sub(N, { (vars ring N)_(0,0) => 1 });
    degIm := degree specialFiber I;
    
    mult // degIm
)



-- It computes the partial Jacobian dual ranks.
-- INPUT: A multi-homogeneous ideal. 
-- OUTPUT: The partial Jacobian dual ranks.
partialJDRs = method()
partialJDRs(Ideal) := (I) -> (
    grading := checkMultiGraded(I);
    R := ring I;
    m := length grading;
    ReesEq := RgradRees(I);
    AA := ring ReesEq;
    gensRees := flatten entries gens ReesEq;
   
    -- coordinate ring of the image   
    mm := ideal vars AA;
    S := AA / (mm + ReesEq);
        
    JDRs := { };	

    -- compute the JDRs	 
    for i from 1 to m do (
    	deg := toList((i-1):0) | {1} | toList((m-i):0);
        L := select(gensRees, f -> apply(m, j -> (degree f)_j) == deg);
     	if L == {} then JDRs = append(JDRs, 0) 
	else (
	    M := jacobian matrix{L};
	    JDRs = append(JDRs, rank(M ** S));     
     	);    
    );

    JDRs
)


-- Computes the full Jacobian dual rank of a rational map (this is defined in Notation 4.2)
-- INPUT: an ideal representing the rational map. 
-- OUTPUT: the full Jacobian dual rank. 
-- CAVEAT: For the momment, it only supports multi-projective spaces in the source.
jDRank = method()
jDRank(Ideal) := (I) -> (
    checkMultiGraded(I);
    ReesEq := RgradRees(I); -- equations of Rees(I)
    AA := ring ReesEq;
    m := length (getGrading ring I)_0;
        
    -- computes the total Jacobian dual matrix
    L := select(flatten entries gens ReesEq, f -> sum(m, j -> (degree f)_j) == 1);
    if L == {} then return 0;
    M := jacobian matrix{L};    
 
    --coordinate ring of the image
    mm := ideal vars AA;
    S := AA / (mm + ReesEq);
  
    -- computes the total Jacobian dual rank  
    rank (M ** S)	   
)   



-- Given a multigraded rational map phi, it determines the birationality of phi
-- INPUT: an ideal representing the rational map phi
-- OUTPUT: true/false if the rational map is birational/non-birational onto its image
-- CAVEAT: For the momment, it only supports multi-projective spaces in the source
-- REMARK: From Theorem 4.4 we can simply compute the rank of the "full" Jacobian dual matrix.
--         Therefore, we only need to check the rank of one matrix and it allows us to treat 
--         the muli-graded case similarly to the single-graded.
isBiratMap = method()
isBiratMap(Ideal) := (I) -> (    
    grading := checkMultiGraded(I);
    
    r := (sum grading) - (length grading);
    JDR := jDRank I;
            
    (JDR == r)
)


-- This function computes the upper bound given in Theorem 3.22 for a single graded rational map.
-- INPUT: A homogeneous ideal defining a rational map.
-- OUTPUT: An upper bound which can be computed with some Hilbert function computations.
upperBoundDegreeSingleGraded = method()
upperBoundDegreeSingleGraded(Ideal) := (I) -> (
    checkSingleGraded(I);
    if dim I > 1 then 
           error "The base locus should have dimension zero.";
    d := (degree I_0)_0;
    n := numgens ring I;
    J := saturate(I);
    B := 1 + binomial(d-1,n-1) + hilbertFunction(d,I) - hilbertFunction(d,J);
    for i from 2 to n-2 do B = B + hilbertFunction((n-i)*d-n,I);
    
    B
) 


------------------------------------------------------------------------------------------------------------------
------------------------------------------------------------------------------------------------------------------



--------------------
--------------------
---------- Documentation
--------------------
--------------------


beginDocumentation()

doc /// 
  Key
   "MultiGradedRationalMaps"
  Headline
     A package for computing the degree and checking the birationality of a multi-graded rational map.
  Description
   Text
    MultiGradedRationalMap provides functions for computing the degree and checking the birationality of a multi-graded rational map.
    
    {\bf ACKNOWLEDGEMENTS}:
    The author is very grateful to Laurent Busé for his constant support on the preparation of this package.    
  
  Caveat
    Under developpement.
 ///
 
 doc ///
  Key
   degreeOfMap
   (degreeOfMap,Ideal)
  Headline
   Computation of the degree
  Usage
   degreeOfMap(I)
  Inputs
    I:Ideal
    	an ideal defining the map
  Outputs
    :ZZ
    	an integer, the degree 
  Description
   Text
    Here we show an example.
   Example
    {"R = QQ[x,y,z]",
     "I = ideal(random(4, R), random(4, R))",
     "degreeOfMap I"} 
///


end--