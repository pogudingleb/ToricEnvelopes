with(combinat):
with(LinearAlgebra):

with(Algebraic); 
a := RootOf(x^4 + x^3 + x^2 + x + 1, x, index = 1); 
b := RootOf(x^2 - 5, x); 
alpha := RootOf(x^4 - 2 * x^2 + 9, x, index = 1);
imag := RootOf(x^2 + 1, x, index = 1);
c := RootOf(x^2 - 2, x, index = 1);

# List of groups with generators
# Generators are taken from G. Miller, H. Blichfeldt, and D. L.E., Theory and applications of finite groups 
groups := table([
  binary_tetrahedron = table([
    gens = [
      Matrix(2, 2, [[imag, 0], [0, -imag]]),
      Matrix(2, 2, [[0, 1], [-1, 0]]),
      1/2 * Matrix(2, 2, [[1 + imag, -1 + imag], [1 + imag, 1 - imag]])
    ],
    # 9 is a square root of -1 mod 41
    gens_char = [
      Matrix(2, 2, [[9, 0], [0, -9]]),
      Matrix(2, 2, [[0, 1], [-1, 0]]),
      1/2 * Matrix(2, 2, [[1 + 9, -1 + 9], [1 + 9, 1 - 9]])
    ],
    size = 24,
    modulus = 41
  ]), 
  binary_icosahedron = table([
    gens = [
      Matrix(2, 2, [[a^3, 0], [0, a^2]]), 
      Matrix(2, 2, [[0, 1], [-1, 0]]), 
      1/b * Matrix(2, 2, [[a^4 - a, -a^3 + a^2], [-a^3 + a^2, -a^4 + a]])
    ],
    # 83816 is a 5th primitive root of unity mod 102001
    # 24747 is a square root of 5 mod 102001
    gens_char = [
      Matrix(2, 2, [[83816^3, 0], [0, 83816^2]]), 
      Matrix(2, 2, [[0, 1], [-1, 0]]), 
      1/24747 * Matrix(2, 2, [[83816^4 - 83816, -83816^3 + 83816^2], [-83816^3 + 83816^2, -83816^4 + 83816]])
    ],
    size = 120,
    modulus = 102001
  ]),
  binary_octahedron = table([
    gens = [
      1 / c * Matrix(2, 2, [[1 + imag, 0], [0, 1 - imag]]),
      Matrix(2, 2, [[0, 1], [-1, 0]]),
      1 / 2 * Matrix(2, 2, [[1 + imag, -1 + imag], [1 + imag, 1 - imag]])
    ],
    # 67719 is a square root of 2 mod 102001
    # 24989 is a square root of -1 mod 102001 
    gens_char = [
      1 / 67719 * Matrix(2, 2, [[1 + 24989, 0], [0, 1 - 24989]]),
      Matrix(2, 2, [[0, 1], [-1, 0]]),
      1 / 2 * Matrix(2, 2, [[1 + 24989, -1 + 24989], [1 + 24989, 1 - 24989]])
    ],
    size = 48,
    modulus = 102001
  ])
]);


GenerateGroup := proc (gens, size, char := 0) 
  local to_add, G, g, h, T, t, gens_count, n;
  description "generate group G of given size from set of generators"; 
  n := LinearAlgebra[RowDimension](gens[1]);
  G := [LinearAlgebra[IdentityMatrix](n, n)];
  gens_count := 1;
  while nops(G) < size do 
    T := cartprod([G, gens]); 
    while not T[finished] do 
      t := T[nextvalue](); 
      g := evala(t[1].t[2]);
      to_add := true; 
      for h in G do
        if 
        (char = 0 and LinearAlgebra[Equal](evala(g - h), Matrix(n)))
        or
        (char > 0 and LinearAlgebra[Equal](g - h mod char, Matrix(n)))
        then 
          to_add := false;
        end if;
      end do; 
      if to_add then 
        G := [op(G), g] 
      end if;
    end do;
    gens_count := gens_count + 1; 
  end do; 
  G; 
end proc; 

DegreeBoundChar := proc(group_data)
  local G, G_vectors, J, n, i, j, G_mod, G_vectors_mod, J_mod, J_elim_mod, vanishing_ideal_mod, char,
  vars, v_sub, max_deg, result, d;

  n := LinearAlgebra[RowDimension](group_data[gens][1]);
  vars := [];
  for i from 1 to n do
    for j from 1 to n do
      vars := [op(vars), cat(x, i, j)];
    end do:
  end do;

  # Generating group and finding vanishin ideal modulo suitable prime number
  char := group_data[modulus];
  G_mod := GenerateGroup(group_data[gens_char], group_data[size], char);
  G_vectors_mod := map(m -> convert(m, list), G_mod);
  vanishing_ideal_mod := PolynomialIdeals[VanishingIdeal](G_vectors_mod, vars, char):
  J_mod := Groebner[Homogenize]( vanishing_ideal_mod, h );
  J_elim_mod := PolynomialIdeals[EliminationIdeal](J_mod, {op(vars)});
 
  # Rational reconstruction + checking the result
  J_elim := PolynomialIdeals[PolynomialIdeal]( 
    map(p -> iratrecon(p, char), 
    PolynomialIdeals[Generators](J_elim_mod)) 
  );
  G := GenerateGroup(group_data[gens], group_data[size]);
  G_vectors := map(m -> convert(m, list), G);
  for v in G_vectors do
    v_sub := zip((x, val) -> x = val, vars, v);
    for p in PolynomialIdeals[Generators](J_elim) do
      if evala(subs(v_sub, p)) <> 0 then
        print("PANIK: polynomial ", p, "is not zero at ", v);
      end if;
    end do;
  end do;
  if Groebner[HilbertPolynomial](J_elim) <> group_data[size] / n then
    print("PANIK: Hilbert polynomial is ", Groebner[HilbertPolynomial](J_elim));
  end if;
  
  # Finding the minimum degree
  max_deg := max( map( p -> degree(p, vars), PolynomialIdeals[Generators](J_elim)) );
  result := max_deg;
  for d from 0 to max_deg do
    polys := select( p -> evalb(degree(p, vars) < max_deg - d), PolynomialIdeals[Generators](J_elim) );
    if PolynomialIdeals[IdealContainment](
      J_elim,
      PolynomialIdeals[Radical](PolynomialIdeals[PolynomialIdeal](polys))
    ) then
      result := max_deg - d - 1;
    end if:
  end do;
  result;
end proc;

print("Degree bound for binary tetrahedron group is ", DegreeBoundChar(groups[binary_tetrahedron]));
print("Degree bound for binary octahedron group is ", DegreeBoundChar(groups[binary_octahedron]));
print("Degree bound for binary icosahedron group is ", DegreeBoundChar(groups[binary_icosahedron]));
