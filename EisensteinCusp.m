/*

This program is run by entering `magma magma_eisenstein' at the command line. It is a companion to the paper `Cusps and volumes of Picard modular surfaces'.

Using a presentation for the Picard modular group for the Eisenstein integers, it computes all the torsion-free subgroups of index 72 which are contained in an index four subgroup. One can add further divisors of 72 to the list `divisors' below to search for other index 72 subgroups. One of these index two subgroups is the intersection of the maximal lattice with its sister, and this is the one which contains all the torsion-free subgroups. One can check this via homomorphisms to finite groups, or that one lattice contains the word `r' and the other does not. Some of the lattices are only conjugate in the sister lattice, and these repetitions are eliminated by finding an explicit isomorphism between the lattices via presentations. The list `torsion_free' contains all the lattices.

The procedure at the end explores normal cores and the image of the peripheral subgroup of the Picard Eisenstein lattice in the quotient group to determine the number of cusps for each torsion-free lattice of index 72. This allows one to count cusps combinatorially.

*/

G<j, r1> := Group<j, r1 | j^3, r1^6, (j*r1^-1*j)^4, (r1, (j*r1^-1*j)^2)>;;

f := j*r1^-1*j;;

r := f^2;;

p := r^-1*j;;

q := r1*p;;

t := q*r1^3*r*p*q*r1^-3*q^-1;;

s := q^-1*p;;

torsion := [* j, r1, r1^2, r1^3, f, r, t, t^2, t^3, (t*r), (t*r)^2, (t*r)^3, (t*r)^4, (t*r)^6, s*t, s^2*t, s^3*t, s^4*t, s^5*t, s*t^2, s^2*t^2, s^2*t^3, s^2*t^4, s^2*t^5, s^3*t, s^3*t^2, s^3*t^3, s^3*t^4, s^3*t^5, r1*r, r1^2*r, r1^3*r *];;

divisors := [* 4 *];;

torsion_free := [* *];;

already_found := false;;

for d in divisors do

   Gindexd := LowIndexSubgroups(G, <d, d>);;

   for h in Gindexd do

      H := Rewrite(G, h);;

      e := 72 div d;;

      Hsubgroups := LowIndexSubgroups(H, <e, e>);;

      for m in Hsubgroups do

         M := Rewrite(G, m);;

         cosets := RightTransversal(G, M);;

         for c in cosets do

            for g in torsion do

               if c*g*c^-1 in M then

                  torsion_exists := true;;

                  break c;;

               else

                  torsion_exists := false;;

               end if;;

            end for;;

         end for;;

         if torsion_exists eq false then

            already_found := false;;

            for N in torsion_free do

               if IsConjugate(G, M, N) eq true or SearchForIsomorphism(M, N, 9) eq true then

                  already_found := true;;

                  break N;;

               else

                  alread_found := false;;

               end if;;

            end for;;

            if already_found eq false then

               Append(~torsion_free, Rewrite(G, M));;

            end if;;

         end if;;

      end for;;

   end for;;

end for;;

nil_manifolds := [* *];;

for M in torsion_free do

   core := Rewrite(G, Core(G, M));;

   F := G / core;;

   Ghom := hom<G -> F | j -> F.1, r1 -> F.2>;;

   FM := Rewrite(F, M@Ghom);;

   FMcosets := RightTransversal(F, FM);;

   fp := p@Ghom;;

   fq := q@Ghom;;

   FB := Rewrite(F, sub<F | fp, fq>);;

   Mnil := [* *];;

   nil_indices := [* *];;

   for c in FMcosets do

      FMBc := Rewrite(FM, FM meet FB^c);;

      Append(~nil_indices, Index(FM, FMBc));;

      Append(~Mnil, FMBc);;

   end for;;

   Append(~nil_manifolds, [* Mnil, nil_indices, Index(F, FB) *]);;

end for;;
