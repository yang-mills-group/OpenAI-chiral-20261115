import YM.CF.Font.Moss
set_option autoImplicit false
noncomputable section
namespace YM.CF.Nacre
open Function Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch Fock NormedSpace Lat Rush Cube Scroll SU Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant Font
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {G:Gauge}{m:ℕ}{n:Side}
-- Actual path columns
def boot (x:Site n)(p:Wind n): Walk:= match p with
 | Sum.inl i=>shiftH x i.1 ++ square i.2.val.1 i.2.val.2 ++ reverse (shiftH x i.1)
 | Sum.inr i=> Font.swirl n i
lemma booth(x:Site n)(p:Wind n):stop x (boot x p)=x:=by
 cases p with
 | inr a=>exact swirl_stop ..
 | inl i=> have hp:=reverse_stop (shiftH x i.1) x; rw [stopH] at hp; simpa only [boot,stop_append,stopH,square_stop] using hp
lemma leanB(x:Site n)(p:Wind n):(boot x p).length≤ 8* (dial x p + 1) :=by cases p with
 | inr i=>simp [boot,swirl,dial]; omega
 | inl i=> have he:=short x i.1; simp only [boot,dial,List.length_append,reverse,List.length_map,List.length_reverse]; change _+4+(shiftH x i.1).length≤_; omega
def silt(x:Site n)(p:Wind n)(U:Config G n):G.Color:=G.curvature (travel U x (boot x p))
lemma fragile(x:Site n)(p:Wind n)(A:fieldDir G n 1):HasDerivAt (fun t:ℝ=> silt x p (represent (t • A))) (heat x (collect G A) p) 0:=by
 have he:= Work.F03.curvature_of_hasDerivAt (Push.travell (boot x p) x A); unfold silt; convert! he using 1
 cases p with
 | inr a=> rfl
 | inl i=>
    rw [boot,amix,amix,stop_append,stopH,square_stop]; have he:= aturn x (collect G A) (shiftH x i.fst); rw [stopH] at he; change _= _+heat x (collect G A) (Sum.inl i)+_; rw [he]; abel
lemma silt_g (x:Site n)(p:Wind n)(U:Config G n)(z:Site n→G.El):silt x p (Lattice.gauge z U)=G.adjoint (z x) (silt x p U):=by simp only [silt,travel_gauge,booth,G.curvature_conjugate]
@[simp] lemma silt_0(x: Site n)(p:Wind n):silt x p (1:Config G n)=0:=by
 have hp(w:Walk)(x:Site n):travel (1:Config G n) x w=1:=by induction w generalizing x<;>simp_all [travel,Step.read]
 rw [silt,hp,G.curvature_unit]
lemma pulled_l(x:Site n)(p:Wind n)(A: fieldDir G n 1):Tendsto (fun t:ℝ=> t⁻¹ • silt x p (represent (t • A))) (𝓝[≠] 0) (𝓝 (heat x (collect G A) p)):=by simpa only [zero_add,zero_smul,link_one,silt_0,sub_zero] using (hasDerivAt_iff_tendsto_slope_zero.mp (fragile x p A))

abbrev HopK(n:Side):=Site n × SpinIdx
def terse (x:HopK n):Site (More n):=node x.1
def walkB(u v: HopK n)(V:Bkg (More n)):Op Slot:= (matter (travel V (terse u) (shiftH (terse u) (terse v)))).val
def halo (P: Toy m n)(u v:HopK n)(x:Trip m n)(C: Fin m→ group.Color):Op Slot:= Matrix.of fun i j=> P (u,i) (v,j) x C
def handy(P:Toy m n):Prop:=∀ (u v:HopK n)(x:Trip m n)(C: Fin m→ group.Color) (g:E),halo P u v x (fun i=> group.adjoint g (C i))= twist (matter g) (halo P u v x C)
def mold(P:Toy m n)(u v: HopK n)(x:Trip m n)(V:Bkg (More n)):Op Slot:= halo P u v x (fun i=> silt (terse u) (x i) V)* walkB u v V
def cavil(P:Toy m n)(V:Bkg (More n)):Op (Single n):=Matrix.of fun i j=> (∑ x:Trip m n,mold P i.1 j.1 x V) i.2 j.2
lemma city (P:Toy m n)(h:handy P)(u v x)(V:Bkg (More n))(g:Site (More n)→ E): mold P u v x (Lattice.gauge g V)= (matter (g (terse u))).val*mold P u v x V*star ((matter (g (terse v))).val):=by
 let A:= (matter (g (terse u)))
 let B:= (matter (g (terse v)))
 unfold mold; rw [show (fun i=>silt _ _ _)=_ from funext (fun i=>silt_g (terse u) (x i) V g),h u v x]; let H:=halo P u v x (fun i=> silt (terse u) (x i) V)
 rw [show walkB u v (gauge g V)=A.val* walkB u v V*star B.val from ?_, twist_formula]; swap; · unfold walkB; rw [travel_gauge,stopH,map_mul,map_mul,map_inv]; rfl
 change A.val*H*star A.val*(A.val*_ *_)= _; rw [mul_assoc, ←mul_assoc (star _),←mul_assoc (star _),A.property.1,one_mul]; simp only [mul_assoc]; rfl -- tune
lemma cobblestone(P:Toy m n)(h:handy P)(V:Bkg (More n))(g:Site (More n)→E): cavil P (Lattice.gauge g V)=twist (tradew n g) (cavil P V):=by
 let H:= tradew n g; suffices hx:cavil P (gauge g V)*H.val= H.val*cavil P V by rw [twist_formula,←hx,Matrix.mul_assoc, H.property.2,Matrix.mul_one]
 ext ⟨x,i⟩ ⟨y,j⟩
 rw [Matrix.mul_apply,Matrix.mul_apply]; unfold Single; rw [Fintype.sum_prod_type, Fintype.sum_prod_type (α₁:=HopK n)]
 simp only [H,tradew,jump_apply,Equiv.refl_apply,mul_ite,ite_mul, mul_zero,zero_mul,sum_ite_irrel,sum_const_zero,sum_ite_eq,sum_ite_eq',mem_univ, ite_true]
 let A:=matter (g (terse x)); let B:=matter (g (terse y))
 change ((∑ t:Trip m n,mold P x y t (Lattice.gauge g V))*B.val) i j=(A.val*∑ t:Trip m n,mold P x y t V) i j
 simp only [city P h, Matrix.sum_mul,Matrix.mul_sum,Matrix.mul_assoc,show star ((matter (g (terse y))).val)* B.val=1 from B.property.1,mul_one]; rfl
end YM.CF.Nacre
