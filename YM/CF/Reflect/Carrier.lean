import YM.CF.Reflect.Initial

/-! Generator coefficients in product-cone form. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.RP
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology
open Function Fock Filter NormedSpace SU Lat Lattice Branch Cube Tenant Phase Mir Mir.Trip MeasureTheory Finset Reflect
attribute [local instance] opCStarAlgebra
section car
variable {n : Type*} [LinearOrder n] [Fintype n]
lemma odd_kink (U : UNI n) (x y : Ket n) (s : Finset n) (g : twist U (cutM s)=cutM sᶜ) (p:acts (cutM s) x=x) (q:acts (cutM s) y=y) :
    chord true • (theta U (remove x)*remove y) + chord true • (theta U (create x)*create y) = -(create (acts U.val x) * remove y)- create y * remove (acts U.val x) := by
  have ht : acts (cutM sᶜ) (acts U.val x)=acts U.val x := by rw [←g,←swivel,p]
  have he := Sector.apart ((Sector.makeP (acts U.val x) ht).contr) (Sector.makeP y q) disjoint_compl_left
  have hh : remove (acts U.val x)*create y= -(create y*remove (acts U.val x)) := by simpa only [Sector.grainB, Bool.and_true,ite_true,neg_smul,one_smul] using he
  rw [theta_downV,theta_upV,Algebra.smul_mul_assoc,Algebra.smul_mul_assoc, smul_smul,smul_smul,hh]; change (Complex.I*Complex.I) • _ + (Complex.I * -Complex.I) • _=_; rw [mul_neg,Complex.I_mul_I,neg_smul,one_smul,neg_neg,one_smul]; abel
lemma Hpair (s : Finset n) (U : UNI n) (g : twist U (cutM s)=cutM sᶜ) (A B : Op n) (h : cutM s*A=A) (p : cutM s*B=B) :
    dg (-(U.val*A*star B))+dg (star (-(U.val*A*star B)))=
      ∑ j:n,(chord true • (theta U (remove (acts A (basisKet j)))*remove (acts B (basisKet j)))+chord true • (theta U (create (acts A (basisKet j)))*create (acts B (basisKet j)))) := by
  rw [dg_star, dg_neg, prizeUV, star_neg, star_sum, ←sum_neg_distrib, ←sum_neg_distrib, ←sum_add_distrib]
  refine sum_congr rfl ?_; intro i _
  rw [odd_kink U _ _ s g (by rw [←act_mul,h]) (by rw [←act_mul,p]), star_mul,show ∀ x:Ket n, star (remove x)=create x from fun x=>star_star _,act_mul]; change -(create _* remove _) + -(create _*remove _)=_; rw [sub_eq_add_neg]
lemma main_decomp (s : Finset n) (U : UNI n) (g : twist U (cutM s)=cutM sᶜ) (A : Op n) (p : IsSelfAdjoint A) (F : Op n) (k : twist U F= -A) (u : IsSelfAdjoint F) :
    let P := cutM s; let Q := cutM sᶜ; (P*F*P).trace=0 → dg A= theta U (dg (P*F*P)) + dg (P*A*P) + (dg (Q*A*P)+dg (star (Q*A*P))) := by
  intro P Q h
  have he : IsSelfAdjoint P := (cutM_idp ..).2; have hx : IsSelfAdjoint Q := (cutM_idp ..).2
  have hf : Q=1-P := dim_cut _
  have hm : theta U (dg (P*F*P))=dg (Q*A*Q) := by
    rw [theta_dg,h,star_zero,zero_smul,star_mul,star_mul, he,u, ←mul_assoc, map_mul,map_mul,k,show twist U P=Q from g,mul_neg,neg_mul, dg_neg,zero_sub,neg_neg]
  rw [hm, ←dg_add, ←dg_add, ←dg_add,star_mul,star_mul,he,hx,p]; apply congrArg; rw [hf]; noncomm_ring
@[fun_prop] lemma dg_cont : Continuous (dg (n:=n)) := continuous_finsetSum _ fun i _=> continuous_finsetSum _ fun j _=> (continuous_id.matrix_elem i j).smul continuous_const
lemma abs_dg (s : Finset n) (A : Op n) : Sector s false (dg (cutM s*A*cutM s)) := pair_charge (by
  have he : cutM s*cutM s=cutM s := (cutM_idp _).1; rw [mul_assoc _ _ (cutM s), mul_assoc (cutM s*A), he,←mul_assoc,←mul_assoc,he]) -- tune
end car
variable {m B : Side} (i : Axis) (x : Pack m B) (c : Foot m B)
lemma waking (y z : Pack m B) :
    let s:= tiedK m B i x
    let h : Pack m B→Op (Xmind m B) := fun y=>wiel m B (axisCut m B i c) (s y y).1
    let v := enter m B i; let w := exitK m B i; let A := v (s y y).1; let A' := v (s z z).1; let B₁ := w (s y y).1; let B' := w (s z z).1
    let L := Ledge m B i; let F := finger m B i; let K:= Xmind m B -- tune use explicit
    dg (wiel m B (axisCut m B i c) (s y z).1)=theta F (dg (L*h z*L))+dg (L*h y*L)+
      ((∑ j:Xmind m B, (chord true • (theta F (remove (acts A' (basisKet j)))* remove (acts A (basisKet j)))+chord true • (theta F (create (acts A' (basisKet j)))* create (acts A (basisKet j))))) +
      ∑ j:Xmind m B, (chord true • (theta F (remove (acts B' (basisKet j)))* remove (acts B₁ (basisKet j)))+chord true • (theta F (create (acts B' (basisKet j)))* create (acts B₁ (basisKet j))))) := by
  intro s h v w A A' B₁ B' L F K; let T := Tedge m B i; let d := axisCut m B i c
  let U := (s y z).1; let V := (s z y).1; let Y := wiel m B d U; let Z := wiel m B d V; let S := colony m B i
  have hk : rayUK m B i V=U := congrArg Prod.fst (sew i x z y)
  have hQ : rayUK m B i U=V := congrArg Prod.fst (sew i x y z)
  have ht : twist F Z= -Y := (reflected_H m B i V c).trans (by rw [hk])
  have hp : L*Y*L=L*h y*L := sup_area i (strum i x y z y) _; have hP : L*Z*L=L*h z*L := sup_area i (strum i x z y z) _
  have hz : T*Y*L= -(F.val*A'*star A)+ -(F.val*B'*star B₁) := by
    unfold T Y L; rw [acrossM]; unfold bendK
    rw [hQ, show enter m B i U=A from enter_area i (strum i x y z y), show exitK m B i U=B₁ from exit_area i (strum i x y z y), show enter m B i V=A' from enter_area i (strum i x z y z), show exitK m B i V=B' from exit_area i (strum i x z y z)]
  have he : dg Y=theta F (dg (L*Z*L))+dg (L*Y*L)+(dg (T*Y*L)+dg (star (T*Y*L))) := main_decomp S F (movedCol ..) Y (self_wiel ..) Z ht (self_wiel ..) (trayH i V d)
  rw [he,hp,hP,hz,dg_add,star_add,dg_add, add_add_add_comm (dg (-(F.val*A'*star A))), Hpair S F (movedCol ..) A' A (enter_pos ..) (enter_pos ..), Hpair S F (movedCol ..) B' B₁ (exit_pos ..) (exit_pos ..)] -- tune
end YM.CF.RP
