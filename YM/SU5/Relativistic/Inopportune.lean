import YM.SU5.Relativistic.Congeal
/-! # physical stencil geometry. footprint and propagation. induction next. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Crest.Sleet
open Function Set Filter Topology NormedSpace MeasureTheory Metric Real Finset Lattice Cube Next.Free
open Laurent Bloch Fir Jill Ember Shore Cuest Lat Fock Nacre Skye Scroll Rush Dial Tulip Pannier.Chancel UpStart Buffered
open Lifted (nodeC basisC node_of)
open scoped Topology BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace Kronecker
attribute [local instance] opCStarAlgebra screen_fin
local notation "I"=>Complex.I
local notation "φ"=> 2*Real.pi
local notation "Φ"=> Set.Icc (-π) π
variable {d:ℕ}{s:Finset ℤ}{c:ℤ→Behind→ℂ}{a r:ℝ}
variable (P:UpStart d s c r (2*a))
variable (n:Side)(o:Cover)(A:ℕ)(F:Waxy)
local notation "G" s:max => strum n o A F s

def district (i:Finset ℤ)(o:Cover)(F:Waxy) : Finset Cover:= Finset.univ.biUnion fun a:SpinIdx=> i.biUnion (fun j=> (F a j).support.image (fun t=>o+tack t j))
lemma drive_entry (j:SpinIdx)(p:Finset ℤ)(i:ℤ)(u:i∈p)(x:WalkA)(v:x∈(F j i).support): o+tack x i∈district p o F:=by unfold district; exact mem_biUnion.mpr ⟨_,mem_univ j,mem_biUnion.mpr ⟨_,u,mem_image_of_mem _ v⟩⟩ -- arg order
variable (s':SU.Slot)
lemma windy_inner(o u:Cover)(i b:SpinIdx)(x y:SU.Slot)(T:Finset Cover)(p:o∈T)(t:u∈T)(z:Set.InjOn (wrap n) T):inner ℂ (basisC n o i x) (basisC n u b y)=if (o,i,x)=(u,b,y) then 1 else 0 := by
 unfold basisC; rw [inner_smul_right,inner_smul_left,basis_inner,basis_apply, Lifted.index,Lifted.index]; by_cases g:o=u; swap; · have ht: wrap n o≠wrap n u:= fun X=>g (z p t X); simp [g,ht]
 subst u; unfold Lifted.winding; by_cases h:i=b <;> by_cases t:x=y <;> simp [h,t,Lifted.winding, ←mul_assoc,fee_one, fee_real, ← Complex.star_def] -- sign

lemma printed_inside (T:Finset Cover)(k:WalkA)(i:ℤ)(x:o+tack k i∈T)(v:district (TwistT A) o F⊆ T) (h:Set.InjOn (wrap n) T) (g:SU.Slot)(j:SpinIdx):
    inner ℂ (basisC n (o+tack k i) j s') (strum n o A F g)= if s'=g ∧ i∈ TwistT A then F j i k else 0:=by
 classical
 have hp(a:SpinIdx)(u:ℤ)(b:u∈TwistT A): inner ℂ (basisC n (o+tack k i) j s') (gust n o a u (F a u) g) = if j=a∧s'=g∧i=u then F a u k else 0:=by
    unfold gust Finsupp.sum; rw [inner_sum]; dsimp only; let S:=(F a u).support
    have ht(z): tack k i=tack z u↔ k=z ∧ i=u:= by obtain ⟨e,h⟩:= tack_equiv ℤ; rw [←h,←h]; exact e.injective.eq_iff.trans (by simp only [Prod.mk.injEq])
    have hx(z:WalkA)(t:z∈S): inner ℂ (basisC n (o+tack k i) j s') (F a u z • basisC n (o+tack z u) a g)= if k=z ∧ i=u ∧ j=a ∧ s'=g then F a u z else 0:=by rw [inner_smul_right,windy_inner n _ _ j a _ _ T x (v (drive_entry o F a _ u b z t)) h]; simp only [Prod.mk.injEq,add_right_inj,ht, and_assoc]; split_ifs <;> simp_all -- insure addition Inj names
    split_ifs with m
    · obtain ⟨c,χ,t⟩:= m; rw [sum_eq_single k]; by_cases e:k∈S; · rw [hx k e]; simp only [c,χ,t,and_self,↓reduceIte]
      · simp [(Finsupp.notMem_support_iff.mp e)]
      · intro i z p; rw [hx i z, if_neg]; simp [Ne.symm p]
      intro k; simp only [Finsupp.notMem_support_iff.mp k,zero_smul,inner_zero_right]
    apply sum_eq_zero; intro a g; rw [hx a g]; split_ifs with h; exact (m ⟨h.2.2.1,h.2.2.2,h.2.1⟩).elim; rfl
 unfold strum; simp_rw [inner_sum]; split_ifs with m
 · rw [sum_eq_single j]; rw [sum_eq_single i]; simpa [m.1] using hp j i m.2
   · intro l v g; simp [hp _ _ v,Ne.symm g]
   · exact fun p=> (p m.2).elim
   · intro a p t; apply sum_eq_zero; intro l u; rw [hp a l u, if_neg]; simp [Ne.symm t]
   simp
 apply sum_eq_zero; intro a _; apply sum_eq_zero; intro y u; rw [hp a y u]; split; next g=> exact (m ⟨g.2.1,g.2.2.symm ▸ u⟩).elim
 rfl
-- scope budgets for lower-generation vector
include P
lemma Solstice (p:0<a)(v:0<d) : ∃ R> (0:ℝ),∀ A:ℕ,∃ F:Waxy, (∀ n:Side,∀ o:Cover,∀ s:SU.Slot,‖strum n o A F s‖≤R) ∧ (∀ i∈plusHalf,∀ j:ℤ,j∉s→F i j=0) ∧
 (∀ S:Finset WalkA, ∑ x∈S, ‖F 2 0 ((d:ℤ) • x)-(if x=0 then 1 else 0)‖^2 ≤ (R*spangle a A)^2) ∧
     ∀ᶠ N:ℕ in atTop,∀ (M:Jill.Male),N ≤ M.val.val → ∀ n:Side,∀ f:SU.Slot,∀ o:Cover, let X:=strum n o A F f; ‖acts (spar 4 M (1:Pane n)) X-X‖≤R*spangle a A:=by
 have he:IsCompact (backPane ×ˢ Φ):= (isCompact_univ_pi (fun _=> isCompact_Icc)).prod isCompact_Icc
 let L:=Function.uncurry (target s c); have hC:ContinuousOn L (backPane ×ˢ Φ):=by
    rw [show L=(fun p:Behind×ℝ=> ∑ i:SpinIdx,turned s c i p.1 p.2 • basisKet i) from funext (fun i=> (basis_expand (target s c i.1 i.2)).symm)]
    apply continuousOn_finsetSum; intro i _; exact ((P.turned_c i).mono (fun _ v=> ⟨Set.mem_univ _,v.2⟩)).smul continuousOn_const
 obtain ⟨C,vC⟩:=he.exists_bound_of_continuousOn hC; obtain ⟨B,h,t⟩:=P.receiptZ p v
 let R:= 3*B+|C|; have hr:3*B≤R:=le_add_of_nonneg_right (abs_nonneg _); have hB:B≤ R:= by linarith
 refine ⟨R,by linarith,fun i=> ?_⟩
 obtain ⟨F,U₁,h₁,h₂⟩:= t i
 refine ⟨F, fun n o s'=> ?_,h₁, fun A=> (h₂ A).trans (pow_le_pow_left₀ (mul_pos h (spangle_pos ..)).le (mul_le_mul_of_nonneg_right hB (spangle_pos ..).le) _),?_⟩
 · rw [← act_unit_norm (star (ear n))]; change ‖acts (star (ear n).val) _‖≤ _; rw [wake_kernel n]; apply shellBound _ _ _ (by linarith); intro k
   let x:= flowE n k; let y:= flowL n k
   obtain ⟨u,g⟩:=here_s n k
   let Z:= timbre i F x y; let A:=target s c x y
   unfold snap; rw [norm_smul,mode_real _ _ (mel_h k).1,one_mul]; apply (norm_le_norm_sub_add Z A).trans; have hx: ‖A‖≤ |C|:= (vC (x,y) ⟨u,g⟩).trans (le_abs_self _); have ht:= le_trans (U₁ x u y g) (mul_le_of_le_one_right h.le (show spangle a (i:ℤ) ≤1 from Real.exp_le_one_iff.mpr (by simp only [Int.natAbs_natCast]; nlinarith only [Nat.cast_nonneg (α:=ℝ) i, p])))
   change _ ≤ R; change ‖Z-A‖ ≤ B at ht; unfold R; linarith
 apply (take_patch P (mul_pos h (spangle_pos ..)) i F U₁).mono; intro k u M v n s' o; exact (u M v n s' o).trans (by rw [←mul_assoc]; exact mul_le_mul_of_nonneg_right hr (spangle_pos ..).le)
end YM.CF.Crest.Sleet
#print axioms YM.CF.Crest.Sleet.Solstice
