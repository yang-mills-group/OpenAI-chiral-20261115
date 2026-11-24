import YM.CF.Ione.Tick
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 20000
set_option linter.unusedVariables false
noncomputable section
namespace YM.CF.Ione
open Function Filter Metric NormedSpace Finset Fock Lattice Wilson Laurent Lat Rush SU Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant Phase Broc Matrix Scroll Thera Branch Laic Cube
open scoped Matrix.Norms.L2Operator Matrix Topology ContDiff MatrixOrder BigOperators InnerProductSpace Kronecker
attribute [local instance] opCStarAlgebra
open Urn Hake Pastry Salt Hive Vow Skye Scion Levier Spire Scree Stilo
attribute [local instance] opCStarAlgebra
variable {n:Type*}[LinearOrder n][Fintype n](b r t c:Bool)(U V:UNI n)
set_option quotPrecheck false
open scoped Classical
-- degree selection and rebate maps
variable (m:ℕ)(K:Finset n)
def ink_Q (A:Dough n):FC n:=∑ i:Finset n with i.card=m, crumb A.val i • poke i
lemma worthS(A:Dough n)(h:Flour K A.val): Flour K (ink_Q m A):=by
 refine Flour.sum _ fun i p=>?_ ; by_cases h':i∈ Wheat K; exact (Flour.point h').smul _
 rw [h.door h',zero_smul]; exact Flour.trivial
def wage_Q(A:Dough n): Dough n:=⟨ink_Q m A,worthS m _ A A.property⟩
lemma price_X(A:Dough n): crumb (wage_Q m A).val K=if K.card=m then crumb A.val K else 0:=by
 unfold wage_Q; simp only [ink_Q,crumb_sum,crumb_scale, Pastry.chip]; by_cases h:K.card=m<;>simp [h,eq_comm (a:=K)] -- tune
lemma pimp_Q(A B:Dough n)(t:∀ i:Finset n,crumb A.val i=crumb B.val i): A=B:=Subtype.ext (((fineShape A).allP.trans (sum_congr rfl fun i _=> congrArg (fun x:ℂ=>x • poke i) (t _))).trans (fineShape B).allP.symm)
lemma peek_P : Continuous (wage_Q (n:=n) m):=by
 refine Continuous.subtype_mk ?_ _; unfold ink_Q crumb; apply continuous_finsetSum; intro i _; have hp:Continuous (fun v:Dough n=> crumb v.val i):= (continuous_apply ∅).comp ((continuous_apply i).comp continuous_subtype_val); exact hp.smul continuous_const
lemma pose_U (A:ribbon n): wage_Q m (paintR b r U A)=paintR b r U (wage_Q m A):=by
 apply pimp_Q; intro i; rw [price_X,cribP,cribP]; let H:=quant (spice U r).val; split_ifs with p
 · apply sum_congr rfl; intro j _; rw [price_X]; split; rfl
   rename_i g; change H i j* _=H i j* _; rw [show H i j=0 from quant_grade _ _ _ (fun h=>g (h.symm.trans p)),zero_mul,zero_mul]
 symm; apply sum_eq_zero; intro j _; rw [price_X]; split; next g=> rw [show (quantU (n:=LeanV n) (spice U r)).val i j=0 from quant_grade _ _ _ (fun h=>p (h.trans g)),zero_mul]
 rw [Ione.sign0,mul_zero]
abbrev Mono_A (A:Dough n):Prop:=∀ i:Finset n,i.card≠2→ crumb A.val i=0
lemma up_r (A:Dough n)(p:Mono_A A): wage_Q 2 A=A:=by apply pimp_Q; intro i; rw [price_X]; split; rfl; exact (p _ ‹_›).symm
lemma plus_Y (A B:Dough n):wage_Q m (A+B)=wage_Q m A+wage_Q m B:=by apply pimp_Q; intro i; rw [price_X]; change ite _ (crumb (A.val+B.val) _) _ = crumb ((wage_Q m A).val+(wage_Q m B).val) _; rw [crumb_add,crumb_add,price_X,price_X]; split <;> simp
lemma bloom_M(i:LeanV n)(j:LeanV n)(D:Finset (LeanV n))(p:D.card≠2):crumb (put i*put j) D=0:=by
 by_cases h:i=j; rw [h,put_sq]; rfl
 let X:Finset (LeanV n):= {i,j}; rw [←show poke {i}=put i from Poly.tag_once _ _, ← show poke {j}=put j from Poly.tag_once _ _]; unfold poke; rw [Poly.tag_mul,if_pos (by simp [h]),crumb_scale,show crumb ((cane _).tag _) D= _ from Pastry.chip _ _]; rw [if_neg (fun l=>p ?_),mul_zero]; rw [l]; simp [h]
variable {N:Side}(s:Sweep N)
abbrev estate:= Bool × (SpinIdx × Slot)
def cast_H (i:Dwell N):Seat N × estate:= (cod_A i,i.1,i.2.1.2,i.2.2)
lemma sting:Injective (cast_H (N:=N)):=by
 rintro ⟨b,⟨i,v⟩,t⟩ ⟨c,⟨j,u⟩,w⟩ p; let y:=Prod.mk.inj p; have hh: Injective (@node N):= fun x y h=> (assembly N).embed_injective (add_right_cancel (show _+(1:Site (More N))=_+_ from h)); have he:=hh y.1; have hk:=Prod.mk.inj y.2; have hv:=Prod.mk.inj hk.2; exact Prod.ext hk.1 (Prod.ext (Prod.ext he hv.1) hv.2)
local notation "Dk"=> Finset (Dwell N)
lemma trill_b(X:Support (More N)): (camp X).card ≤ X.card*Fintype.card estate:=by
 have h:(camp X).image cast_H ⊆ X ×ˢ univ:=by intro i v; obtain ⟨x,p,rfl⟩:= mem_image.mp v; exact mem_product.mpr ⟨(mem_filter.mp p).2, mem_univ _⟩
 simpa only [card_image_of_injective _ sting,card_product,card_univ] using card_le_card h
abbrev fare_T (l:ℕ):ℕ:= 2^(l*Fintype.card estate)
local notation "Yh"=> (hail_Q s).val
lemma trill_V(j:Dk): (univ.filter fun i:Dk=>Yh i j ≠0).card ≤ fare_T j.card:=by
 let X:= actY s (abode j); let Z:= camp X; have hp: X.card≤ j.card:=by unfold X actY; rw [card_map]; apply card_image_le
 refine (card_le_card (t:=Z.powerset) (fun i p=>mem_powerset.mpr (nearV s _ j (mem_filter.mp p).2))).trans ?_; rw [card_powerset]; exact pow_le_pow_right₀ (by decide) ((trill_b _).trans (Nat.mul_le_mul_right _ hp))
lemma trill_Q(j:Dk): (∑ i:Dk,‖Yh i j‖) ≤ (fare_T j.card:ℝ):=by
 let M:= univ.filter fun i:Dk=>Yh i j≠0; rw [←sum_subset (subset_univ M) (fun i _ g=>by rw [show Yh i j=0 from not_not.mp fun t=> g (mem_filter.mpr ⟨mem_univ _,t⟩),norm_zero])]; apply le_trans (sum_le_sum (g:=fun _=>1) (fun i _=> (norm_entry ..).trans (CStarRing.norm_of_mem_unitary (hail_Q s).property).le)); simpa only [sum_const,nsmul_eq_mul,mul_one] using (Nat.cast_le (α:=ℝ)|>.mpr (trill_V s j))
end YM.CF.Ione
