import YM.CF.Buffered.Growth
/-!
# Separate axial growth. Fixed q,3q anchors. The entropy replacement for
other m'³ periods doesn't require them to divide the other grown sides.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 22000
set_option linter.unusedSectionVars false
set_option maxHeartbeats 430000
noncomputable section
namespace YM.CF.Buffered.Region
open Function Filter NormedSpace SU Lat Lattice Cube Finset Mir Mir.Trip Phase RP MeasureTheory Roost Rails Mil RG WilsonStartup Spark Nova Fock Push.SectorMeasure Ordered Cin Stripe Tile Traversed Stack Bays Saddle
open Installed (point)
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder Fin.NatCast
attribute [local instance] opCStarAlgebra
variable {m v p B l n:Side}
variable {e x:ℝ} (K: Ticket m v B p e x)(q:Clip)(β u:ℝ)
local notation "M" => Axis → Side

namespace Growth

def layout (l:Side)(x:M) : Axis→Side:=fun i=>x i * l
lemma reaches (p:Even l.val)(x:Axis→Side): Landing (layout l x):= fun i=> p.mul_left _
def size (x:M) : ℕ:= ∏ i,(x i).val
lemma s_update (x:M)(i:Axis)(u:Side): size (update x i u)=u.val*∏ j ∈ (univ:Finset Axis).erase i,(x j).val:= by unfold size; rw [←mul_prod_erase univ _ (mem_univ i), update_self]; congr 1; exact prod_congr rfl fun j v=>by rw [update_of_ne (mem_erase.mp v).1]
lemma s_pos (x:M) : 0<size x := prod_pos fun i _=> (x i).property
lemma s_scale (x:M)(i:Axis)(u:Side): size (update x i u)=u.val*size (update x i 1):= by rw [s_update,s_update]; congr 1; exact (one_mul _).symm
lemma uni_v (t:Side): size (Uniform t)=t.val^4:=by simp [size,Uniform,Axis]

variable (Z:Badge v B) (l:Side)(L:Even l.val)(hu:0 ≤ u)
local notation "zz" δ => prism (layout l δ) K Z.reflected q β u
local notation "Zq" => prism (layout l (Uniform 1)) K Z.reflected q β u

def heightK (δ:M):= ‖prism (layout l δ) K Z.reflected q β u‖
#print heightK
local notation "W" δ:max => heightK K q β u Z l δ
private def edgeV (x:ℕ):Side:=⟨3+2*x,by omega⟩
private lemma beat (l:Side)(δ:M)(i:Axis)(v:Side): Traversed (away i (layout l δ)) (layout l (update δ i v)) (v*l):=⟨by simp [layout],fun j=> by simp [away,layout,j.property]⟩
include L hu
lemma positive_cube (δ:M): 0 ≤ prism (layout l δ) K Z.reflected q β u:=by
 letI : MeasurableSpace (EdgePorts (away 0 (layout l δ)) v B) :=⊤; haveI : DiscreteMeasurableSpace (EdgePorts (away 0 (layout l δ)) v B):= inferInstanceAs (@DiscreteMeasurableSpace _ ⊤); exact geA K Z q β u (Traversed.self 0 (layout l δ)) (reaches L δ) hu
-- ℓ=length in tiles of q. rest δ units of ℓ. applies to all axis enlargements.
lemma reduces (δ:M)(i:Axis)(a:Side): heightK K q β u Z l (update δ i a) ≤ heightK K q β u Z l (update δ i 1) ^ a.val:=by
 letI : MeasurableSpace (EdgePorts (away i (layout l δ)) v B) :=⊤; haveI : DiscreteMeasurableSpace (EdgePorts (away i (layout l δ)) v B):= inferInstanceAs (@DiscreteMeasurableSpace _ ⊤); exact monot K Z q β u (beat l δ i 1) (reaches L _) hu (beat l δ i a) (reaches L _) a (by rw [one_mul]; rfl)
private lemma bows (δ:M)(i:Axis)(a:ℕ): heightK K q β u Z l (update δ i 3) ^(a+1) ≤ heightK K q β u Z l (update δ i 1) ^ a * heightK K q β u Z l (update δ i (edgeV a)):=by
 letI : MeasurableSpace (EdgePorts (away i (layout l δ)) v B) :=⊤; haveI : DiscreteMeasurableSpace (EdgePorts (away i (layout l δ)) v B):= inferInstanceAs (@DiscreteMeasurableSpace _ ⊤); exact middle K Z q β u (beat l δ i 1) (reaches L _) hu (beat l δ i _) (reaches L _) (beat l δ i 3) (reaches L _) (by rw [one_mul]; rfl) a (by rw [one_mul]; rfl)
lemma height_min (δ:M): (W δ) ≤ W (Uniform 1) ^ size δ:=by -- notation binds ^ tune
 classical
 let f (z:Finset Axis): Axis → Side:= fun i=> if i∈z then δ i else 1
 have hp (z): (W (f z)) ≤ (W (Uniform 1)) ^ size (f z):=by
    induction z using Finset.induction_on with
    | empty=> rw [show f ∅=Uniform 1 from funext fun i=> if_neg (notMem_empty _),uni_v,show (1:Side).val^4=1 by decide,pow_one]
    | insert i z h ih=>
      have ht: update (f z) i 1=f z:=by unfold f; ext j; by_cases v:j=i <;> simp_all only [update_apply,ite_self,ite_false] -- tune
      rw [show f (insert i z)=update (f z) i (δ i) from ?_,s_scale,ht]
      · rw [mul_comm ((δ i).val),pow_mul]; refine (reduces K q β u Z l L hu (f z) i (δ i)).trans ?_; rw [ht]; exact pow_le_pow_left₀ (norm_nonneg _) ih _
      funext j; by_cases t:j=i <;> simp_all [update_apply,f]
 have hk:= hp univ; have ht:f univ=δ:=funext fun i=>if_pos (mem_univ _); rwa [ht] at hk
def debit (δ:M):ℝ:= Real.log ‖Zq‖- Real.log (W δ)/(size δ:ℝ)
local notation "D" δ:max => debit K q β u Z l δ
lemma h_nonneg (δ:M): 0 ≤ W δ:= norm_nonneg _ -- remove include
lemma base_debit (δ:M)(p:0 < W δ): 0 ≤ D δ:=by
 have h := height_min K q β u Z l L hu δ; have he:= Real.log_le_log p h; let n := size δ; rw [Real.log_pow] at he
 unfold debit; rw [sub_nonneg]; refine (div_le_iff₀ (by exact_mod_cast (s_pos δ))).2 ?_; rw [mul_comm]; exact he
private lemma climbs (δ₁ : M)(i:Axis)(w k:ℝ)(p:0 <  W (update δ₁ i 3))(h:D (update δ₁ i 3)≤k)(a:ℕ) : let y:=update δ₁ i (edgeV a)
 0 < W y ∧ (D y) ≤ (3/2:ℝ)* k:=by
 intro y; have v := bows K q β u Z l L hu δ₁ i a; let g:=update δ₁ i 1; let f:=update δ₁ i 3
 have hK:0 ≤ k:=(base_debit K q β u Z l L hu f p).trans h
 let A:=heightK K q β u Z l; have he:0 < A g:=lt_of_le_of_ne (norm_nonneg _) (fun u'=>by have hp:= p.trans_le (reduces K q β u Z l L hu δ₁ i 3); change 0 < A g ^ (3:ℕ) at hp; rw [←u', zero_pow (by decide: (3:ℕ)≠0)] at hp; exact lt_irrefl 0 hp)
 have hv':0 < A y:= pos_of_mul_pos_right (lt_of_lt_of_le (pow_pos p _) v) ?_ -- pos_of_mul_pos_* tune
 · refine ⟨hv',?_⟩; have ht:= Real.log_le_log (pow_pos p _) v; change Real.log (A f ^ _ ) ≤ Real.log (A g ^ _ * A y) at ht; rw [Real.log_mul (pow_pos he a).ne' hv'.ne', Real.log_pow, Real.log_pow] at ht
   let n:ℝ:= size g; let Z0:= Real.log ‖Zq‖; have wn:0<n := by unfold n; exact_mod_cast s_pos g
   have hy:(size y:ℝ)=(3+2*(a:ℝ))*n:=by unfold y; rw [s_scale]; simp [n,g,edgeV] -- tune push
   have hf:(size f:ℝ)=3*n:=by unfold f; rw [s_scale]; push_cast; rfl
   have he:= Real.log_le_log he (height_min K q β u Z l L hu g); rw [Real.log_pow] at he; change Real.log (A g) ≤ n*Z0 at he
   change Z0-Real.log (A f)/(size f:ℝ) ≤ _ at h; rw [hf] at h; change Z0-Real.log (A y)/(size y:ℝ) ≤ _; rw [hy]; apply sub_le_iff_le_add'.mpr
   rw [← sub_le_iff_le_add, le_div_iff₀ (by positivity)]; have hw:= (le_div_iff₀ (by positivity: 0<3*n)).1 (show Z0-k≤Real.log (A f)/(3*n) from by linarith); push_cast at ht; nlinarith
 exact pow_nonneg he.le a
lemma roof (a:ℕ)(p: 0 < W (Uniform 3)) : 0 < W (Uniform (edgeV a)) ∧ D (Uniform (edgeV a)) ≤ (3/2:ℝ)^4 * D (Uniform 3):=by
 let f(s:Finset Axis)(i:Axis):= if i∈s then edgeV a else (3:Side)
 suffices h:∀ S:Finset Axis, 0 < W (f S) ∧ D (f S) ≤ (3/2:ℝ)^S.card * D (Uniform 3) by specialize h univ; rw [show f univ=Uniform (edgeV a) from funext fun _=> if_pos (mem_univ _), card_univ] at h; exact h
 intro S; induction S using Finset.induction_on with
 | empty => simpa only [card_empty,pow_zero,one_mul,show f ∅=Uniform 3 from funext fun i=> (show _ from if_neg (notMem_empty i))] using And.intro p (le_refl (D (Uniform 3)))
 | insert i s h ih =>
   have hp: update (f s) i 3=f s:= by unfold f; funext j; by_cases v:j=i; subst j; simp [h]; rw [update_of_ne v]
   rw [card_insert_of_notMem h, show f (insert i s)= update (f s) i (edgeV a) from (by funext j; by_cases h:j=i <;> simp [f, h]), pow_succ', mul_assoc]; exact climbs K q β u Z l L hu (f s) i 0 _ (hp.symm ▸ ih.1) (hp.symm ▸ ih.2) a
-- uniform integer inequalities. avoid marking a specific on-plane q geometry.
lemma altitude (k:Side) (p: Odd k.val)(p₀: 0 < W (Uniform 1))(p₃: 0 < W (Uniform 3)): 0 < W (Uniform k) ∧ D (Uniform k) ≤ (3/2:ℝ)^4 * D (Uniform 3):=by
 obtain ⟨a,t⟩:=p; obtain _|a:=a
 · have h:k=1:=Subtype.ext (show k.val=1 by omega); rw [h]; refine ⟨p₀,?_⟩; let Z:=Real.log ‖Zq‖; rw [show D (Uniform 1)=0 by unfold debit; rw [uni_v]; simp [heightK]]; exact mul_nonneg (by positivity) (base_debit K q β u _ l L hu (Uniform 3) p₃)
 rw [show k=edgeV a from Subtype.ext (show k.val=3+2*a by omega)]; exact roof K q β u Z l L hu a p₃
end Growth
end YM.CF.Buffered.Region
#print axioms YM.CF.Buffered.Region.Growth.height_min
#print axioms YM.CF.Buffered.Region.Growth.altitude
