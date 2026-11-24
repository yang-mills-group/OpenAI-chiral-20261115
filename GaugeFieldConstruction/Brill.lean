import GaugeFieldConstruction.Porches
set_option autoImplicit false
set_option maxHeartbeats 220000
set_option maxRecDepth 5700
set_option synthInstance.maxSize 28000
set_option quotPrecheck false
set_option linter.style.longLine false
open Function Filter Set MeasureTheory
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
namespace Spine
open Fock Analysis SlabMark MeshClock Vacancy Tapestry Etch
open Germ Alliance Lattice Py.Rate Py.Rate.LocalLimit Preparation Journey Satin Heat
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
noncomputable section
abbrev meshPin (P:Spine):AddSubgroup ℝ := marks (timeMesh P.par)
abbrev stampPin (P:Spine)(s:ℕ)(k:ℤ):P.meshPin:= notch (timeMesh P.par) s k
noncomputable def mellow (P:Spine)(s:ℕ):ℝ:=(mill (timeMesh P.par) s:ℝ≥0).val/ (ruler P.par.block:ℝ)
lemma mellow_good (P:Spine)(s:ℕ):0<P.mellow s:=div_pos (mill_pos _ _) (by exact_mod_cast ruler_gene P.par.block)
lemma mellow_firm(P:Spine)(s:ℕ)(k:ℤ): (P.stampPin s k:ℝ)=P.mellow s*((ruler P.par.block*k:ℤ):ℝ):=by
 have hp:0< (ruler P.par.block:ℝ):=by exact_mod_cast ruler_gene P.par.block
 change (k:ℝ)*(mill _ _:ℝ≥0).val =_; unfold mellow; push_cast; field_simp
lemma mellow_clock (P:Spine)(s:ℕ):P.mellow s= 1/ (2*((P.par.R.L.val:ℝ)^s)):=by
 have h:0<(P.par.R.L.val:ℝ):=by exact_mod_cast P.par.R.L.property
 have p:0<(P.par.block.val:ℝ):=by exact_mod_cast P.par.block.property
 unfold mellow mill timeMesh ruler; dsimp; push_cast; field_simp; ring
lemma mellow_age(P:Spine)(s t:ℕ)(p:s ≤ t):P.mellow t*(P.par.R.L.val:ℝ)^(t-s)=P.mellow s:=by
 have h:0<(P.par.R.L.val:ℝ):=by exact_mod_cast P.par.R.L.property
 rw [mellow_clock,mellow_clock]; field_simp
 rw [show t=s+(t-s) by omega, pow_add] -- nested?
 simp; ring
section
variable {P:Spine}{j:Axis}{k m s t:ℕ}{S T:Finset Cover}{F G:P.Test}{A B:P.Slabs j}{α β γ:P.meshPin}
local notation "L₀"=> P.par.R.L.val
local notation "M"=> timeMesh P.par
local notation "K"=> P.calibration
local notation "π"=> P.stampPin
variable (P) in
lemma minted_le(s:ℕ)(a b:ℤ): (π s a:ℝ) ≤ (π s b:ℝ) ↔ a≤b:= bell_le _ _ _ _
variable (P) in
lemma minted_sub(s:ℕ)(a b:ℤ): π s (b-a) =π s b- π s a:=Subtype.ext (show bell M s (b-a)=bell M s b-bell M s a from by unfold bell; push_cast; ring)
variable (P) in
lemma minted_val_add(s:ℕ)(a b:ℤ):(π s (a+b):ℝ)=(π s a:ℝ)+(π s b:ℝ):= bell_add _ _ _ _
variable (P) in
lemma minted_neg(s:ℕ)(a:ℤ): π s (-a)=-π s a:=Subtype.ext (by change bell M _ _= -bell M _ _; simp [bell])
lemma minted_tall (α:P.meshPin):∀ᶠ t:ℕ in atTop,∃ a:ℤ,π t a=α:=by
 obtain ⟨s,i,rfl⟩:=notch_exists M α; exact (eventually_ge_atTop s).mono fun t h=> ⟨_,notch_up M s t h i⟩
lemma mint_voxel (u:P.VMark):∀ᶠ t:ℕ in atTop,∃ v:Cover,P.vtile t v=u:=by
 filter_upwards [eventually_all.mpr (show ∀ j:Axis,∀ᶠ t:ℕ in atTop,∃ w:ℤ,π t w=u j from fun j=> minted_tall (P:=P) (u j))] with t h; choose k hk using h; exact ⟨k,funext hk⟩
lemma minted_le_sub {a b:P.meshPin}(p:(a:ℝ)≤(b:ℝ)):∀ᶠ t:ℕ in atTop,∃ k:ℕ,π t k=b-a:=by
 filter_upwards [minted_tall (P:=P) (b-a)] with t h
 obtain ⟨v,hv⟩:=h; have ht:0≤v:=(minted_le P t 0 v).mp (by
   change ((notch _ _ _):ℝ) ≤ _; rw [notch_zero,hv]; exact sub_nonneg.mpr p)
 refine ⟨v.toNat,by rw [Int.toNat_of_nonneg ht]; exact hv⟩
lemma convey_higher (F:P.Test) (h:k ≤ s)(p:s ≤ t): P.conveying s (t-s) (P.conveying k (s-k) F)=P.conveying k (t-k) F:=Subtype.ext (by
 have ht:= joined (D:=P.projection.refine) P.run P.large k (s-k) (t-s) F.val; rw [show k+(s-k)=s by omega,show s-k+(t-s)=t-k by omega] at ht; exact ht.symm)
lemma convey_start (F:P.Test)(s:ℕ): P.conveying s (s-s) F=F:=by rw [Nat.sub_self]; rfl
variable (P) in
/-- Buffered housing for this pose, in actual physical E chart. -/
def Marrow (j:Axis)(s:ℕ)(a b:ℝ)(S:Finset Cover):Prop:=∀ x∈S,
 a ≤ P.mellow s*((x j:ℝ) - P.calibration.ℓ) ∧ P.mellow s*((x j:ℝ)+P.calibration.ℓ) ≤ b
lemma Marrow.at_size {a b:ℤ}(S:Finset Cover):P.Marrow j s (π s a:ℝ) (π s b:ℝ) S ↔
 Between K j (ruler P.par.block*a) (ruler P.par.block*b) S:=by
 have ht : (∀ x:Cover,
 ((π s a:ℝ)≤ P.mellow s*((x j:ℝ)-P.calibration.ℓ)∧ P.mellow s*((x j:ℝ)+P.calibration.ℓ)≤(π s b:ℝ)) ↔
 (ruler P.par.block*a+P.calibration.ℓ ≤ x j ∧ x j+P.calibration.ℓ ≤ ruler P.par.block*b)):=by
    intro x; rw[mellow_firm,mellow_firm,mul_le_mul_iff_right₀ (mellow_good P s),mul_le_mul_iff_right₀ (mellow_good P s),le_sub_iff_add_le]
    norm_cast
 exact ⟨fun h x hx=>(ht x).mp (h x hx),fun h x hx=>(ht x).mpr (h x hx)⟩
lemma Marrow.refine {a b:ℝ}(u:P.Marrow j s a b S)(e:s ≤ t): P.Marrow j t a b (volumeAround P.par P.width (t-s) S):=by
 intro w z; obtain ⟨v,m,Y⟩:= Tower.shield P.par P.width S (t-s) z
 obtain ⟨hn,hy⟩:=u v m
 have hu:=Y j
 change |(w-L₀^(t-s) • v) j|+P.calibration.ℓ≤ (L₀:ℤ)^(t-s)*(P.calibration.ℓ:ℤ) at hu
 simp only [Pi.sub_apply,nsmul_eq_mul,Nat.cast_pow,Pi.mul_apply,Pi.natCast_apply,Pi.pow_apply] at hu
 have hr: |(w j:ℝ)-(L₀:ℝ)^(t-s)*(v j:ℝ)|+ (P.calibration.ℓ:ℝ) ≤ (L₀:ℝ)^(t-s)*(P.calibration.ℓ:ℝ):=by exact_mod_cast hu
 rw [←mellow_age P s t e,mul_assoc] at hn hy
 constructor
 · exact hn.trans (mul_le_mul_of_nonneg_left (by linarith [le_abs_self ( -((w j:ℝ)-(L₀:ℝ)^(t-s)*(v j:ℝ))),abs_neg ((w j:ℝ)-(L₀:ℝ)^(t-s)*(v j:ℝ))]) (mellow_good P t).le)
 exact le_trans (mul_le_mul_of_nonneg_left (by linarith [le_abs_self ((w j:ℝ)-(L₀:ℝ)^(t-s)*(v j:ℝ))]) (mellow_good P t).le) hy

lemma BEntry.mesh_frame {a:ℤ}{w:ℕ}(f:F∈bay K S true)(p:0<w)
 (v:P.Marrow j s (π s a:ℝ) (π s (a+w):ℝ) S): P.BEntry j w (P.shifts j (-a) F):=by
 have ht:=Between.relocate P.calibration j ((Marrow.at_size S).mp v) (-a)
 change Between K j (ruler P.par.block * (-a) + ruler P.par.block*a)
   (ruler P.par.block * (-a) +ruler P.par.block*(a+(w:ℤ))) _ at ht
 refine ⟨p,_,P.shifts_support j (-a) _ f,?_⟩; ring_nf at ht; exact ht

end
end
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
