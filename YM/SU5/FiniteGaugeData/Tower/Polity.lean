import YM.SU5.FiniteGaugeData.Tower.Delivered
import YM.SU5.FiniteGaugeData.Tower.Performed
/-!
# Transfer central train across any fixed number of rungs, arbitrary n
under finite-period length constraint. Constant maturity stage independent
of number of slabs n. Even spec across whole bbox not needed. -/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 5900
set_option maxHeartbeats 390000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.SlabMark
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
local notation "K" => tent Y H
local notation "L₀"=>Λ.R.L.val
local notation "m" n:max s:max=>momentm Y n s
local notation "T₀" n:max s:max=> Journey.side Y n s
lemma refine_side(n s t:ℕ): (Journey.side Y n (s+t)).val=L₀^t * (Journey.side Y n s).val:=by
 induction t with
 | zero=> simp
 | succ i ih=>
    have ht:= Ratio.exact_size (Vale.apt (Y.ir n) Λ.block Λ.R.L (s+i))
    rw [pow_succ',←Nat.add_assoc s]; change (Journey.side Y n ((s+i)+1)).val=(L₀*L₀^i)*_
    change (T₀ n (s+i+1)).val=(T₀ n (s+i)).val*(Λ.R.L).val at ht; rw [ht,ih]; ring
lemma side_register(n s:ℕ): (((K).c (m n s)).val)=(Journey.side Y n s).val:=congrArg Subtype.val (terrain Y H (Y.ir n) s)
include H
lemma goes(s:ℕ):Tendsto (fun n=>((Journey.side Y n s).val)) atTop atTop :=by
 have h:= (c_grows (tent Y H)).comp (momentum Y s)
 simp_rw [←side_register Y H]; exact h
lemma moment_le(n s:ℕ): (m n s).val≤ (Journey.side Y n s).val:= (side_register Y H n s) ▸ side_lower (tent Y H)

lemma expands_shape {S:Finset Cover}{j:Axis}{t:ℤ}(b:Between (tent Y H) j 0 t S)(h:ℕ): Between (tent Y H) j 0 ((L₀:ℤ)^h*t) (volumeAround Λ l h S):=by
 intro w z
 obtain ⟨v,mY,u⟩:=shield Λ l S h z
 obtain ⟨x,k⟩:= b v mY; rw [zero_add] at x; have hu:=u j; change |(w-L₀^h • v) j|+ ((K).ℓ:ℕ) ≤ L₀^h * (((K).ℓ:ℕ):ℤ) at hu
 let c:ℤ:=(Λ.R.L.val:ℤ)^h
 have hC:0≤ c:=by unfold c; positivity
 have hv:= abs_le.mp (show |(w-L₀^h • v) j| ≤ c*(((K).ℓ:ℕ):ℤ)-(((K).ℓ:ℕ):ℤ) from by change _ ≤ (Λ.R.L.val:ℤ)^h* (↑((K).ℓ):ℤ)-_; linarith)
 simp only [Pi.sub_apply,Pi.smul_apply,nsmul_eq_mul,Nat.cast_pow,Pi.mul_apply,Pi.natCast_apply,Pi.pow_apply] at hv
 change (0+(((K).ℓ:ℕ):ℤ) ≤ w j) ∧ w j+(((K).ℓ:ℕ):ℤ)≤c*t
 change (((K).ℓ:ℕ):ℤ) ≤ v j at x; change v j+(((K).ℓ:ℕ):ℤ)≤ t at k
 constructor <;> (unfold c at *; nlinarith [mul_le_mul_of_nonneg_left x hC,mul_le_mul_of_nonneg_left k hC])

variable {i k:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}(V:Universal Y H i k I E)(s:ℕ)
variable {D:ℕ→Family (tent Y H)→Family (tent Y H)}{a b:ℕ→ℕ}(Q:Coherent (i:=i) (k:=k) (E:=E) Y H D a b)
variable (j:Axis){w:ℕ}{f:Family (tent Y H)}{S:Finset Cover}(t:InTest (tent Y H) true S false f)(hB:Between (tent Y H) j 0 (ruler Λ.block*w) S)
local notation "Z" u:max n:max k:max=> train Y H s u n k S f
local notation "π" r:max=>i (a r)
local notation "ζ" r:max=> k (b r)
local notation "W" t:max=> volumeAround Λ l t S
local notation "uM" t:max=> (L₀^t*w)
include V Q hB t
lemma banner_drop (r:ℕ): ∀ᶠ e:ℕ in atTop, ∀ (n:ℕ)(v:ℤ), 2*(ruler Λ.block*w*n) ≤ (((T₀ (π e) s).val:ℕ):ℤ)→
 sharp Y H (s+r) (π e) (ζ e) (banner j (uM r) ((L₀:ℤ)^r*v) n (Z r (π e) (ζ e)))=sharp Y H s (π e) (ζ e) (banner j w v n f):=by
 induction r with
 | zero=> exact Eventually.of_forall fun n v p' k=>by simp [train]
 | succ r ih=>
    have hM:Tendsto (fun r=>π r) atTop atTop:= V.pick.grow_i.tendsto_atTop.comp Q.growsA.tendsto_atTop
    let X:=W (r+1); let S0:=W r
    let A:=s+r
    have ht:∀ᶠ e in atTop,Tivoli X ((K).c (m (π e) (A+1))) :=hM.eventually (turning Y H (A+1) X)
    filter_upwards [ih,Q.finance (s+r+1),ht] with e he ae hh n q v
    let M':ℕ:=π e; let k':ℕ:= ζ e
    let F:=Z r M' k'
    have hs:InTest K true S0 false F := prepared_train Y H s S r _ _ t
    have Hs: Between K j 0 (ruler Λ.block * ((L₀:ℤ)^r*w)) S0 :=by rw [mul_left_comm]; exact expands_shape Y H hB r
    have he₁:legalAt Y A M' k':=⟨ae.depth,ae.enters⟩
    let F':=block Y H A M' k' S0 F
    have hx:Delivered Y H A M' k' F F':=⟨aux_test hs,aux_test (booked ..),reserved Y H A S0 M' k' he₁ hs hh⟩
    let U:ℤ:= (L₀:ℤ)^r
    have hy:2*(ruler Λ.block * (U*w) * n) ≤ (((T₀ M' A).val:ℕ):ℤ):=by
       unfold A; rw [refine_side,Nat.cast_mul,Nat.cast_pow]; have ht:0≤U:=by positivity
       rw [show 2*(ruler Λ.block *(U*w)*n)=U*(2*(ruler Λ.block*w*n)) from by ring]; exact mul_le_mul_of_nonneg_left v ht
    have hp:=delivering Y H A M' k' he₁ (bulk_lift Y H A M' k' j he₁ hx n ((L₀:ℤ)^r*q) hs Hs (by positivity) hy)
    rw [← he n q v,←Nat.add_assoc s r, train_step]
    convert hp using 2 <;> push_cast <;> rw [pow_succ'] <;> congr 1 <;> ring
end YM.CF.Buffered.Afterglow.Tower.SlabMark
#print axioms YM.CF.Buffered.Afterglow.Tower.SlabMark.banner_drop
