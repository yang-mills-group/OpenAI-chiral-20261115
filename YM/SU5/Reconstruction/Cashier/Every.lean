import YM.SU5.Reconstruction.Cashier.Watch
/-! Banner estimates to all stages. Variant of Polity and PureCap. -/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 5900
set_option maxHeartbeats 390000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.SlabMark.Bankroll
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
variable {i k:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}(V:Universal Y H i k I E)(s:ℕ)
variable {D:ℕ→Family (tent Y H)→Family (tent Y H)}{a b:ℕ→ℕ}(Q:Coherent (i:=i) (k:=k) (E:=E) Y H D a b)
variable (j:Axis){w:ℕ}{f:Family (tent Y H)}{S:Finset Cover}(t:InTest (tent Y H) true S false f)(hB:Between (tent Y H) j 0 (ruler Λ.block*w) S)
local notation "Z" u:max n:max k:max=> train Y H s u n k S f
local notation "π" r:max=>i (a r)
local notation "ζ" r:max=> k (b r)
local notation "W" t:max=> volumeAround Λ l t S
local notation "uM" t:max=> (L₀^t*w)
include V Q hB
lemma uniform_drop (r:ℕ): ∀ᶠ e:ℕ in atTop, ∀ {f:Family (tent Y H)}, InTest K true S false f → ∀ (n:ℕ)(v:ℤ), 2*(ruler Λ.block*w*n) ≤ (((T₀ (π e) s).val:ℕ):ℤ)→
 sharp Y H (s+r) (π e) (ζ e) (banner j (uM r) ((L₀:ℤ)^r*v) n (train Y H s r (π e) (ζ e) S f))=sharp Y H s (π e) (ζ e) (banner j w v n f):=by
 induction r with
 | zero=> exact Eventually.of_forall fun n f t v p' k=>by simp [train]
 | succ r ih=>
    have hM:Tendsto (fun r=>π r) atTop atTop:= V.pick.grow_i.tendsto_atTop.comp Q.growsA.tendsto_atTop
    let X:=W (r+1); let S0:=W r
    let A:=s+r
    have ht:∀ᶠ e in atTop,Tivoli X ((K).c (m (π e) (A+1))) :=hM.eventually (turning Y H (A+1) X)
    filter_upwards [ih,Q.finance (s+r+1),ht] with e he ae hh f pf n q v
    let M':ℕ:=π e; let k':ℕ:= ζ e
    let F:=train Y H s r M' k' S f
    have hs:InTest K true S0 false F := prepared_train Y H s S r _ _ pf
    have Hs: Between K j 0 (ruler Λ.block * ((L₀:ℤ)^r*w)) S0 :=by rw [mul_left_comm]; exact expands_shape Y H hB r
    have he₁:legalAt Y A M' k':=⟨ae.depth,ae.enters⟩
    let F':=block Y H A M' k' S0 F
    have hx:Delivered Y H A M' k' F F':=⟨aux_test hs,aux_test (booked ..),reserved Y H A S0 M' k' he₁ hs hh⟩
    let U:ℤ:= (L₀:ℤ)^r
    have hy:2*(ruler Λ.block * (U*w) * n) ≤ (((T₀ M' A).val:ℕ):ℤ):=by
       unfold A; rw [refine_side,Nat.cast_mul,Nat.cast_pow]; have ht:0≤U:=by positivity
       rw [show 2*(ruler Λ.block *(U*w)*n)=U*(2*(ruler Λ.block*w*n)) from by ring]; exact mul_le_mul_of_nonneg_left v ht
    have hp:=delivering Y H A M' k' he₁ (bulk_lift Y H A M' k' j he₁ hx n ((L₀:ℤ)^r*q) hs Hs (by positivity) hy)
    rw [← he pf n q v,←Nat.add_assoc s r, train_step]
    convert hp using 2 <;> push_cast <;> rw [pow_succ'] <;> congr 1 <;> ring

section packed
omit Q hB V
variable (C:ℝ)
private lemma clipped_small {F:ℕ→ℕ}(v:Tendsto F atTop atTop)(q:ℝ)(x:0≤q): ∀ᶠ i in atTop,∀n:ℕ,n ≤ F i→ Real.exp (-((F i:ℕ):ℝ)^2)*(q^(4*n)) ≤ Real.exp (-2000*(n:ℝ)):=by
 filter_upwards [ (tendsto_natCast_atTop_atTop (R:=ℝ)|>.comp v).eventually_ge_atTop (4*q+2000)] with i hi n u
 have he: q≤ Real.exp q:=by linarith [Real.add_one_le_exp q]
 have hi:(4*q+2000) ≤ (↑(F i):ℝ):=hi
 have hx:(n:ℝ) ≤ F i:= by exact_mod_cast u
 have hg:= Nat.cast_nonneg (α:=ℝ) n
 calc _ ≤ Real.exp (-((F i:ℕ):ℝ)^2)* (Real.exp q)^(4*n) := by gcongr
      _ = Real.exp (-((F i:ℕ):ℝ)^2+(4*n:ℕ)*q):= by rw [Real.exp_add, Real.exp_nat_mul]
      _ ≤ _:= by apply Real.exp_le_exp_of_le; push_cast; nlinarith

open SatinVerification
variable (G:GroundExtension (i:=i) (k:=k) (E:=E) Y H)
local notation "J₀" r:max=> i (G.rows r)
local notation "J₁" r:max=> k (G.columns r)
include V
private lemma exponent_plate (h:0≤C):∀ᶠ r in atTop,∀ n≤(T₀ (J₀ r) s).val,∀ f:Family K,TestFamily K true f→pay f (C^(4*n))→‖sharp Y H s (J₀ r) (J₁ r) f-hot Y H s (J₀ r) (J₁ r) f‖≤ Real.exp (-2000*(n:ℝ)):=by
 filter_upwards [clipped_small (site_law Y H V G.history s) C h,G.clipped s] with i a b n t f p v; exact (b p _ v).trans (a n t)
variable (F:ℕ→Family (tent Y H))(p:∀i,InTest (tent Y H) true S false (F i))(hp:∀i,pay (F i) C) (wage:Rolls Y H s G F w)(e:0 < w)
local notation "B₀" i:max r:max=>train Y H s r (J₀ i) (J₁ i) S (F i)
local notation "b₀"=>ruler Λ.block
noncomputable def rate : ℝ:=Real.exp (-512)
omit V in
lemma pennies : 0<rate:=Real.exp_pos _
include p hp wage e hB
lemma allAlong (r:ℕ) : ∀ᶠ i in atTop,∀ n:ℕ,∀ v:ℤ,
 0<n→2*(b₀*w*n) ≤ (((T₀ (J₀ i) s).val:ℕ):ℤ)→ (((T₀ (J₀ i) s).val:ℕ):ℤ) ≤ (4*(b₀*w*n))→
 ‖hot Y H (s+r) (J₀ i) (J₁ i) (banner j (uM r) ((L₀:ℤ)^r*v) n (B₀ i r))‖ ≤ rate^(2*n):=by
 let N(i):= (T₀ (J₀ i) (s+r)).val
 obtain ⟨A,p₀,Tp⟩:=fares Y H s G.history S r; have ht:0≤ C:=pay_nonneg (hp 0)
 filter_upwards [wage j,uniform_drop Y H V s G.history j hB r,Tp 1 zero_lt_one, exponent_plate Y H V (s+r) (A*C) G (by positivity)] with i W₀ t p' t' n v hh Q y
 have h(n:ℕ): 1 ≤ b₀*(w:ℤ):= by
                                       have ht:0<(w:ℤ):=by exact_mod_cast e
                                       have hr:= ruler_gene Λ.block; nlinarith
 let f:=F i; let g:= B₀ i r
 let b:=sharp Y H (s+r) (J₀ i) (J₁ i); let a:= hot Y H (s+r) (J₀ i) (J₁ i)
 let X:=banner j (uM r) ((L₀:ℤ)^r*v) n g; let g₀:=(T₀ (J₀ i) s).val
 obtain ⟨c₀,k₁⟩:= main_bill j (uM r) ((L₀:ℤ)^r*v) n (aux_test (prepared_train Y H s S r _ _ (p i))) ((p' _ (p i) C (hp i)).2.1)
 have hu:n≤g₀:=by
    change _ ≤ (g₀:ℤ) at Q; zify; nlinarith [mul_le_mul_of_nonneg_right (h 0) (show 0≤(n:ℤ) by positivity)]
 have hu':n ≤ N i:= hu.trans (by unfold N g₀; rw [refine_side]; exact Nat.le_mul_of_pos_left _ (pow_pos Λ.R.L.property r))
 have hgx : ‖b X‖≤ Real.exp (-3000*(n:ℝ)):= by unfold b X g; rw [t (p i) n v Q]; exact W₀ n v hh Q y
 have hhΩ:(1:ℝ)≤(n:ℝ):=by exact_mod_cast hh
 have hv:Real.exp (-3000*(n:ℝ)) ≤ Real.exp (-2000*(n:ℝ)):=by apply Real.exp_le_exp_of_le; linarith
 change ‖a X‖ ≤ _
 calc _ ≤ _ := (norm_le_norm_sub_add _ (b X)).trans (add_le_add ((norm_sub_rev ..).trans_le (t' _ hu' X c₀ k₁)) (hgx.trans hv))
      _ ≤ Real.exp (976*(n:ℝ))*Real.exp (-2000*(n:ℝ)):= by
         have h:2 ≤ Real.exp (976*(n:ℝ)):= by linarith only [Real.add_one_le_exp (976*(n:ℝ)),hhΩ];
         nlinarith [Real.exp_pos (-2000*(n:ℝ))]
      _ = _:= by unfold rate; rw [←Real.exp_add,←Real.exp_nat_mul]; push_cast; ring_nf
end packed
end YM.CF.Buffered.Afterglow.Tower.SlabMark.Bankroll
#print axioms YM.CF.Buffered.Afterglow.Tower.SlabMark.Bankroll.allAlong
