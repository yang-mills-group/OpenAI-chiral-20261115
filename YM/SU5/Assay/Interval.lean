import YM.SU5.Assay.Turnstile
import YM.SU5.Assay.Freeze
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
variable {i k:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}(V:Universal Y H i k I E)(s:ℕ)
variable {D:ℕ→Family (tent Y H)→Family (tent Y H)}{a b:ℕ→ℕ}(Q:Coherent (i:=i) (k:=k) (E:=E) Y H D a b)
variable (j:Axis){w:ℕ}{f:Family (tent Y H)}{S:Finset Cover}(t:InTest (tent Y H) true S false f)(hB:Between (tent Y H) j 0 (ruler Λ.block*w) S)
local notation "Z" u:max n:max k:max f:max=> train Y H s u n k S f
local notation "π" r:max=>i (a r)
local notation "ζ" r:max=> k (b r)
local notation "W" t:max=> volumeAround Λ l t S
local notation "uM" t:max=> (L₀^t*w)
include V Q hB
lemma banner_all (r:ℕ): ∀ᶠ e:ℕ in atTop, ∀ (f:Family (tent Y H)) (_:InTest (tent Y H) true S false f), ∀ (n:ℕ)(v:ℤ), 2*(ruler Λ.block*w*n) ≤ (((T₀ (π e) s).val:ℕ):ℤ)→
 sharp Y H (s+r) (π e) (ζ e) (banner j (uM r) ((L₀:ℤ)^r*v) n (Z r (π e) (ζ e) f))=sharp Y H s (π e) (ζ e) (banner j w v n f):=by
 induction r with
 | zero=> exact Eventually.of_forall fun e f t n v k=>by simp [train]
 | succ r ih=>
    have hM:Tendsto (fun r=>π r) atTop atTop:= V.pick.grow_i.tendsto_atTop.comp Q.growsA.tendsto_atTop
    let X:=W (r+1); let S0:=W r
    let A:=s+r
    have ht:∀ᶠ e in atTop,Tivoli X ((K).c (m (π e) (A+1))) :=hM.eventually (turning Y H (A+1) X)
    filter_upwards [ih,Q.finance (s+r+1),ht] with e he ae hh f t n q v
    let M':ℕ:=π e; let k':ℕ:= ζ e
    let F:=Z r M' k' f
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
    rw [← he f t n q v,←Nat.add_assoc s r, train_step]
    convert hp using 2 <;> rw [pow_succ'] <;> congr 1 <;> ring

omit hB
lemma screenFlash (c d d':ℝ) (hc:0<c) (hd:0<d)(he:d<d'):
  ∀ᶠ e:ℕ in atTop, ∀ (p:ℕ), 0<p → p ≤ (2*(T₀ (π e) s).val)^4 →
  ∀ (f:Family (tent Y H)), TestFamily K true f → pay f (c^p) →
    (‖sharp Y H s (π e) (ζ e) f‖≤d^p → ‖hot Y H s (π e) (ζ e) f‖ ≤ d'^p) ∧
    (‖hot Y H s (π e) (ζ e) f‖≤d^p → ‖sharp Y H s (π e) (ζ e) f‖ ≤ d'^p) := by
 let A:=LocalLimit.postage Λ.block Λ.R.L s
 have ht:Tendsto (fun e=> ζ e) atTop atTop:= (V.pick.grow_k.comp Q.growsB).tendsto_atTop
 filter_upwards [Q.finance s, ht.eventually (Assay.flashFreeze Y H s c d d' A hc hd he)] with e h g p hp t f y q
 obtain ⟨S,b⟩:=y.paid
 refine g _ h p hp ?_ S f b q
 unfold A; rw [← sites_postage]
 change (_:ℝ)≤ (((((T₀ (π e) s).val*2:ℕ)):ℝ)^4)
 rw [Nat.mul_comm]
 exact_mod_cast t

omit V Q
variable (w) (f0:ℕ→Family (tent Y H))
def slideN (i:ℕ):ℕ:=finalN (T₀ i s).val (16*Λ.block.val*w)
local notation "N₀"=> slideN Y s w
def Matinee (q:ℝ):Prop:= ∀ᶠ e:ℕ in atTop,
  let n:=N₀ (π e)
  ∀ v:ℤ, ‖hot Y H s (π e) (ζ e) (banner j w (w*v) n (f0 e))‖ ≤q^(4*n)

include V Q
lemma framing (hw:0<w):∀ᶠ e:ℕ in atTop,
    let n:=N₀ (π e); let x:=(T₀ (π e) s).val
    0<n ∧ 2*(ruler Λ.block*w*n) ≤ ((x:ℕ):ℤ) ∧ 4*n ≤ 2*x :=by
 let B:=16*Λ.block.val*w; have hb:0<B:=by unfold B; have p:=Λ.block.property; positivity
 filter_upwards [(site_law Y H V Q s).eventually_ge_atTop (2*B)] with e h
 intro n x
 have t:2*B*n≤x := by unfold n slideN finalN; rw [Nat.mul_comm]; exact Nat.div_mul_le_self ..
 have b:2*n≤x := le_trans (Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_right _ hb)) t
 refine ⟨Nat.div_pos h (by positivity),?_,by omega⟩
 have k:((2*B*n:ℕ):ℤ)≤ ↑x:=by exact_mod_cast t
 apply le_trans (le_of_eq ?_) k; unfold B ruler; push_cast; ring

include hB
lemma matineeTurn (tf:BQueue S f0 f)(hw:0<w)(c d:ℝ)(hc:0<c)(hd:c<d)
    (mtn:Matinee (i:=i) (k:=k) (a:=a) (b:=b) Y H s j w f0 c):Turnstile (i:=i) (k:=k) (a:=a) (b:=b) Y H s j w S f0 (d^2):=by
 intro r
 let q:=(c+d)/2; have ht:c<q:=by unfold q; linarith
 have he:q<d:=by unfold q; linarith
 let g:=train_queue Y H s Q f S f0 tf r
 obtain ⟨x,hx,_,hX⟩:=tf.bdd
 obtain ⟨y,hy,_,hY⟩:=g.bdd
 filter_upwards [screenFlash Y H V s Q x c q hx hc ht,screenFlash Y H V (s+r) Q y q d hy (hc.trans ht) he,hX,hY,mtn,banner_all Y H V s Q j hB r,framing Y H V s Q w hw] with e h₁ h₂ p u b t₁ t₂
 intro n v
 obtain ⟨hn,hn',t⟩:=t₂
 change 0<n at hn; have hp:0<4*n:=by positivity
 have a: 4*n≤ (2*(T₀ (π e) s).val)^4:=t.trans (Nat.le_pow (by omega))
 have a': 4*n≤ (2*(T₀ (π e) (s+r)).val)^4:=by
     rw [refine_side]; apply le_trans a; gcongr
     exact Nat.le_mul_of_pos_left _ (pow_pos Λ.R.L.property r)
 let F:=banner j (uM r) ((uM r)*v) n (Z r (π e) (ζ e) (f0 e))
 obtain ⟨hf,pF⟩:=main_bill j w (w*v) n (aux_test (tf.whereTo e)) p
 obtain ⟨hg,pG⟩:=main_bill j (uM r) ((uM r)*v) n (aux_test (g.whereTo e)) u
 rw [←pow_mul,show 2*(2*n)=4*n from by ring]
 apply (h₂ _ hp a' F hg pG).1
 unfold F
 rw [mul_assoc ((L₀:ℤ)^r) (w:ℤ) v,t₁ _ (tf.whereTo e) n _ hn']
 exact (h₁ _ hp a _ hf pF).2 (b v)
end YM.CF.Buffered.Afterglow.Tower.SlabMark
