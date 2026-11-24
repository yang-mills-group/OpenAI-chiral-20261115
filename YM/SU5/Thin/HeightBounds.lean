import SatinFixedContrastNovember4
import YM.SU5.Thin.Banner
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 6000
set_option maxHeartbeats 400000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.SlabMark
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Heat Analysis
open Dial -- `mateK`
open CF.Pannier.Damask
variable {P : Preparation} {l : ℕ} (Y : Course P (VolumeCape.Dream.Nimbus l)) (H : Real.exp 1 ≤ P.x)
local notation "K" => tent Y H
variable {i k:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}(V:Universal Y H i k I E)(s:ℕ)
variable {D:ℕ→Family (tent Y H)→Family (tent Y H)}{a b:ℕ→ℕ}(Q:Coherent (i:=i) (k:=k) (E:=E) Y H D a b)
local notation "π" r:max=> i (a r)
local notation "ζ" r:max=> k (b r)
local notation "Z" p:max i:max k:max=> ((Y.voyage i).X (Y.uv k)).gram p
local notation "R" p:max i:max=> (Y.voyage i).CapeT p
local notation "N" s:max r:max => side Y r s
open Pastry
private lemma canopy (s i k:ℕ)(f:Mark (side Y i s))(c:∀ x,‖f x‖≤1) : Papal.Backlog Y s i k 1 0 0 f := by
  intro x
  simp only [zero_mul,neg_zero,add_zero,Real.exp_zero]
  let A':=f (x.1,(R s i) x); let Q':=changeM P.U ((R s i) x) (Z s i k).J.M
  have hy:‖Q'‖=1:= (Papal.safety Y s i k x).2.2
  let U:= acts (star A') (mateK (N s i)); have hp:‖U‖≤1:=(Graph.spentS ..).trans (by rw [norm_star,(tickB _).2,mul_one]; exact c _)
  intro q; simp only [costs,one_pow,mul_one]; exact (norm_inner_le_norm ..).trans ((mul_le_mul hp (CF.Pannier.Chancel.token_limit _ hy) (norm_nonneg _) zero_le_one).trans_eq (one_mul _))
private lemma sharpSite (s i:ℕ) : sites (N s i) = (4*(P.block.val:ℝ))^4 * ((momentm Y i s).val:ℝ)^4:= by
  unfold sites side Preparation.Ctor cell CSide More momentm; push_cast; ring_nf
private lemma older {N₀:Side}(S:Mark N₀→ℂ)(T:ℝ)(_:0≤T)(h:∀ c:ℂ,∀ f,S (c • f)=c*S f)
    (g:∀ f:Mark N₀,Envelope f→(∀ z,‖f z‖≤1)→‖S f‖≤T) : ∀ f:Mark N₀, Envelope f →∀ c:ℝ,0≤c→(∀ z,‖f z‖≤c)→‖S f‖≤T*c:=by
  intro f e c u f'
  rcases u.eq_or_lt with w|w
  · subst c; have p : (0:ℂ) • f=f:=by funext i; have h:f i=0:=norm_le_zero_iff.mp (f' i); rw [Pi.smul_apply,zero_smul,h]
    exact (show S f=0 from ((congrArg S p).symm.trans (by rw [h,zero_mul]))) ▸ (by rw [norm_zero,mul_zero])
  let a:ℂ:=(c:ℂ); let f'' := a⁻¹ • f; have hp:(a:ℂ)≠0:=Complex.ofReal_ne_zero.mpr w.ne'; have ht:‖a‖=c:=(Complex.norm_real ..).trans (Real.norm_of_nonneg w.le)
  have hf : Envelope f'':= Girt.pole_w f _ (continuous_const_smul (a⁻¹)) e
  have hx: ∀ z,‖f'' z‖≤1:= by
    intro i; change ‖a⁻¹ • (f i)‖≤1; rw [norm_smul,norm_inv,ht]; exact (mul_le_mul_of_nonneg_left (f' _) (inv_nonneg.mpr w.le)).trans_eq (inv_mul_cancel₀ w.ne')
  have hg:=g f'' hf hx
  rw [show S f=a * S f'' from (congrArg S (smul_inv_smul₀ hp f)).symm.trans (h a f''),norm_mul,ht]; exact (mul_le_mul_of_nonneg_left hg w.le).trans_eq (mul_comm ..)
private lemma carry {A B:Side}(t:A=B)(F: Mark B→ℂ)(T:ℝ)
    (h:∀ f:Mark B,Envelope f→∀ c:ℝ,0≤c→ (∀ v,‖f v‖≤c)→‖F f‖≤ T*c) :
    ∀ f:Mark A,Envelope f→∀ c:ℝ,0≤c→ (∀ v,‖f v‖≤c)→‖F (t ▸ f)‖≤ T*c:=by subst A; exact h

open CF.Pannier

def PaidHeight (q:ℝ) : Prop:= ∀ᶠ e in atTop, ∀ r:Ferry Y s (π e) (ζ e),
    ∀ f:Mark ((tent Y H).c (momentm Y (π e) s)), Envelope f → ∀ c:ℝ,0≤c→(∀ v,‖f v‖≤c)→
      ‖collector Y H (π e) (ζ e) r.depth s f‖ ≤ Real.exp (q*((momentm Y (π e) s).val:ℝ)^4)*c -- args?? using π ζ dep
include V Q
lemma heightGain {A:ℝ}(p:Inflation A P) : ∃ q:ℝ,0≤q∧∀ᶠ s:ℕ in atTop, PaidHeight (a:=a) (b:=b) (i:=i) (k:=k) Y H s q := by
  let X:= (4*(P.block.val:ℝ))^4
  let q:= (Papal.sealPrice P.V P.W-0)+ Py.Rate.Pannier.blossom P.K+(A+1) -- qualify
  let M:=max (0:ℝ) q * X
  have he:M≥0:=mul_nonneg (le_max_left ..) (by unfold X; positivity)
  refine ⟨M+1,by linarith,?_⟩
  filter_upwards [Papal.measured Y p zero_le_one P.height 0] with s hs
  have hf: Tendsto (fun e=>ζ e) atTop atTop:=(V.pick.grow_k.comp Q.growsB).tendsto_atTop
  filter_upwards [((V.pick.grow_i.comp Q.growsA).tendsto_atTop.eventually hs), hf.eventually (Papal.thaw_plot Y 1 zero_lt_one s)] with x hx hX r
  let k':= ζ x; let i':=π x; let U:= solder Y i' k' r.depth s; let F:= compass Y i' k' s; let n:= N s i'
  apply carry (terrain Y H (Y.ir i') s) U
  let d:ℝ := ((momentm Y i' s).val:ℝ)^4
  apply older U (Real.exp ((M+1)*d)) (Real.exp_pos _).le (fun c f=> by unfold U solder; rw [mark_smul,mul_div_assoc])
  intro f h u
  have hv:‖U f‖≤1+ Real.exp (q*sites n):= by
    apply (norm_le_norm_sub_add (U f) (F f)).trans
    apply add_le_add
    exact (norm_sub_rev ..).trans_le ((hX _ r.depth _ _ h u).trans_eq (one_mul 1))
    exact hx _ r.depth r.enters _ 0 h (canopy Y s i' k' f u)
  have hM: q*sites n≤ M*d:= by rw [sharpSite]; change q*(X*d)≤ M*d; rw [←mul_assoc]; exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right ..) (by unfold X; positivity)) (by unfold d; positivity)
  have hd:1≤d:=one_le_pow₀ (show (1:ℝ) ≤ ((momentm Y i' s).val:ℝ) from Nat.one_le_cast.mpr (momentm Y i' s).property)
  have x:1≤ Real.exp (M*d):= Real.one_le_exp (mul_nonneg he (zero_le_one.trans hd))
  refine hv.trans ?_
  rw [add_mul M 1 d,one_mul,Real.exp_add]
  have hf: (2:ℝ) ≤ Real.exp d:= by linarith only [hd,Real.add_one_le_exp d]
  have he':= Real.exp_monotone hM
  nlinarith only [hf,x,he',mul_le_mul_of_nonneg_left hf (Real.exp_pos (M*d)).le]
end YM.CF.Buffered.Afterglow.Tower.SlabMark
#print axioms YM.CF.Buffered.Afterglow.Tower.SlabMark.heightGain
