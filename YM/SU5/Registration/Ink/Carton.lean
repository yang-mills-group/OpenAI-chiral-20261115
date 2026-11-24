/- This file incorporates modified third-party source. See the source attributions in notices/. -/ import YM.SU5.Registration.Ink.WavePort
import YM.SU5.Registration.Reconstruction
import YM.Work.C03
/-!
 General module version for the actual G in M4; adapting YM pinned contour chain.
 Adapted from  YM/Fields/Tall & YM/Work/C02, C03.
-/
set_option autoImplicit false
noncomputable section
namespace YM.SatinWFixed
open Boundary OS OS.Semigroup Set Function Filter SatinRegistration
open scoped Topology BigOperators NNReal ENNReal
open Boundary.Small
open Work.C03 (exists_lit enough_logD coe_logD lit_strict tail_lit tail_ready continuous_buffer eventually_lit)

variable {H : Hilbert} {S : OS.Semigroup H timeAxis} {V : Type*} [AddCommGroup V] [Module ℂ V] {n : ℕ}
structure Carton (S : OS.Semigroup H timeAxis) (V : Type*) [AddCommGroup V] [Module ℂ V] where
  bar (p : ℝ≥0) : V →ₗ[ℂ] H.Op
  coherent (v) : Sound S (fun p=> bar p v)
  price (v) : PadPaid (fun p=> bar p v)
  omega : H
  hot (s) : S.E s omega=omega
  size : ‖omega‖=1
  stay p : S.unit.translation p omega=omega

namespace Carton
variable (B : Carton S V)
lemma rated (v:V) : ∃ Q:ℝ, ∃ A:ℕ, 0 ≤ Q ∧ ∀ p: ℝ≥0, p ∈ Ioo (0:ℝ≥0) 1 → ‖B.bar p v‖≤ Q*(p:ℝ)⁻¹^A := by
 obtain ⟨A,Q,p,q⟩:= B.price v; refine ⟨Q,A,p,fun y ht =>?_⟩
 have h:= q y ht.1 ht.2.le; rw [inv_pow,← div_eq_mul_inv]; rw [mul_comm] at h; exact (le_div_iff₀ (pow_pos (show 0 < (y:ℝ) from ht.1) _)).2 h
lemma pad_bar {p:ℝ≥0} (hp:0<p) (u : ℝ≥0) (v:V) : B.bar (p+u) v=((S.E u).comp (B.bar p v)).comp (S.E u):= B.coherent v p hp u

def ripZ (S:OS.Semigroup H timeAxis) (w:ℂ)(t)(x : Space3) := (S.F (Small.interval w t)).comp (S.U (bufferF x))
lemma flanksZ (S : OS.Semigroup H timeAxis) (w : ℂ) (t : ℝ≥0) (x : Space3) (v:H)(h:(t:ℝ)<w.im): ‖ripZ S w t x v‖ ≤ ‖v‖:= by
  have he := (S.F (Small.interval w t)).le_opNorm (S.U (bufferF x) v)
  rw [S.unitary] at he
  exact he.trans (mul_le_of_le_one_left (norm_nonneg _) (S.norm_row ((down _ _).2 h)))
/-- product recursively of all bars after first. -/
def trainZ (p : ℝ≥0) : ∀ n, Times n → SpacePoints n → (Fin n → V) → ℂ → Space3 → H
  | 0,_,_,_,_,_ => B.omega
  | n+1,z,x,v,Z,X =>
      ripZ S (z 0-Z) (p+p) (x 0-X) ((B.bar p (v 0)) (trainZ p n (Fin.tail z) (Fin.tail x) (Fin.tail v) (z 0) (x 0)))

def matrixZ (p : ℝ≥0) : ∀ n, Times n → SpacePoints n → (Fin n → V) → ℂ
  | 0,_,_,_ => inner ℂ B.omega B.omega
  | n+1,z,x,v => inner ℂ B.omega (B.bar p (v 0) (B.trainZ p n (Fin.tail z) (Fin.tail x) (Fin.tail v) (z 0) (x 0)))


theorem pad_rip (S : OS.Semigroup H timeAxis) {z : ℂ} {p u : ℝ≥0} (hu : 0<u)
    (hz : 4*((p+u:ℝ≥0):ℝ) < z.im) (x : Space3) :
    ripZ S z (p+p) x = ((S.E u).comp (ripZ S z ((p+u)+(p+u)) x)).comp (S.E u) := by
  have ht := dur.mpr hu
  let w := Small.interval z ((p+u)+(p+u))
  have hw : w ∈ inside := (down ..).mpr (by push_cast at *; linarith [p.coe_nonneg, u.coe_nonneg])
  have hsum : duration u + w ∈ inside := show 0<(duration u).re+w.re from add_pos ht hw
  have he : Small.interval z (p+p) = duration u+w+duration u := by
    simp only [interval, duration, w, NNReal.coe_add, Complex.ofReal_add]; ring
  unfold ripZ
  rw [he, S.pairs hsum ht,
    S.pairs ht hw, S.roots_heat hu, ContinuousLinearMap.comp_assoc,
    S.independent, ← ContinuousLinearMap.comp_assoc, ContinuousLinearMap.comp_assoc (S.E u) (S.F w)]

private lemma train_pad {p u : ℝ≥0}
    (hp : 0<p) (hu : 0<u) (z : Times n) (x : SpacePoints n) (v : Fin n → V) (Z : ℂ) (X : Space3)
    (h : lit z (p+u)) (ht : ∀ i, 4*((p+u:ℝ≥0):ℝ)<(z i).im-Z.im) :
    S.E u (B.trainZ (p+u) n z x v Z X) = B.trainZ p n z x v Z X := by
  induction n generalizing Z X with
  | zero => exact B.hot u
  | succ n ih =>
    rw [trainZ, trainZ, B.pad_bar hp, pad_rip S (z:=z 0-Z) (p:=p) hu (ht 0)]
    simp only [ContinuousLinearMap.comp_apply]
    rw [ih (Fin.tail z) (Fin.tail x) (Fin.tail v) (z 0) (x 0) (tail_lit h)
      (fun j => h.2.2 0 j.succ j.succ_pos)]

private lemma matrixZ_pad {p u : ℝ≥0}
    (hp : 0<p) (hu : 0<u) (z : Times n) (x : SpacePoints n) (v : Fin n → V)
    (hz : lit z (p+u)) : B.matrixZ (p+u) n z x v = B.matrixZ p n z x v := by
  cases n with
  | zero => rfl
  | succ n =>
    rw [matrixZ, matrixZ, B.pad_bar hp]
    simp only [ContinuousLinearMap.comp_apply]
    rw [train_pad B hp hu _ _ _ _ _ (show lit (Fin.tail z) _ from tail_lit hz)
      (fun j => hz.2.2 0 j.succ j.succ_pos), ← S.swing,
      show S.E u B.omega=B.omega from B.hot u]

def Defined (F : InkWaves V) := ∀ n (z : Times n), z ∈ strict n → ∀ p, lit z p →
    ∀ x v, F.F n z x v=B.matrixZ p n z x v
lemma same {n : ℕ} {z : Times n} (x : SpacePoints n) (p : Fin n → V) (q l : ℝ≥0) (hp : z∈strict n) (h : lit z q) (hk : lit z l) :
    B.matrixZ q n z x p=B.matrixZ l n z x p := by
  obtain u|u|u := lt_trichotomy q l
  · obtain ⟨α,rfl⟩:= exists_add_of_le u.le
    exact (matrixZ_pad B h.1 (by simpa using u) z x p hk).symm
  · rw [u]
  obtain ⟨α,rfl⟩:= exists_add_of_le u.le
  exact matrixZ_pad B hk.1 (by simpa using u) z x p h
/-- Insert one bar in front of a multilinear ket. -/
def attachZ (p : ℝ≥0) (M : MultilinearMap ℂ (fun _ : Fin n => V) H.space) :
    MultilinearMap ℂ (fun _ : Fin (n+1) => V) H.space := by
  let f : V →ₗ[ℂ] MultilinearMap ℂ (fun _ : Fin n => V) H.space := {
    toFun v := (B.bar p v).toLinearMap.compMultilinearMap M
    map_add' v w := by
      ext1 u; change B.bar p (v+w) (M u) = _+_; rw [map_add]; rfl
    map_smul' c v := by
      ext1 u; change B.bar p (c•v) (M u) = c • B.bar p v (M u); rw [map_smul]; rfl
  }
  exact LinearMap.uncurryLeft f

lemma attachZ_apply (p : ℝ≥0) (M : MultilinearMap ℂ (fun _ : Fin n => V) H.space)
    (v : Fin (n+1) → V) : attachZ B p M v = B.bar p (v 0) (M (Fin.tail v)) := rfl

lemma trainZ_multi (p : ℝ≥0) (z : Times n) (x : SpacePoints n) (Z : ℂ) (X : Space3) :
    ∃ M : MultilinearMap ℂ (fun _ : Fin n => V) H.space, ∀ v, M v = B.trainZ p n z x v Z X := by
  induction n generalizing Z X with
  | zero => exact ⟨MultilinearMap.constOfIsEmpty ℂ _ B.omega,fun _ => rfl⟩
  | succ n ih =>
    obtain ⟨M,hM⟩ := ih (Fin.tail z) (Fin.tail x) (z 0) (x 0)
    let P := ripZ S (z 0-Z) (p+p) (x 0-X)
    exact ⟨P.toLinearMap.compMultilinearMap (attachZ B p M),fun v => by
      change P (attachZ B p M v) = _; rw [attachZ_apply,hM]; rfl⟩

lemma matrixZ_multi (p : ℝ≥0) (z : Times n) (x : SpacePoints n) :
    ∃ M : MultilinearMap ℂ (fun _ : Fin n => V) ℂ, ∀ v, M v = B.matrixZ p n z x v := by
  cases n with
  | zero => exact ⟨MultilinearMap.constOfIsEmpty ℂ _ (inner ℂ B.omega B.omega),fun _ => rfl⟩
  | succ n =>
    obtain ⟨M,hM⟩ := trainZ_multi B p (Fin.tail z) (Fin.tail x) (z 0) (x 0)
    exact ⟨(innerSL ℂ B.omega).toLinearMap.compMultilinearMap (attachZ B p M),fun v => by
      change inner ℂ B.omega (attachZ B p M v) = _; rw [attachZ_apply,hM]; rfl⟩

lemma ripZ_cont {D : Type*} [TopologicalSpace D] {u : D} (s : ℝ≥0)
    {z : D → ℂ} {x : D → Space3} {f : D → H}
    (hs : (s:ℝ) < (z u).im) (hz : ContinuousAt z u) (hx : ContinuousAt x u) (hf : ContinuousAt f u) :
    ContinuousAt (fun t => ripZ S (z t) s (x t) (f t)) u := by
  have hU := (S.cont_cross (T:=H.space × Cross timeAxis) Prod.fst Prod.snd continuous_fst continuous_snd).continuousAt.comp
    (hf.prodMk (continuous_buffer.continuousAt.comp hx))
  have hF := (S.localHeat _ ((down _ _).2 hs)).continuousAt
  have hI : ContinuousAt (fun t => Small.interval (z t) s) u := by
    unfold Small.interval; fun_prop
  have ha := (hF.comp (f:=fun t => Small.interval (z t) s) hI).clm_apply hU
  exact ha

lemma trainZ_cont {D : Type*} [TopologicalSpace D] {u : D} (p : ℝ≥0)
    (v : Fin n → V) (z : D → Times n) (x : D → SpacePoints n) (Z : D → ℂ) (X : D → Space3)
    (he : lit (z u) p) (ht : ∀ i, ((p+p:ℝ≥0):ℝ) < (z u i-Z u).im)
    (hz : ∀ i, ContinuousAt (fun t => z t i) u) (hx : ∀ i, ContinuousAt (fun t => x t i) u)
    (hZ : ContinuousAt Z u) (hX : ContinuousAt X u) :
    ContinuousAt (fun t => B.trainZ p n (z t) (x t) v (Z t) (X t)) u := by
  induction n generalizing Z X with
  | zero => exact continuousAt_const
  | succ n ih =>
    have hc := ih (Fin.tail v) (fun t => Fin.tail (z t)) (fun t => Fin.tail (x t)) (fun t => z t 0) (fun t => x t 0)
      (tail_lit he) (tail_ready he) (fun i => hz i.succ) (fun i => hx i.succ) (hz 0) (hx 0)
    exact ripZ_cont (p+p) (ht 0) ((hz 0).sub hZ) ((hx 0).sub hX) ((B.bar p (v 0)).continuous.continuousAt.comp hc)

lemma matrixZ_cont (v : Fin n → V) {p : ℝ≥0} {u : Times n × SpacePoints n} (he : lit u.1 p) :
    ContinuousAt (fun t : Times n × SpacePoints n => B.matrixZ p n t.1 t.2 v) u := by
  cases n with
  | zero => exact continuousAt_const
  | succ n =>
    have hc := trainZ_cont B p (Fin.tail v) (u:=u) (fun t => Fin.tail t.1) (fun t => Fin.tail t.2)
      (fun t => t.1 0) (fun t => t.2 0) (tail_lit he) (tail_ready he)
      (fun i => (continuous_apply i.succ |>.comp continuous_fst).continuousAt)
      (fun i => (continuous_apply i.succ |>.comp continuous_snd).continuousAt) (by fun_prop) (by fun_prop)
    exact (innerSL ℂ B.omega).continuous.continuousAt.comp ((B.bar p (v 0)).continuous.continuousAt.comp hc)

lemma ripZ_diff {D : Type*} [NormedAddCommGroup D] [NormedSpace ℂ D] {u : D} (s : ℝ≥0) (x : Space3)
    {z : D → ℂ} {f : D → H} (hs : (s:ℝ) < (z u).im)
    (hz : DifferentiableAt ℂ z u) (hf : DifferentiableAt ℂ f u) :
    DifferentiableAt ℂ (fun t => ripZ S (z t) s x (f t)) u := by
  have hU := (S.U (bufferF x)).differentiableAt.comp u hf
  have hF := (S.localHeat _ ((down _ _).2 hs)).differentiableAt
  have hI : DifferentiableAt ℂ (fun t => Small.interval (z t) s) u := by
    unfold Small.interval; fun_prop
  have ha := (hF.comp u hI).clm_apply hU
  exact ha

lemma trainZ_diff {D : Type*} [NormedAddCommGroup D] [NormedSpace ℂ D] {u : D} (p : ℝ≥0)
    (v : Fin n → V) (z : D → Times n) (x : SpacePoints n) (Z : D → ℂ) (X : Space3)
    (he : lit (z u) p) (ht : ∀ i, ((p+p:ℝ≥0):ℝ) < (z u i-Z u).im)
    (hz : ∀ i, DifferentiableAt ℂ (fun t => z t i) u) (hZ : DifferentiableAt ℂ Z u) :
    DifferentiableAt ℂ (fun t => B.trainZ p n (z t) x v (Z t) X) u := by
  induction n generalizing Z X with
  | zero => exact differentiableAt_const _
  | succ n ih =>
    have hd := ih (Fin.tail v) (fun t => Fin.tail (z t)) (Fin.tail x) (fun t => z t 0) (x 0)
      (tail_lit he) (tail_ready he) (fun i => hz i.succ) (hz 0)
    exact ripZ_diff (p+p) (x 0-X) (ht 0) ((hz 0).sub hZ) ((B.bar p (v 0)).differentiableAt.comp u hd)

lemma matrixZ_diff (v : Fin n → V) (x : SpacePoints n) {p : ℝ≥0} {u : Times n} (he : lit u p) :
    DifferentiableAt ℂ (fun t => B.matrixZ p n t x v) u := by
  cases n with
  | zero => exact differentiableAt_const _
  | succ n =>
    have hd := trainZ_diff B p (Fin.tail v) Fin.tail (Fin.tail x) (fun t : Times _ => t 0) (x 0)
      (tail_lit he) (tail_ready he) (fun i => by change DifferentiableAt ℂ (fun t : Times _ => t i.succ) _; fun_prop)
      (by fun_prop)
    exact (innerSL ℂ B.omega).differentiableAt.comp u ((B.bar p (v 0)).differentiableAt.comp u hd)

lemma norm_trainZ (p : ℝ≥0) (v : Fin n → V) (z : Times n) (x : SpacePoints n) (Z : ℂ) (X : Space3)
    (he : lit z p) (ht : ∀ i, ((p+p:ℝ≥0):ℝ) < (z i-Z).im) :
    ‖B.trainZ p n z x v Z X‖ ≤ (∏ i, ‖B.bar p (v i)‖) * ‖B.omega‖ := by
  induction n generalizing Z X with
  | zero => simp [trainZ]
  | succ n ih =>
    have hn := ih (Fin.tail v) (Fin.tail z) (Fin.tail x) (z 0) (x 0) (tail_lit he) (tail_ready he)
    rw [Fin.prod_univ_succ,mul_assoc]
    exact (flanksZ S _ _ _ _ (ht 0)).trans (((B.bar p (v 0)).le_opNorm _).trans
      (mul_le_mul_of_nonneg_left hn (norm_nonneg _)))

lemma norm_matrixZ (p : ℝ≥0) (v : Fin n → V) (z : Times n) (x : SpacePoints n) (he : lit z p) :
    ‖B.matrixZ p n z x v‖ ≤ ‖B.omega‖ * ((∏ i, ‖B.bar p (v i)‖) * ‖B.omega‖) := by
  cases n with
  | zero => simpa [matrixZ] using (norm_inner_le_norm B.omega B.omega (𝕜:=ℂ))
  | succ n =>
    have hn := norm_trainZ B p (Fin.tail v) (Fin.tail z) (Fin.tail x) (z 0) (x 0) (tail_lit he) (tail_ready he)
    rw [Fin.prod_univ_succ,mul_assoc ‖B.bar p (v 0)‖]
    exact (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left (((B.bar p (v 0)).le_opNorm _).trans
      (mul_le_mul_of_nonneg_left hn (norm_nonneg _))) (norm_nonneg B.omega))

lemma defined_power {F : InkWaves V} (hF : B.Defined F) : F.Breathes := by
  intro n v
  choose Q d hQ h using fun i => B.rated (v i)
  let P (i : Fin n) := Q i * 8^d i
  have hP i : 0 ≤ P i := by have := hQ i; unfold P; positivity
  have hn := Finset.prod_nonneg (s:=Finset.univ) (fun i _ => hP i)
  refine ⟨∑ i, d i, ‖B.omega‖ * ((∏ i, P i) * ‖B.omega‖), by positivity, fun y k hk hb x => ?_⟩
  let p := logD k
  have hp : Small.enough y p := enough_logD hk hb
  have he : lit (Boundary.shift x y) p := by simpa [lit,Boundary.shift] using hp
  have hi i : ‖B.bar p (v i)‖ ≤ P i * k⁻¹^d i := by
    apply (h i p ⟨hp.1,hp.2.1⟩).trans_eq
    unfold p P; rw [coe_logD hk,inv_div,div_eq_mul_inv,mul_pow,mul_assoc]
  calc ‖F.restricted v y x‖ = ‖B.matrixZ p n (Boundary.shift x y) (trace x) v‖ := by rw [InkWaves.restricted, hF n _ (lit_strict he) p he]
       _ ≤ ‖B.omega‖ * ((∏ i, ‖B.bar p (v i)‖) * ‖B.omega‖) := norm_matrixZ B p v _ _ he
       _ ≤ ‖B.omega‖ * ((∏ i, (P i * k⁻¹^d i)) * ‖B.omega‖) := by gcongr with i; exact hi i
       _ = _ := by rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]; ring

lemma defined_exists : ∃ F : InkWaves V, B.Defined F := by
  classical
  let F : InkWaves V := {
    F n z x := if h : z ∈ strict n then (matrixZ_multi B (exists_lit h).choose z x).choose else 0
  }
  refine ⟨F, fun n z hz p hp x v => ?_⟩
  change (if h : z ∈ strict n then (matrixZ_multi B (exists_lit h).choose z x).choose else 0) v = _
  rw [dif_pos hz, (matrixZ_multi B _ z x).choose_spec]
  exact B.same x v _ p hz (exists_lit hz).choose_spec hp

lemma defined_region {F : InkWaves V} (hF : B.Defined F) : F.Region := by
  refine ⟨fun n v u hu => ?_,fun n v x u hu => ?_⟩
  · obtain ⟨p,hp⟩ := exists_lit hu.1
    apply ContinuousAt.continuousWithinAt
    apply (matrixZ_cont B v hp).congr_of_eventuallyEq
    filter_upwards [(continuous_fst.tendsto u).eventually (eventually_lit hp)] with t ht using
      hF n _ (lit_strict ht) p ht t.2 v
  · obtain ⟨p,hp⟩ := exists_lit hu
    exact ((matrixZ_diff B v x hp).congr_of_eventuallyEq ((eventually_lit hp).mono (fun t ht =>
      hF n t (lit_strict ht) p ht x v))).differentiableWithinAt
end Carton
end YM.SatinWFixed
