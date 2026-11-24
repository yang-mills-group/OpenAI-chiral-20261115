import YM.SU5.FiniteGaugeData.Dally.Clipso
import Mathlib.Analysis.Analytic.IsolatedZeros
/-!
 # The longitude argument
 -/
noncomputable section
open Metric Filter Function WithLp Set
open scoped Topology NNReal ENNReal InnerProductSpace
set_option autoImplicit false
namespace YM.CF.Buffered.Afterglow.Hierarchy.Seld.Poin.Galleon.Dai
open _root_.YM Dally Gem Leal Leal.Breve Celeritas Land Mist OS OS.Semigroup Flute Apso Mink
variable {K : Axis → Hilbert} (W : ∀ i : Axis, OS.Semigroup (K i) i)
    {ι : Type} (G : Canopy (K timeAxis) ι) (ω : ∀ i, (K i).space) (A : Tribe G)
variable {n : ℕ} (u : Fin n → ι) (w : Palette G u)
variable (b : SpaceAxis) (x : Points n) (t s : ℝ)
attribute [local instance] ostensible
local notation "ₜ" => timeAxis
local notation "p₀" => Palette G u
local notation "m₀" => Sale W G ω A u

lemma cruise (a : SpaceAxis) (p : a≠b) (hx : capable a.castSucc x) : capable a.castSucc (wheelR b x t) := by
  have T : clockV a.castSucc (wheelR b x t)=clockV a.castSucc x := funext fun i => warpQ b a t (x i) p
  rw [capable,T]; exact hx
lemma Capri (hx : longitude x) : ∀ᶠ u in 𝓝[≠] t, longitude (wheelR b x u) := by
  suffices he : ∀ᶠ u in 𝓝[≠] t, ∀ (a:Axis)(i j:Fin n), i≠j →
      (wheelR b x u) i a ≠ (wheelR b x u) j a by
    filter_upwards [he] with u h using fun a i j v => by_contra fun w=> h a i j w v
  refine eventually_all.mpr fun a => eventually_all.mpr fun i => eventually_all.mpr fun j => ?_
  by_cases h : i=j
  · exact Eventually.of_forall fun _ v => False.elim (v h)
  let f (i : Fin n) (z : ℝ) := (wheelR b x z) i a
  have F (i z) : AnalyticAt ℝ (f i) z := by
    let p := PiLp.proj (p:=2) (β:=fun _ : Axis => ℝ) (𝕜:=ℝ) a
    let q := PiLp.proj (p:=2) (β:=fun _ : Fin n => E4) (𝕜:=ℝ) i
    exact ((p.comp q).analyticAt _).comp (engineC b x z)
  rcases (F i t).eventually_eq_or_eventually_ne (F j t) with he|he
  · have E := AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq (fun z (_:z∈ Set.univ) => F i z)
      (fun z _ => F j z) isPreconnected_univ (mem_univ _) he (mem_univ 0)
    exfalso; apply ((hx a).ne h); simpa only [f,capable,clockV,wheel_zero] using E
  exact he.mono fun u v _ => v

private lemma agree (t s : ℝ) (u : ℝ → ℂ) (h : t<s) (H : Continuous u) (v : ∀ i ∈ Ioo t s, HasDerivAt u 0 i) : u t=u s := by
  have A (L : ℂ→L[ℝ]ℝ) : L (u t)=L (u s) := by
    obtain ⟨i,_,q⟩ := exists_hasDerivAt_eq_slope (L ∘ u) (fun _=>0) h (L.continuous.comp H).continuousOn
      fun i hi => by simpa using L.hasFDerivAt.comp_hasDerivAt i (v i hi)
    exact (sub_eq_zero.mp ((div_eq_zero_iff.mp q.symm).resolve_right (sub_pos.mpr h).ne')).symm
  exact Complex.ext (A Complex.reCLM) (A Complex.imCLM)
private lemma fill (u : ℝ → ℂ) (h : Continuous u) (H : ∀ t, ∀ᶠ v in 𝓝[≠] t, HasDerivAt u 0 v) : HasDerivAt u 0 t := by
  have p : ∀ᶠ v in 𝓝 t, v≠t → HasDerivAt u 0 v := eventually_nhdsWithin_iff.mp (H t)
  obtain ⟨r,hr,R⟩ := nhds_basis_ball.eventually_iff.mp p
  refine (hasDerivAt_const t (u t)).congr_of_eventuallyEq ?_
  filter_upwards [ball_mem_nhds t hr] with z hz
  rw [Real.ball_eq_Ioo] at hz; obtain ⟨a,b⟩:=hz; rcases lt_trichotomy z t with v|v|v
  · refine agree z t u v h fun i ⟨l,q⟩ => R (by rw [Real.ball_eq_Ioo]; exact ⟨lt_trans a l,by linarith⟩) q.ne
  · rw [v]
  exact (agree t z u v h fun i ⟨l,q⟩ => R (by rw [Real.ball_eq_Ioo]; exact ⟨by linarith,lt_trans q b⟩) l.ne').symm
variable {U : Set (Shrine K)} (hp : ∀ a b,b ≠ a → Philos (σ:=Fin n) W ω a b U)
    (hc : ∀ i, saucer (W i) (ω i)=ω i) (g : Stamp W G A U) (ha : longitude x) (Z : Grace W G ω A)
include hp hc g Z ha
lemma clutch (H : capable ₜ (wheelR b x t)) :
    ticket W G ω A ₜ x u w = m₀ (sojourn G u w b x t) := by
  obtain ⟨j,h⟩ := exists_ne b; let a : Axis := j.castSucc
  let d := sojourn G u w b x; let F (p : Points n × Palette G u) := ticket W G ω A a p.1 u p.2
  let f := F ∘ d
  have Θ (z : ℝ) : capable a (d z).1 := cruise b x z j h (ha a)
  have η (z : ℝ) : AnalyticAt ℝ d z := (engineC b x z).prod (engineP G u w b z)
  have Wv z (H : capable ₜ (d z).1) : f z=m₀ (d z) := purse W G ω A a _ _ u _ hp hc g (Θ z) H
  have Λ : Continuous f := continuous_iff_continuousAt.mpr fun i=> (dock W G ω A _ _ u (d i).2 (Θ i)).comp (f:=d) (η i).continuousAt
  have P (s : ℝ) (v : longitude (d s).1) : HasDerivAt f 0 s := by
    let x' := wheelR b x s; let w' := vane G u w b s
    let f' := m₀ ∘ sojourn G u w' b x'; have he : HasDerivAt f' 0 (s-s) := by rw [sub_self, ← Z n x' v u w' b]; exact rollout W G ω A u w' b x' (hp ₜ) hc g v
    apply (he.comp_sub_const ..).congr_of_eventuallyEq
    have E : ∀ᶠ z in 𝓝 s, capable ₜ (d z).1 := (show ContinuousAt (fun z=> (d z).1) s from (η s).continuousAt.fst).eventually
      ((capable_open ₜ n).mem_nhds (v ₜ))
    filter_upwards [E] with z hz
    rw [Wv z hz]; simp only [f',d,Function.comp_def,sojourn,x',w',wheel_more,vane_more,sub_add_cancel]
  have Q (i : ℝ) : HasDerivAt f 0 i := fill i f Λ fun t => (Capri b x t ha).mono P
  have hn : capable ₜ (d 0).1 := by rw [show d 0=(x,w) from sojourn_root ..]; exact ha ₜ
  have hq : ticket W G ω A ₜ x u w=m₀ (d 0) := by rw [show d 0=(x,w) from sojourn_root ..]
  exact hq.trans ((Wv 0 hn).symm.trans ((is_const_of_deriv_eq_zero (fun i=> (Q i).differentiableAt) (fun i=> (Q i).deriv) 0 t).trans (Wv t H)))
#print axioms clutch
omit hp hc g Z ha
lemma longitude_dense (n : ℕ) : Dense {x : Points n | longitude x} := by
  intro x
  let p : Points n := points fun i => toLp 2 (fun _ => (↑i.val : ℝ))
  let z (t : ℝ) := x + t • p
  have R : Tendsto z (𝓝[≠] 0) (𝓝 x) := ((show Continuous z by unfold z; fun_prop).tendsto' 0 x (by simp [z])).mono_left nhdsWithin_le_nhds
  apply mem_closure_of_tendsto R
  refine eventually_all.mpr fun a => ?_
  suffices H : ∀ᶠ t : ℝ in 𝓝[≠] 0, ∀ i j : Fin n, i≠j → (z t i) a ≠ z t j a from
    H.mono fun t h i j v => by_contra fun q => h i j q v
  refine eventually_all.mpr fun i => eventually_all.mpr fun j => ?_
  by_cases h : x i a = x j a
  · filter_upwards [self_mem_nhdsWithin] with t ht v
    change x i a + t * ↑i.val ≠ x j a + t * ↑j.val
    have ht' : t≠0 := ht
    rw [h]; intro P; exact v (Fin.ext <| Nat.cast_injective (R:=ℝ) (mul_left_cancel₀ ht' (add_left_cancel P)))
  filter_upwards [R.eventually ((isOpen_ne_fun (by fun_prop : Continuous (fun x : Points n => x i a))
    (by fun_prop : Continuous (fun x : Points n => x j a))).mem_nhds h)] with t v using fun _ => v

def Departure (R : SO) : (Points n) ≃ₜ (Points n) where
  toFun x := cruze x R
  invFun x := cruze x R⁻¹
  left_inv _ := by simp
  right_inv _ := by simp
  continuous_toFun := stale R
  continuous_invFun := stale _
-- prune extra dependencies? test
variable (R : SO)
def Pearl (n : ℕ) (R : SO) : Prop :=
  ∀ x : Points n, capable ₜ x → capable ₜ (cruze x R) → ∀ u w,
    ticket W G ω A ₜ x u w=ticket W G ω A ₜ (cruze x R) u (staff G u w R)
lemma raise (n : ℕ) {D : Set (Points n)} (T : Dense D)
    (H : ∀ x ∈ D, capable ₜ x → capable ₜ (cruze x R) → ∀ u w,
      ticket W G ω A ₜ x u w=ticket W G ω A ₜ (cruze x R) u (staff G u w R)) : Pearl W G ω A n R := by
  intro x hx hK u w
  let K := Departure (n:=n) R; let w' := staff G u w R
  let f (w : Palette G u) (p : Points n) := ticket W G ω A ₜ p u w
  have hc (w) (p : Points n) (hp : capable ₜ p) : ContinuousAt (f w) p := (dock W G ω A ₜ p u w hp).comp (f:=fun y => (y,w)) (continuousAt_id.prodMk continuousAt_const)
  apply tendsto_nhds_unique_of_frequently_eq (hc w x hx).tendsto ((hc w' (K x) hK).comp (f:=K) (K.continuous.continuousAt)).tendsto
  exact (((mem_closure_iff_frequently.mp (T x)).and_eventually
    (show ∀ᶠ y in 𝓝 x, capable ₜ y ∧ capable ₜ (K y) from (Eventually.and ((capable_open ₜ n).mem_nhds hx)
      (K.continuous.continuousAt.eventually ((capable_open ₜ n).mem_nhds hK))))).mono fun y ⟨d,v,p⟩ => H y d v p u w)
include hp hc g Z
-- all-axes agreement used crucially!
lemma imperial : Pearl W G ω A n R := by
  have P:= sheen R; induction P with
  | one => intro x hx _ u w; simp
  | turn i t =>
    exact raise W G ω A (Rho i t) n (longitude_dense n) fun x a _ hx u w =>
      clutch W G ω A u w i x t hp hc g a Z hx
  | chain R S P Q H K =>
    refine raise W G ω A (R*S) n ((longitude_dense n).preimage (Departure (n:=n) S).isOpenMap) ?_
    intro x xR hx hxT u w
    have M : longitude (cruze x S):= xR
    rw [K x hx (M ₜ), H (cruze x S) (M ₜ) (by rw [cruze_more]; exact hxT), cruze_more, staff_more]
omit hp
variable (Pe : ∀ (n : ℕ) a b, b ≠ a → Philos (σ:=Fin n) W ω a b U)
include Pe
lemma gybe : Gem.RotReal W G ω A := by
  constructor; intro n x f s L M p q H V ε ε0
  let u := fun i => (f i).fst; let w : Palette G u := fun i => (f i).snd; let y := cruze x s
  have v : chart timeAxis y M := ⟨q,V⟩
  have hx : chart timeAxis x L := ⟨p,H⟩
  have u' : f = sailK G u w := rfl
  have P := imperial W G ω A (Pe n) hc g Z s
  rw [u', ← portStaff G u w s, show turnO s.val x=y from rfl]
  change dist (weigh W G ω A timeAxis x L u w) (weigh W G ω A timeAxis y M u (staff G u w s)) ≤ ε
  rw [← honor W G ω A _ _ _ _ _ hx, ← honor W G ω A _ _ _ _ _ v,
    P x ((capable_iff _ _).2 ⟨L,hx⟩) ((capable_iff _ _).2 ⟨M,v⟩) u w]
  rw [dist_self]; exact ε0.le
#print axioms gybe
omit Z Pe hc g in
lemma sleet (B : Gem.RotReal W G ω A) : Pearl W G ω A n R := by
  intro x hx hy u w
  obtain ⟨L,H⟩ := (capable_iff _ _).1 hx
  obtain ⟨M,P⟩ := (capable_iff _ _).1 hy
  rw [honor W G ω A _ _ _ _ _ H,honor W G ω A _ _ _ _ _ P, ← dist_le_zero]
  apply le_of_forall_pos_le_add
  intro ε p
  rw [zero_add]
  exact B.ink n x (sailK G u w) R L M H.1 P.1 H.2 P.2 ε p
omit Z
lemma ease (p : Gem.RotReal W G ω A) : Grace W G ω A := by
  intro n x h u w b
  let F := Sale W G ω A u; let G' := sojourn G u w b x
  have hk := rollout W G ω A u w b x (Pe n ₜ) hc g h
  refine hk.unique ((hasDerivAt_const (0:ℝ) (F (x,w))).congr_of_eventuallyEq ?_)
  filter_upwards [(show ∀ᶠ t in 𝓝 (0:ℝ), longitude (wheelR b x t) from
    (engineC b x 0).continuousAt.eventually ((longitude_open n).mem_nhds
      (show longitude (wheelR b x 0) from by rw [wheel_zero]; exact h)))] with t ht using
    (sleet W G ω A (Rho b t) p x (h _) (ht _) u w).symm
-- Equivalence, no estimates yet paid beyond real stamp and packing. τ,D subtraction.
lemma altar (Δ η : ℝ) (hr : 0 < η) (τ : ℕ → ℝ) (S : ∀ n, Set (Points n))
    (ht : ∀ᶠ i in atTop, 0 < τ i) (hy : Tendsto τ atTop (𝓝 0)) (hS : ∀ n, Dense (S n)) :
    Rookie W G ω A Δ η τ S ↔ Gem.RotReal W G ω A :=
  (catalysis W G ω A Δ η τ S (fun n => Pe n ₜ) hc g ht hy hS hr).trans
    ⟨fun H => gybe W G ω A hc g H Pe, ease W G ω A hc g Pe⟩
#print axioms altar
end YM.CF.Buffered.Afterglow.Hierarchy.Seld.Poin.Galleon.Dai
