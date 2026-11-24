import ExactRunning.Dyne.Melody

/-!
# Longitudinal constraints on thermodynamic cross entries

The slab gauge invariance suffices: in particular, transversality
at the **origin** can be used on directions in the plane of the test,
through curves attaining the origin. (No assertion like analytic
continuation to all four external momenta is needed.)
-/

set_option linter.unusedSectionVars false
noncomputable section
namespace ExactRunning
open YM Stationary Lattice Laurent Bloch RG
open Function Filter Finset Matrix
open scoped BigOperators ContDiff Topology ComplexConjugate Matrix

open Exterior Wilson Precision
open Tree

set_option synthInstance.maxSize 1024

open Pairing

variable {G : Gauge} {E I : Pylon G} {m L : Side} {X : BlockTie E I}
variable {ι : Type} [Fintype ι] [DecidableEq ι]

variable {D : Latitude} {K : Kin ι} {p : Momentum} {g : ℝ → Momentum}
variable {A : Phase (Entry G) →ₗ[ℂ] Phase ι}

/-- Gauge invisibility in either slot, for a given type of external leg. -/
def Lateral (D : Latitude) (K : Kin ι) (A : Phase (Entry G) →ₗ[ℂ] Phase ι) :=
  ∀ {g}, Ode D g → ∀ t v u,
   (v ⬝ᵥ K (g t) *ᵥ A (pageD G 0 (g t) *ᵥ u) = 0) ∧
   (A (pageD G 0 (-g t) *ᵥ u) ⬝ᵥ K (g t) *ᵥ v = 0)

lemma Latitude.extend_bilin {α : Type} [Fintype α] [DecidableEq α]
    (B : Phase (Co m α) →ₗ[ℂ] Phase (Co m ι) →ₗ[ℂ] ℂ)
    (h : ∀ v, D.repeats v → ∀ u, B (axes v) (axes u)=0) {v} (hv : D.repeats v)
    (x) : B v x=0 := by
  refine D.extend (p:=(B.flip x)) (q:=fun _=>0)
    (by intro;intros; simp) (by intro;intros;simp) (fun u hu => ?_) hv
  change B (axes u) x=0
  rw [←parts x,map_add,map_smul,h u hu,h u hu]; simp

private lemma read_lane {b : Site m} {f : Corn (Co m ι) → ℝ}
    {L : Link G m →L[ℝ] Corn (Co m ι)}
    (h : Turns (fun _=>A) L)
    (hv : ∀z, D.repeats z → Vanishes f (L (gradientA G m z)))
    (hp : rolls (mon b) p) (hd : D.quiet p) (u) (x : Phase (Co m ι)) :
    let y := tune b (A (pageD G 0 p *ᵥ u))
    beat f 0 2 ![y,x]=0 ∧ beat f 0 2 ![x,y]=0 := by
  obtain ⟨T,H,C⟩ := h.basis
  let Y := T.comp (Matrix.toLin' (approached (patron G (d 0 m))))
  have he : Y (tune b u)=tune b (A (pageD G 0 p *ᵥ u)) := by
    rw [show Y (tune b u)=_ from congr_arg T (page_read m 0 b p hp u),add_zero,C b p hp]
  have ha z : Y (axes z)=axes (L (gradientA G m z)) := by
    dsimp only [Y,LinearMap.comp_apply];rw [Matrix.toLin'_apply,prom_vec,patron_fee,H,first_uniform]
  dsimp only
  rw [←he]
  have hb := Latitude.repeats.wave (hd.rolls hp.symm) u
  constructor
  · refine Latitude.extend_bilin ((beatL f).comp Y) (fun v h w=>?_) hb x
    change beat f 0 2 ![Y (axes v),axes w]=0
    rw [ha,beat_axes, ← Work.F05.bend_apply, (hv _ h w).1, Complex.ofReal_zero]
  refine Latitude.extend_bilin ((beatL f).flip.comp Y) (fun v h w=>?_) hb x
  change beat f 0 2 ![axes w,Y (axes v)]=0
  rw [ha,beat_axes, ← Work.F05.bend_apply,(hv _ h w).2, Complex.ofReal_zero]

theorem Playing.lateral {lo : ℕ} {U : Law ι} (h : Playing D U K)
    {L : (m : Side) → Link G m →L[ℝ] Corn (Co m ι)}
    (turn : ∀m, lo ≤ m.val → Turns (fun _=>A) (L m))
    (ward : ∀m, lo ≤ m.val → ∀ z, D.repeats z → Vanishes (U m) (L m (gradientA G m z))) :
    Lateral D K A := by
  intro g hg t v u
  have val {j} (ho : Ode D j) :
      ContDiff ℝ 2 (fun t => A (pageD G 0 (j t) *ᵥ u)) :=
    (A.toContinuousLinearMap.restrictScalars ℝ).contDiff.comp (𝕜:=ℝ)
      (Play.smmul (ode_poster (page_linen _) zero_lt_one ho) contDiff_const)
  constructor
  · refine congr_fun (Radian.equalizer (Score.val h.score hg contDiff_const (val hg)).continuous
        continuous_const ?_) t
    intro q hq
    obtain ⟨a⟩ := hg.pitch hq lo
    refine tendsto_nhds_unique
      ((h.waves (hg.quiet q) a v (A (pageD G 0 (g q) *ᵥ u))).congr (f₂:=fun _=>0) ?_) tendsto_const_nhds
    intro n
    rw [(read_lane (turn _ (a.large n)) (ward _ (a.large n)) (a.hits n) (hg.quiet _) _ _).2,mul_zero]
  refine congr_fun (Radian.equalizer (Score.val h.score hg (val hg.neg) contDiff_const).continuous
      continuous_const ?_) t
  intro q hq
  obtain ⟨a⟩ := hg.pitch hq lo
  refine tendsto_nhds_unique
      ((h.waves (hg.quiet q) a (A (pageD G 0 (-g q) *ᵥ u)) v).congr (f₂:=fun _=>0) ?_) tendsto_const_nhds
  intro n
  rw [(read_lane (turn _ (a.large n)) (ward _ (a.large n))
      (a.hits n).flip_sign (hg.quiet _).neg _ _).1,mul_zero]

lemma turns_id (m : Side) (ι : Type) [Fintype ι] :
    Turns (fun _=> LinearMap.id (R:=ℂ) (M:=Phase ι)) (ContinuousLinearMap.id ℝ (Corn (Co m ι))) :=
  ⟨LinearMap.id,fun _=>rfl,fun _ _ _ _=>rfl⟩

theorem Playing.ground {K : Kin (Entry G)} {U} (h : Playing D U K)
    (guard : ∀m, Magnet D (U m)) :
    Lateral D K LinearMap.id :=
  h.lateral (lo:=0) (fun _ _=> turns_id _ _) (fun _ _ => (guard _).loyal)

def Inert (K : Kin ι) (p : Momentum) (x y : Phase ι) : Prop :=
  ∀ v, x ⬝ᵥ K p *ᵥ v = 0 ∧ v ⬝ᵥ K p *ᵥ y = 0

lemma Lateral.hit (h : Lateral D K A) (i : Ode D g) (t) (u z) :
    Inert K (g t) (A (pageD G 0 (-g t) *ᵥ u)) (A (pageD G 0 (g t) *ᵥ z)) :=
  fun v => ⟨(h i t v u).2,(h i t v z).1⟩

def arrow (a : Axis) (i : G.ColorIndex) : Phase (Entry G) :=
  Pi.single (coord a,i) 1

private lemma sharp {t : ℝ} (h : t≠0) (g : |t| ≤ Real.pi)
   (a : Axis) (i : G.ColorIndex) :
   ∃ v, arrow a i=pageD G 0 (tilt a t) *ᵥ v := by
  have hw : q (tilt a t) a ≠ 0 := by
    intro e
    rw [q,tilt_pick,sub_eq_zero,Complex.exp_eq_one_iff] at e
    obtain ⟨n,hn⟩ := e
    have he := (wrapDist_eq_zero (u:=t)).mpr ⟨n,by
      simp [Complex.ext_iff,Complex.mul_im] at hn
      rw [hn];ring⟩
    rw [wrapDist_eq g,abs_eq_zero] at he; exact h he
  refine ⟨Pi.single (vac,i) (q (tilt a t) a)⁻¹, ?_⟩
  rw [Matrix.mulVec_single]
  funext ⟨j,l⟩
  obtain ⟨b,rfl⟩ := axisEquiv.surjective j
  simp only [arrow,Pi.single_apply, pageD, tintedLocal, coord_map]
  by_cases hh : a=b
  · subst b
    by_cases k : l=i <;> simp [k,sym_one,hw]
  have hn : coord b≠coord a := fun e => hh (axisEquiv.injective e.symm)
  simp [hn,sym_one,q,tilt_off hh]

theorem Lateral.axis (h : Lateral D K A) (s : Score D K) {a : Axis} (ha : a≠3)
    (i : G.ColorIndex) {t : ℝ} (he : |t|≤Real.pi) :
    Inert K (tilt a t) (A (arrow a i)) (A (arrow a i)) := by
  have hh {t : ℝ} (he : |t| ≤ Real.pi) (ht : t≠0) :
      Inert K (tilt a t) (A (arrow a i)) (A (arrow a i)) := by
    obtain ⟨u,hu⟩ := sharp (neg_ne_zero.mpr ht) (by rwa [abs_neg]) a i
    obtain ⟨w,hw⟩ := sharp ht he a i
    rw [tilt_neg] at hu
    convert h.hit (Ode.axis D ha) t u w using 2
  by_cases ht : t≠0
  · exact hh he ht
  simp only [ne_eq,not_not] at ht; subst t
  intro v
  let x := A (arrow a i)
  have hx : ∀ᶠ t : ℝ in 𝓝[>] 0, Inert K (tilt a t) x x := by
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (gt_mem_nhds Real.pi_pos)] with t hp hg
    exact hh (by rw [abs_of_pos hp]; exact hg.le) (ne_of_gt hp)
  have hc u w := (Score.val s (Ode.axis D ha) (contDiff_const (c:=u))
    (contDiff_const (c:=w))).continuous.continuousWithinAt (x:=0) (s:=Set.Ioi 0)
  exact ⟨tendsto_nhds_unique (hc x v) (tendsto_const_nhds.congr' (hx.mono fun _ h => (h v).1.symm)),
    tendsto_nhds_unique (hc v x) (tendsto_const_nhds.congr' (hx.mono fun _ h => (h v).2.symm))⟩

lemma Lateral.zero (h : Lateral D K A) (s : Score D K) (i : G.ColorIndex) :
    Inert K 0 (A (Pi.single (stripe i) 1)) (A (Pi.single (stripe i) 1)) := by
  rw [← tilt_zero 1]
  exact h.axis s (by decide : (1:Axis)≠3) i (by simpa using Real.pi_pos.le)

end ExactRunning
