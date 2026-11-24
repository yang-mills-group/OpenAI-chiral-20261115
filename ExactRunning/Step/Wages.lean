import ExactRunning.Step.Fleets

/-!
# Ward lemmas

Differentiate the covariance laws for gauge parameters fixed by
the fourth-direction translation. `ep_magnet` for an endpoint,
`z_fine` and `z_coarse` for the full joint cost; clean off-shell
identities for independent backgrounds. `z_flat`, `h_flat`
zero first derivatives by color symmetry.
-/

set_option linter.unusedSectionVars false
noncomputable section
namespace ExactRunning
open YM Stationary Lattice Laurent Bloch RG
open Function Filter Finset Matrix
open scoped BigOperators ContDiff Topology ComplexConjugate Matrix

open Exterior Wilson Precision
open Tree


variable {K Y : Type} [NormedAddCommGroup K] [NormedSpace ℝ K] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
variable {f : K → ℝ}

structure Flat (f : K→ℝ) : Prop where
  smooth : ContDiffAt ℝ ω f 0
  df : fderiv ℝ f 0=0

/-- Tangent ward. Either slot. -/
def Vanishes (f : K→ℝ) (x : K) : Prop :=
  ∀ y, Work.F05.bend f 0 x y=0 ∧ Work.F05.bend f 0 y x=0

lemma Vanishes.sub {x z : K} (h : Vanishes f x) (p : Vanishes f z) : Vanishes f (x-z) :=
  fun y=> by simp [map_sub,(h y).1,(h y).2,(p y).1,(p y).2,LinearMap.sub_apply]

lemma Vanishes.neg {x : K} (h : Vanishes f x) : Vanishes f (-x) := fun y=> by
  simp [map_neg,(h y).1,(h y).2]

lemma Flat.bend (h : Flat f) {u : Y → K} (hb : ContDiffAt ℝ ω u 0) (ho : u 0=0) (x y : Y) :
    Work.F05.bend (f ∘ u) 0 x y =
      Work.F05.bend f 0 (fderiv ℝ u 0 x) (fderiv ℝ u 0 y) := by
  rw [Work.F05.bend_comp_stationary (ho.symm ▸ h.smooth) hb (by rw [ho,h.df]),ho]
  rfl

/-- Infinitesimal covariance from a family of germ equalities. -/
lemma guard (h : Flat f) {H : ℝ × K → K} {W : ℝ → K} {x : K}
    (hs : ContDiffAt ℝ ω H 0)
    (orig : (fun y => H (0,y)) =ᶠ[𝓝 0] id)
    (axis : (fun v:ℝ => H (v,0))=ᶠ[𝓝 0] W)
    (hw : HasDerivAt W x 0)
    (hsym : f ∘ H =ᶠ[𝓝 0] f ∘ Prod.snd) : Vanishes f x := by
  have ho : H 0=0 := orig.self_of_nhds
  let R := ContinuousLinearMap.inl ℝ ℝ K
  let S := ContinuousLinearMap.inr ℝ ℝ K
  have hh : fderiv ℝ H 0 (1,0)=x := by
    have he : HasFDerivAt H (fderiv ℝ H 0) (R 0) := by rw [map_zero];exact (hs.differentiableAt (by simp)).hasFDerivAt
    exact (he.comp_hasDerivAt 0 R.hasFDerivAt.hasDerivAt).unique (hw.congr_of_eventuallyEq axis)
  intro y
  have ht : fderiv ℝ H 0 (0,y) = y := by
    have he : HasFDerivAt H (fderiv ℝ H 0) (S 0) := by rw [map_zero];exact (hs.differentiableAt (by simp)).hasFDerivAt
    exact DFunLike.congr_fun ((he.comp 0 S.hasFDerivAt).fderiv.symm.trans
      (orig.fderiv_eq.trans (fderiv_id ..))) y
  have hx u v := h.bend hs ho u v
  simp_rw [Work.F05.bend_congr hsym, h.bend contDiffAt_snd rfl,fderiv_snd] at hx
  rw [←hh,←ht,←hx,←hx]
  simp

variable {G : Gauge} {m : Side}

abbrev torque (u : BaseSites G m) (z : ℝ×Link G m) := moveField (z.1 • u,z.2)

lemma torque_diff (u : BaseSites G m) : ContDiffAt ℝ ω (torque u) 0 := by
  let H := fun z : ℝ×Link G m => (z.1•u,z.2)
  have hu : H 0=0 := Prod.ext (zero_smul ..) rfl
  have hp : ContDiffAt ℝ ω moveField (H 0) := hu.symm ▸ moveField_analytic.contDiffAt
  exact hp.comp _ (by unfold H;fun_prop)

lemma torque_deriv (u : BaseSites G m) :
    HasDerivAt (fun t:ℝ => torque u (t,0)) (-gradientA G m u) 0 := by
  convert! Push.side _ moveField_analytic.differentiableAt (u,0)
  · ext t; rw [Prod.smul_mk,smul_zero]
  rw [moveField_rate,zero_sub]

lemma torque_germ (u : BaseSites G m) : (fun x:Link G m=> torque u (0,x)) =ᶠ[𝓝 0] id := by
  simp [torque, moveField,shiftLinks,gauge_one]
  exact input_encodes

lemma torque_read (u : BaseSites G m) :
    ∀ᶠ z in 𝓝 (0:ℝ×Link G m), input G m (torque u z)=Lattice.gauge (switchSite (z.1 • u)) (input G m z.2) := by
  have ht : ContinuousAt (fun z : ℝ×Link G m => (z.1•u,z.2)) 0 := by fun_prop
  have hv := ht.tendsto
  simp only [zero_smul,Prod.fst_zero] at hv
  exact hv.eventually moveField_germ

variable (E : Pylon G)
lemma flame {U : Y→ Config G m} [FiniteDimensional ℝ Y]
    (h : Army U 0) (he : U 0=1) :
    ∀ᶠ y in 𝓝 0, ContDiffAt ℝ ω (burn E.p E.r (U y)) 0 := by
  filter_upwards [(tendsto_id.prodMk_nhds tendsto_const_nhds (y:=(0:Link G m))).eventually
    ((blaze_fire _ _ _ E.paths h he).eventually (by simp))]
    with y hy using hy.comp (x:=0) (f:=fun w:Link G m=>(y,w)) (contDiffAt_const.prodMk contDiffAt_id)

structure Magnet (D : Latitude) (F : Link G m → ℝ) : Prop extends Flat F where
  loyal (x : BaseSites G m) : D.repeats x → Vanishes F (gradientA G m x)

variable (D : Latitude)
lemma ep_zero (hG : G.Simple) (he : 0<D.radius) :
    Flat (epCost D E.p E.r ∘ input G m) where
  smooth := (E.endpoint.data he m).reg
  df := by
    let F:= epCost D E.p E.r ∘ input G m
    ext x
    refine oneFlag hG (fderiv ℝ F 0) ?_ x
    intro u
    rw [← tincture u]
    refine chain_fixed _ ?_ ((E.endpoint.data he m).reg.differentiableAt (by simp))
    filter_upwards [flame E ((Army.park (solid u) _).slant (Army.powL (v:=id (α:=Link G m)) contDiffAt_id))
      (by change Lattice.gauge (fun _=>u) (input G m 0)=1;rw [stain_cons,map_zero,input_zero])] with z hz
    change epCost _ _ _ (input _ _ (stain u z)) = _
    rw [← stain_cons]
    exact Latitude.staged.solid u |>.paidUp E hz

lemma ep_magnet (hG : G.Simple) (he : 0<D.radius) :
    Magnet D (epCost D E.p E.r ∘ input G m) := by
  refine ⟨ep_zero E D hG he,fun x hx=>?_⟩
  rw [← neg_neg (gradientA G m x)]
  refine Vanishes.neg (guard (ep_zero E D hG he) (torque_diff x) (torque_germ x) .rfl (torque_deriv x) ?_)
  have hk (t : ℝ) := Latitude.reinstates (hx.smul t)
  have hp : Army (fun z : ℝ×Link G m => Lattice.gauge (switchSite (z.1 • x)) (input G m z.2)) 0 :=
    (Army.powG (contDiffAt_fst.smul contDiffAt_const)).slant (Army.powL contDiffAt_snd)
  filter_upwards [flame E hp (by simp [gauge_one]), torque_read x] with z hy hz
  simp only [Function.comp_apply,hz]
  exact (hk z.1).paidUp E hy

lemma ModeCut.reg {m : Type} [Fintype m] [DecidableEq m] {P : ModeCut m}
    {M : K → Funds m} {x : K} (s : Memo M x)
    (p : IsUnit (P.cutdet (M x))) : ContDiffAt ℝ ω (fun z => P.cutlog (M z)) x := by
  have h := Memo.raw P.e x
  exact ((((h.cross s).cross h).twice (Memo.raw _ _)).det_val).log p.ne_zero

namespace BlockTie
variable {E I : Pylon G} (X : BlockTie E I) {r : ℝ}

abbrev ZSafe (m : Side) (r : ℝ) :=
  IsUnit ((X.together r m).cutdet (X.vibrant (m:=m) 1 1)) ∧ 0<r

abbrev HSafe (m : Side) (r : ℝ) :=
  IsUnit ((X.bCut r m).cutdet (X.high (m:=m) 1 1)) ∧
  IsUnit (((X.back r).cut (X.up m) (Foot G)).cutdet (grenade X.μ 1))

-- charts
abbrev B0 (z : Point G m (X.up m)) := Stationary.extend z.2
abbrev V0 (z : Point G m (X.up m)) := input G m z.1
lemma B0_one : X.B0 (m:=m) 0 = 1 := extend_zero
lemma V0_one : X.V0 (m:=m) 0 = 1 := input_zero ..
lemma B0_lit : Thaw (X.B0 (m:=m)) 0 := Thaw.through contDiffAt_snd
lemma V0_lit : Army (X.V0 (m:=m)) 0 := Army.powL contDiffAt_fst

lemma B0_fine : (X.B0 (m:=m) 0).1 = 1 := by rw [B0_one];rfl

lemma z_reg (h : X.ZSafe m r) : ContDiffAt ℝ ω (X.zEnergy r (m:=m)) 0 := by
  let H := (memo_flash X.hμ (X.B0_lit (m:=m)).1).1
  let U := H.spot.cross (Memo.raw (rearM G m _) _)
  let T := (memo_flash X.hμ (X.V0_lit (m:=m))).1
  have hp : Memo (fun z=> fromBlocks ((X.settings (X.B0 z))ᵀ * X.settings (X.B0 z)) 0 0
      (mail (X.V0 (m:=m) z) * (mail (X.V0 z))ᵀ)) 0 :=
    by rintro (i|i) (j|j)
       · exact U.spot.cross U i j
       · exact contDiffAt_const
       · exact contDiffAt_const
       exact T.cross T.spot i j
  have hp := (X.full_memo X.B0_lit X.B0_fine X.V0_lit).twice hp
  refine ((ContDiffAt.mul contDiffAt_const (ModeCut.reg hp ?_)).sub
    (ModeCut.reg (H.spot.cross H) ?_)).sub (ModeCut.reg (T.spot.cross T) ?_)
  · rw [Pi.add_apply,B0_one, V0_one]; exact h.1
  · rw [B0_fine];exact tonic_cut_unit (X.back r) _ h.2
  rw [Prod.fst_zero,input_zero];exact tonic_cut_unit (ridge r) _ h.2

lemma h_reg (h : X.HSafe m r) : ContDiffAt ℝ ω (X.hEnergy r (m:=m)) 0 := by
  let H := (memo_flash X.hμ (X.B0_lit (m:=m)).1).2.2
  refine (ContDiffAt.mul contDiffAt_const (ModeCut.reg (X.high_memo X.B0_lit X.B0_fine X.V0_lit) ?_)).sub
    (ModeCut.reg H ?_)
  · rw [B0_one,V0_one];exact h.1
  rw [B0_fine];exact h.2

lemma B0_star (u : G.El) (z : Point G m (X.up m)) :
    X.B0 (starsky u z) = X.sign (solid u) (solid u) (X.B0 z) := flare_color _ _
lemma V0_star (u : G.El) (z : Point G m (X.up m)) :
    X.V0 (starsky u z) = Lattice.gauge (solid u) (X.V0 z) := by
  have h := (stain_cons u z.1).symm
  rw [tincture] at h
  exact h

private lemma star_carry (u : G.El) :
    (X.zEnergy (m:=m) r ∘ starsky u =ᶠ[𝓝 0] X.zEnergy r) ∧
    (X.hEnergy (m:=m) r ∘ starsky u =ᶠ[𝓝 0] X.hEnergy r) := by
  have hp := X.full_fare (X.B0_lit (m:=m)) X.B0_fine X.V0_lit
  have hi := X.movers (X.B0_lit (m:=m)) X.B0_fine
  let L := starsky u (c:=m) (f:=X.up m)
  have hv : Tendsto L (𝓝 0) (𝓝 0) := by simpa only [map_zero] using L.continuous.tendsto 0
  apply eventually_and.mp; filter_upwards [hi,hv.eventually hp,hv.eventually hi] with z hh he h
  change X.zCost r (X.B0 (L z)) _ = _ ∧ X.hCost r (X.B0 (L z)) _ = _
  rw [show X.B0 (L z)=_ from X.B0_star _ z] at *
  rw [show X.V0 (L z)=_ from X.V0_star _ z] at he
  change X.zCost _ _ (X.V0 (L z)) = _ ∧ X.hCost _ _ (X.V0 (L z)) = _
  rw [show X.V0 (L z)=_ from X.V0_star _ z]
  exact ⟨X.z_swivel (.solid _) (.solid _) he, X.h_swivel (.solid _) (.solid _) hh h he⟩

lemma z_flat (h : X.ZSafe m r) : Flat (X.zEnergy (m:=m) r) :=
  ⟨X.z_reg h,triple_star X.simple (fun u=> (X.star_carry u).1) ((X.z_reg h).differentiableAt (by simp))⟩

lemma h_flat (h : X.HSafe m r) : Flat (X.hEnergy (m:=m) r) :=
  ⟨X.h_reg h,triple_star X.simple (fun u=> (X.star_carry u).2) ((X.h_reg h).differentiableAt (by simp))⟩

section rule
variable {A : Type} [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A]
variable {p : A→ Point G m (X.up m)} {k : A → Coats G (X.up m)} {u : A→Coats G m}
def anew (k : A → Coats G (X.up m)) (u : A→Coats G m) (p : A→ Point G m (X.up m)) (x : A) := (X.sign (k x) (u x) (X.B0 (p x)),
                     Lattice.gauge (u x) (X.V0 (p x)))

def wchart (b : Joint G m (X.up m) × Config G m) : Point G m (X.up m) :=
  (content b.2, retract b.1)

lemma z_rewrite (hk : Army k 0) (kg : k 0=1) (hu : Army u 0) (ug : u 0=1)
    (hp : ContDiffAt ℝ ω p 0) (pg : p 0=0)
    (hb : ∀ x,(X.back r).staged (k x)) (ht : ∀ x,(ridge r).staged (u x)) :
    let H := X.wchart ∘ X.anew k u p
    ContDiffAt ℝ ω H 0 ∧ (X.zEnergy r ∘ H =ᶠ[𝓝 0] X.zEnergy r ∘ p) := by
  let b z := (X.anew k u p z).1
  let v z := (X.anew k u p z).2
  have bo : b 0=1 := by simp [b,anew,kg,ug,pg,X.B0_one,sign]
  have vo : v 0=1 := by simp [v,anew,ug,pg,X.V0_one,gauge_one]
  have ba : Thaw b 0 := ((Thaw.through hp.snd).wages _ hk hu)
  have va : Army v 0 := hu.slant (Army.powL hp.fst)
  refine ⟨(va.logL vo).prodMk (ba.log bo),?_⟩
  filter_upwards [X.full_fare ba (by rw [bo];rfl) va,
    (show Tendsto v _ (𝓝 1) from vo ▸ va.cont.tendsto).eventually content_encodes,
    (show Tendsto b _ (𝓝 1) from bo ▸ ba.cont.tendsto).eventually extend_retract] with z hy hi hh
  change X.zCost r (Stationary.extend (retract (b z))) (input _ _ (content (v z))) = _
  rw [hi,hh]; exact X.z_swivel (hb z) (ht z) hy
end rule

lemma return_wchart :
    (fun z:Point G m (X.up m)=> X.wchart (X.B0 z,X.V0 z)) =ᶠ[𝓝 0] id := by
  filter_upwards [(continuous_fst.tendsto (0:Point G m (X.up m))).eventually input_encodes,
    (continuous_snd.tendsto (0:Point G m (X.up m))).eventually retract_extend]
    with z hh hv using Prod.ext hh hv

lemma z_small {k : ℝ → Coats G (X.up m)} {u : ℝ→Coats G m}
    (hk : k 0=1) (hu : u 0=1) :
    let H := X.wchart ∘ X.anew (k ∘ Prod.fst) (u ∘ Prod.fst) (p:=Prod.snd)
    (fun z:Point G m (X.up m)=> H (0,z)) =ᶠ[𝓝 0] id := by
  simp only [Function.comp_apply,anew,hk,hu,gauge_one,sign,wages_zero]
  exact X.return_wchart

lemma z_fine (s : X.ZSafe m r) {x : BaseSites G (X.up m)} (h : (X.back r).repeats x) :
    Vanishes (X.zEnergy r) (0,corps (X.S m) 1 x) := by
  let k := fun a:ℝ=> switchSite (a • x)
  let u : ℝ→Coats G m := fun _=> 1
  have ko : k 0=1 := by simp [k]
  have he := X.z_rewrite (k:=k ∘ Prod.fst) (u:=u ∘ Prod.fst) (p:=Prod.snd)
    (Army.powG (contDiffAt_fst.smul contDiffAt_const)) ko (Army.park _ _) rfl contDiffAt_snd rfl
    (r:=r) (fun z=> Latitude.reinstates (h.smul z.1)) (fun _ _=> rfl)
  refine guard (X.z_flat s) he.1 (X.z_small (u:=u) ko rfl)
    (W:=fun a => (0, parade (X.S m) 1 (a • x))) ?_
    ((hasDerivAt_const ..).prodMk (Push.side _
      ((parade_diff _ _).differentiableAt (by simp)) x)) he.2
  exact Eventually.of_forall fun z => by
    simp [wchart, Function.comp_apply,anew,B0_one,V0_one,k,u,parade,gauge_one, sign]

lemma z_coarse (s : X.ZSafe m r) {x : BaseSites G m} (h : (ridge r).repeats x) :
    Vanishes (X.zEnergy r) (-gradientA G m x,(0,x)) := by
  let u := fun a:ℝ=> switchSite (a • x)
  let k : ℝ→Coats G (X.up m) := fun _=> 1
  have uo : u 0=1 := by simp [u]
  have he := X.z_rewrite (m:=m) (k:=k ∘ Prod.fst) (u:=u ∘ Prod.fst) (p:=Prod.snd)
    (Army.park _ _) rfl (Army.powG (contDiffAt_fst.smul contDiffAt_const)) uo contDiffAt_snd rfl
    (r:=r) (fun _ _=> rfl) (fun z=> Latitude.reinstates (h.smul z.1))
  refine guard (X.z_flat s) he.1 (X.z_small (k:=k) rfl uo)
    (W:=fun a=> (torque x (a,0),(0,a • x))) ?_
    ((torque_deriv x).prodMk ((hasDerivAt_const ..).prodMk (by simpa using ((hasDerivAt_id' (0:ℝ)).smul_const x)))) he.2
  have ht := (continuous_id.smul (continuous_const (y:=x))).tendsto (0:ℝ)
  change Tendsto (fun t:ℝ=> t • x) _ (𝓝 ((0:ℝ) • x)) at ht; rw [zero_smul] at ht
  filter_upwards [ht.eventually frameLog_switch] with z hz
  simp [wchart,anew,u,k,sign, B0_one,V0_one,wages,gauge_one,retract,torque,moveField,shiftLinks,hz]

end BlockTie
end ExactRunning
