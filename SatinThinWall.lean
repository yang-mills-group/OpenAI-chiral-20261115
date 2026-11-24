import SatinFixedContrastNovember4

import SatinThinCollapse

/-!
# A thin bilocal-composite experiment: II. wall and grid

General-purpose lemmas, for any Apron whose stencil is born in positive time
at its intrinsic resolution. These generalize arguments in the Six files
(Photos, TransitWall, FineRays). Use the ACTUAL UNprojected vectors and
prove which continuum-space-projected vectors they approach for fixed widths;
projection is not built into finite-grid values. Flip earlier test in **time
only** for use of OS Gram. Retains full arbitrary transverse positioning and
**the joint gauge-matter mark** as the smearand. We do not co-sample the two
center poses with any contact requirement.
-/
set_option autoImplicit false
set_option maxHeartbeats 350000
set_option synthInstance.maxSize 28000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open Lamour.Bridge.Celeste.Morn
namespace Spine
open Aria Casting Six OS.Semigroup.Balloon

open MacroGrid Set

private lemma thin_heats {X : Hilbert} {j : Axis} (p : OS.Semigroup X j)
    (v : X) (a b : ℝ) (f : 0 ≤ a) (w : a ≤ b) :
    p.E ((b-a).toNNReal) (p.E a.toNNReal v)= p.E b.toNNReal v := by
  have he : b.toNNReal=(b-a).toNNReal+a.toNNReal := by ext; simp [f,f.trans w, sub_nonneg.mpr w]
  rw [he,p.time]; rfl

section
variable (P : Spine) (x : P.Spectrum0 3)
local notation "ξ" => P.advocate 3 x 3
local notation "M" => timeMesh P.par
local notation "H" => P.ColorHil 3 ξ
local notation "ω" => P.colorZero 3 ξ
local notation "S" => P.physicalEnergy 3 ξ
local notation "E" => (S).E
local notation "Γ" => P.truck 3 ξ
local notation "G" => P.ManyF 3 ξ
local notation "Ω" => P.heaven 3 ξ
local notation "R" => P.seasons 3 ξ
local notation "V₀" => P.cartage 3 ξ
local notation "π'" => P.wealth 3 ξ
local notation "λ'" => (P.enter 3 ξ)

/-- OS vector at the seam. -/
abbrev thinOrigin (A:P.Apron) (h:P.birthF 3 A.s A.F) : H := P.viewF 3 ξ A.s h
variable (t : ℕ) (A : P.Apron) (eA : P.birthF 3 A.s A.F)
local notation "Y" => P.thinOrigin x A eA
local notation "w" => A.realWidth P 3
local notation "u" => P.meshPose t
local notation "T" => P.vtile t

/-- Extend off the ordered region using `toNNReal`; used only to simplify integration.
Don't claim price interpretation on that extension! -/
def thinGridRay (p:Cover) : H:= Γ (T p) (E ((u p 3).toNNReal) Y)
def thinRay (p:Vantage) : G:= V₀ p ((R).E ((p 3).toNNReal) (π' Y))

/- We do *not* need to spend a special padding grant not already in the Apron's
 positive width. The actual transfer over its width acts on an already-paid view. -/
theorem thinRawEntry : A.engine P 3 ξ ω = E (w).toNNReal Y := by
  let a := A.u 3
  have he : whenly M A.s a=(w).toNNReal := by
    change whenly M A.s a=(bell M A.s a).toNNReal; rw [natural_time]; exact Real.toNNReal_coe.symm
  exact (P.engine_view 3 ξ A).trans ((P.identical_F 3 ξ A.s _ (P.passesLater 3 A.s a eA)
    (A.card_price P 3)).trans ((P.releasedLater 3 ξ A.s a eA).trans
        (congrArg (fun b:ℝ≥0 => E b Y) he)))

lemma thin_charter_shift (p:Cover) (z:ℝ)(h:(w)≤z):
    E ((z-(w)).toNNReal) (P.charter 3 ξ (T p) (A.engine P 3 ξ) ω)=
      Γ (T p) (E z.toNNReal Y):= by
  let y:= A.engine P 3 ξ ω
  let U:=P.truck 3 ξ (T p)
  let Z':=E (z-(w)).toNNReal
  exact (congrArg (fun y:H=> Z' y) (P.raw_aperture 3 ξ (T p) A)).trans
    (((P.sixWard_truck_heat 3 ξ (T p) (z-(w)).toNNReal y).symm).trans
      (congrArg (fun y:H=> U y) ((congrArg (fun y:H=> Z' y) (P.thinRawEntry x A eA)).trans
        (thin_heats S Y (w) z (A.real_width_pos P 3).le h))))

lemma thin_grid_pose_view(k:Cover)(b:(w)< u k 3)(p:A.s≤t):
    ∃ h:P.birthF 3 t (P.issuing t A k), P.viewF 3 ξ t h=P.thinGridRay x t A eA k:= by
  let i:Fin 1:=0; let L:=[i]; let Q:= fun _:Fin 1=>A; let r:=fun _:Fin 1=>k
  have he : ∀ i∈L,(Q i).s≤t := fun i _=>p
  have ht:P.onBoard 3 t Q r L 0:= by
    refine ⟨(bell_le M t _ _).1 ?_,trivial⟩
    rw [P.begins 3 Q r t i p]; change bell M t 0 ≤ u k 3 - (w)
    rw [show bell M t 0=0 by simp [bell]]; linarith
  have hx: P.issuing t A k=P.shifts 3 (-(0:ℤ)) (P.fullScroll t Q r L):= by
    rw [neg_zero,P.shifts_zero]; change _=_*1; rw [mul_one]; rfl
  obtain ⟨f,g⟩:= P.vread 3 ξ t _ _ L 0 ht he
  have u':P.birthF 3 t (P.issuing t A k):=by rw [hx]; exact f
  refine ⟨u', (P.identical_F 3 ξ t _ _ hx).trans (g.trans ((P.transporting 3 ξ Q r t L 0 ht he).trans ?_))⟩
  let C:= P.charter 3 ξ (T k) (A.engine P 3 ξ)
  rw [show bell M t 0=0 by simp [bell]]
  change E (((u k 3-(w))-0).toNNReal) (C ω)= _
  rw [sub_zero]; exact P.thin_charter_shift x t A eA k (u k 3) b.le

variable (F : SampleDose)
local notation "α" => P.activation t F
local notation "Q" => P.usedGrid t F
local notation "δ" => P.macroStep t

def thinGridKet : H := ∑ i∈ Q, α i • P.thinGridRay x t A eA i
def thinKet : G := ∫ p:Vantage, (F.val p:ℂ) • P.thinRay x A eA p

/-- The exact selected meaning at the finer grid height t. -/
lemma thin_grid_view (p:P.WallAfter A F 0)(h:A.s≤t) :
    ∃ q:P.birthF 3 t (P.prepared t A F), P.viewF 3 ξ t q=P.thinGridKet x t A eA F := by
  refine P.birthSum ξ t Q _ _ ?_
  intro i v
  have hA : (w) < u i 3:= (zero_add _).symm.trans_lt (p _ ((P.usedPose t F i).1 v))
  let q:=P.thin_grid_pose_view x t A eA i hA h
  exact ⟨P.birthScale t (α i) q.choose,(P.sixWard_view_scale ξ t (α i) q.choose).trans
    (congrArg (fun y:H=> (α i) • y) q.choose_spec)⟩

private lemma thin_into_grid (X:Hilbert)(f:Vantage→X)(U:Cover → X.Op):
    poseApprox X (fun z:Vantage=>(F.val z:ℂ) • f z) U (δ) =∑ i∈ Q, α i • U i (f (u i)):=by
  let g:=fun i:Cover=> U i ((F.val (u i):ℂ) • f (u i));
  have he(i:Cover)(x:i∉Q): g i=0:= by
    have hu : F.val (u i)=0 := by by_contra p; exact x ((P.usedPose t F i).2 (subset_closure p))
    unfold g; rw [hu,Complex.ofReal_zero,zero_smul,map_zero]
  refine (room_price (δ) (P.macroStep_pos t) g Q he).2.trans ?_
  rw [Finset.smul_sum]; apply Finset.sum_congr rfl; intro i h
  unfold g; rw [map_smul,
    show Fintype.card Axis=4 by rfl, ← Complex.coe_smul ((δ)^4), smul_smul]
  push_cast [activation]; rfl

lemma thin_to_ket (J:P.Ellis 3 x) : Tendsto (fun t' => P.thinGridKet x t' A eA F) atTop
      (𝓝 (λ' (P.thinKet x A eA F))) := by
  let f(p:Vantage):= E (p 3).toNNReal Y
  let g(p:Vantage):=(F.val p:ℂ) • f p
  let K:=π'; let l(p:Vantage):= V₀ p (K (g p))
  have he:HasCompactSupport g:= F.budget.mono (fun i v t=> v ((congrArg (fun b:ℝ=> (b:ℂ) • f i)
      (show F.val i=0 from t)).trans (zero_smul ℂ _)))
  have ht:Continuous g:= (Complex.continuous_ofReal.comp F.smooth.continuous).smul
    (((S).continuousE Y).comp (continuous_real_toNNReal.comp (continuous_apply _)))
  have hp : (fun p => (F.val p:ℂ) • P.thinRay x A eA p)=l := funext fun p => by
    let E':=(R).E; let U:=V₀ p; let c:=(F.val p:ℂ)
    exact ((congrArg U (map_smul K c (f p))).trans ((map_smul U c _).trans
      (congrArg (fun y:G=> c • (U y)) (P.bankHeat 3 ξ (p 3).toNNReal Y)))).symm
  unfold thinKet; rw [hp]
  exact (P.macroRiemann x 3 J g he ht).congr fun i=> thin_into_grid P i F H f _

lemma thin_flipWallBefore (a:ℝ)(p:P.WallBefore A F (-a)) : P.WallAfter A (flipDose F 3) a := by
  intro y h
  rw [flipBudget] at h
  have hv := p (poseMirror 3 y) h
  change a+(w)<y 3
  rw [show (poseMirror 3 y) (3:Axis) = - y 3 from (show opposeR 3 y 3 = -y 3 from if_pos rfl)] at hv
  linarith only [hv]

lemma thin_flipDose_twice : flipDose (flipDose F 3) 3= F := by
  have extD {x y: SampleDose} : x.val = y.val → x=y := by cases x; cases y; rintro t; cases t; rfl
  have he : (flipDose (flipDose F 3) 3).val = F.val := funext fun i =>
    congrArg F.val (reflectPose_twice 3 i)
  exact extD he

/-- Don't demand that the earlier external test is the time reflection of
    the later external test. Rather pay the earlier vector with its *own* test. -/
lemma thin_grid_flip (q:P.WallBefore A F 0)(p:A.s≤t) :
    ∃ k:P.Test, P.reflectTest 3 k=P.prepared t (A.kiss P 3) F ∧
      ∃ h:P.birthF 3 t k, P.viewF 3 ξ t h=P.thinGridKet x t A eA (flipDose F 3) := by
  let L:=flipDose F 3
  refine ⟨P.prepared t A L,(P.prepared_opposition t A L 3).symm.trans
    (congrArg (P.prepared t (A.kiss P 3)) (thin_flipDose_twice F)),?_⟩
  exact thin_grid_view P x t A eA L (P.thin_flipWallBefore A F 0 (by simpa using q)) p

lemma thin_pair_grid (B:P.Apron) (eB : P.birthF 3 B.s B.F)
    (U:SampleDose) (a:P.WallBefore A F 0) (b:P.WallAfter B U 0) (h:A.s≤t)(g:B.s≤t) :
    P.singleState 3 t x (P.prepared t (A.kiss P 3) F * P.prepared t B U) =
      inner ℂ (P.thinGridKet x t A eA (flipDose F 3)) (P.thinGridKet x t B eB U) := by
  obtain ⟨k,v,h₁,h'⟩:= P.thin_grid_flip x t A eA F a h
  obtain ⟨g₁,g'⟩:= P.thin_grid_view x t B eB U b g
  rw [← v,← P.single_agrees 3 3 x,← h',← g']; exact (P.released_gram 3 ξ t h₁ g₁).symm

lemma thin_pair_kets (B:P.Apron) (eB : P.birthF 3 B.s B.F)
    (U:SampleDose) (a:P.WallBefore A F 0) (b:P.WallAfter B U 0) (J:P.Ellis 3 x) :
    Tendsto (fun t => P.singleState 3 t x (P.prepared t (A.kiss P 3) F * P.prepared t B U)) atTop
      (𝓝 (inner ℂ (P.thinKet x A eA (flipDose F 3)) (P.thinKet x B eB U))) := by
  have ht:= (P.thin_to_ket x A eA (flipDose F 3) J).inner (𝕜:=ℂ) (P.thin_to_ket x B eB U J)
  rw [(λ').inner_map_map] at ht
  exact ht.congr' (((eventually_ge_atTop A.s).and (eventually_ge_atTop B.s)).mono (fun i h=>
    (P.thin_pair_grid x i A eA F B eB U a b h.1 h.2).symm))

lemma thin_late_single_grid (a:P.WallAfter A F 0)(h:A.s≤t) :
    P.singleState 3 t x (P.prepared t A F) = inner ℂ ω (P.thinGridKet x t A eA F) := by
  obtain ⟨g₁,g'⟩ := P.thin_grid_view x t A eA F a h
  rw [←g']; exact ((P.view_scalar 3 ξ t g₁).trans (P.single_agrees 3 3 x _ _)).symm

lemma thin_early_single_grid (a:P.WallBefore A F 0)(h:A.s≤t) :
    P.singleState 3 t x (P.prepared t (A.kiss P 3) F) =
      star (inner ℂ ω (P.thinGridKet x t A eA (flipDose F 3))) := by
  obtain ⟨k,g,h₀,h'⟩:=P.thin_grid_flip x t A eA F a h
  exact (congrArg (P.singleState 3 t x) g.symm).trans
    (((P.common_reading t x k 3).2.2.1).trans (congrArg star
      (((congrArg (inner ℂ ω) h'.symm).trans ((P.view_scalar 3 ξ t h₀).trans (P.single_agrees 3 3 x t k))).symm)))

lemma thin_late_single (a:P.WallAfter A F 0) (J:P.Ellis 3 x) :
    Tendsto (fun t => P.singleState 3 t x (P.prepared t A F)) atTop
      (𝓝 (inner ℂ Ω (P.thinKet x A eA F))) := by
  have he: Tendsto (fun (_:ℕ)=>ω) atTop (𝓝 (λ' Ω)) := tendsto_const_nhds
  have ht := he.inner (𝕜:=ℂ) (P.thin_to_ket x A eA F J)
  rw [(λ').inner_map_map] at ht
  exact ht.congr' ((eventually_ge_atTop A.s).mono fun i h=>
    (P.thin_late_single_grid x i A eA F a h).symm)

lemma thin_early_single (a:P.WallBefore A F 0) (J:P.Ellis 3 x) :
    Tendsto (fun t => P.singleState 3 t x (P.prepared t (A.kiss P 3) F)) atTop
      (𝓝 (star (inner ℂ Ω (P.thinKet x A eA (flipDose F 3))))) := by
  have he: Tendsto (fun (_:ℕ)=>ω) atTop (𝓝 (λ' Ω)) := tendsto_const_nhds
  have ht := (he.inner (𝕜:=ℂ) (P.thin_to_ket x A eA (flipDose F 3) J)).star
  rw [(λ').inner_map_map] at ht
  exact ht.congr' ((eventually_ge_atTop A.s).mono fun i h=>
    (P.thin_early_single_grid x i A eA F a h).symm)

lemma thinRay_cont : Continuous (P.thinRay x A eA) :=
  P.caravan 3 ξ id _ continuous_id (((R).continuousE (π' Y)).comp
    (continuous_real_toNNReal.comp (continuous_apply (3:Axis))))

end
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
