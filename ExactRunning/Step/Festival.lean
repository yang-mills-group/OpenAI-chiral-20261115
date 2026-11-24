import ExactRunning.Step.Record
import ExactRunning.Det.Prediction

/-!
# Joint finite Hessians

Order of coordinates: ((fine links, added coarse-site frame) = high, coarse links).
Left tangents (Exp increments on left). Rooted frame; K=1, no field-dependent dress
in the tangent chart. Joint function and Hessian with both backgrounds (joint
`b` and coarse `v`) held independent:

* `sitting` is the action (fine classical plus penalty); `full` its full Hessian
  in these coordinates, with blocks `thick`, `spat`, transpose, `alto`.
* `Stable` (on shell): stationary in high slots. Then the Hessian annihilates
  verticals of the fine site gauge (acts on fine links and added coarse-site frame);
  see `wort`.
* `vibrant`: full Hessian completed using `settings=(mail b.1)ᵀ ∘ first` in
  high slots and `(mail v)ᵀ` in coarse slots (ghost for each in Step.Fleets).
  Change high fixing to `restored` with massive ghost, giving `high` block.
* `rest_schur`: given a local stationary graph (`Rest`), Schur complement with
  this latter pivot is Hessian of stationary value plus coarse completion.
  Eventual identities at arbitrary nearby shell points will be useful.
-/

set_option linter.unusedSectionVars false
noncomputable section
namespace ExactRunning
open YM Stationary Lattice Laurent Bloch RG
open Function Filter Finset Matrix
open scoped BigOperators ContDiff Topology ComplexConjugate Matrix

open Exterior Wilson Precision
open Tree

namespace BlockTie
variable {G : Gauge} {E I : Pylon G} {m : Side} {X : BlockTie E I}


-- abbreviations
variable (X)
abbrev Hall (m : Side) := Vault G m (X.up m) × Link G m
abbrev Drum (m : Side) := Bodies G m (X.up m) ⊕ Lines G m 1
abbrev podium (m) := (helmets G m (X.up m)).prod (pocket (Lines G m 1))

abbrev S (m : Side) := (X.step m)
abbrev Z (m : Side) := ribbon (X.step m) (X.choice m) (G:=G)
abbrev J (m : Side) := muster (X.step m) (X.choice m) E.p E.r

def sitting (b : Joint G m (X.up m)) (v : Config G m) (y : X.Hall m) :=
  X.J m (input G m y.2*v) (Stationary.extend y.1*b)

def full (b : Joint G m (X.up m)) (v : Config G m) := damage (X.podium m) (X.sitting b v) 0
def thick (b : Joint G m (X.up m)) (v : Config G m) :=
  damage (helmets _ _ _) (canon (X.S m) (X.choice m) E.p E.r v b) 0
def spat (b : Joint G m (X.up m)) (v : Config G m) := (X.full b v).toBlocks₁₂
def alto (b : Joint G m (X.up m)) (v : Config G m) := (X.full b v).toBlocks₂₂

def settings (b : Joint G m (X.up m)) : Matrix (Lines G (X.up m) 0) (Bodies G m (X.up m)) ℝ :=
  (mail b.1)ᵀ * rearM _ _ _
abbrev μ := inch X.L
lemma hμ : 0<X.μ := inch_pos _
def restored (b : Joint G m (X.up m)) :=
  cannonade (X.S m) (X.choice m) X.μ 1 b

def throat (b : Joint G m (X.up m)) (v : Config G m) := X.alto b v + mail v*(mail v)ᵀ

def vibrant (b : Joint G m (X.up m)) (v : Config G m) :=
  X.full b v + fromBlocks ((X.settings b)ᵀ * X.settings b) 0 0 (mail v*(mail v)ᵀ)

def high (b : Joint G m (X.up m)) (v : Config G m) :=
  X.thick b v + (X.restored b)ᵀ * X.restored b

lemma high_eq (b : Joint G m (X.up m)) (v : Config G m) :
    X.high b v = medals (X.S m) (X.choice m) E.p E.r X.μ 1 v b := by rw [medals,cannon_law];rfl

variable {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

section prepare
variable [FiniteDimensional ℝ Y] {b : Y → Joint G m (X.up m)} {v : Y→Config G m}
    (hb : Thaw b 0) (ho : (b 0).1=1) (hv : Army v 0)
include hb ho hv

lemma crew :
    ContDiffAt ℝ ω (fun y : Y × X.Hall m => X.sitting (b y.1) (v y.1) y.2) 0 :=
  Thaw.earn X.branches (X.choice m)
    ((Thaw.through contDiffAt_snd.fst).mul (hb.comp (w:=Prod.fst) contDiffAt_fst)) (by
      change (Stationary.extend 0*b 0).1=1
      rw [extend_zero,one_mul,ho])
    ((Army.powL contDiffAt_snd.snd).mul (hv.comp (w:=Prod.fst) contDiffAt_fst))
    E.paths

lemma full_memo : Memo (fun y => X.full (b y) (v y)) 0 :=
  memo_damage _ (F:=fun y => X.sitting (b y) (v y)) (X.crew hb ho hv)

lemma full_fare : ∀ᶠ y in 𝓝 0, ContDiffAt ℝ ω (X.sitting (b y) (v y)) 0 := by
  filter_upwards [(tendsto_id.prodMk_nhds tendsto_const_nhds (y:=(0:X.Hall m))).eventually
    ((X.crew hb ho hv).eventually (by simp))]
      with y h using
        h.comp (x:=(0:X.Hall m)) (f:=fun t => (y,t)) (contDiffAt_const.prodMk contDiffAt_id)

omit hv in
lemma movers : ∀ᶠ y in 𝓝 0,
    Explosives (X.S m) (X.choice m) 1 (b y) :=
  explosive _ _ X.branches root_customs hb ho

lemma high_memo : Memo (fun y => X.high (b y) (v y)) 0 := by
  simp_rw [high_eq]; exact (ammo_pay _ _ hb ho hv _ root_customs X.branches (X.choice m) E.paths X.hμ).2.1
end prepare

lemma settings_stood (b : Joint G m (X.up m)) :
    X.settings b * stood (X.S m) b = tonic b.1 := by
  rw [settings,Matrix.mul_assoc,corporal]; rfl

lemma restored_stood {b : Joint G m (X.up m)} (hp : Explosives (X.S m) (X.choice m) 1 b) :
    X.restored b * stood (X.S m) b = grenade X.μ b.1 :=
  count_ammo _ _ _ X.branches hp

end BlockTie

lemma halvesP {n u α : Type} [Fintype n] [Fintype u] [NonUnitalNonAssocSemiring α]
    (a c : n→α) (b d : u→α) :
    dotProduct (Sum.elim a b) (Sum.elim c d) = dotProduct a c + dotProduct b d := by
  rw [dotProduct,Fintype.sum_sum_type];rfl

lemma halvesC {n u P Q : Type} [Fintype n] [Fintype u] [DecidableEq n] [DecidableEq u]
  [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup Q] [NormedSpace ℝ Q]
    (A : Module.Basis n ℝ P) (B : Module.Basis u ℝ Q) (x : P × Q) :
    cash (A.prod B) x = Sum.elim (cash A x.1) (cash B x.2) := by
  funext i;cases i
  · exact cash_prod_left A B x _
  exact cash_prod_right A B x _

namespace BlockTie
variable {G : Gauge} {E I : Pylon G} {m : Side} (X : BlockTie E I)
variable {b : Joint G m (X.up m)} {v : Config G m} (h : ContDiffAt ℝ ω (X.sitting b v) 0)
include h
lemma full_up : (X.full b v).toBlocks₁₁ = X.thick b v := by
  let L := ContinuousLinearMap.inl ℝ (Vault G m (X.up m)) (Link G m)
  have ho : X.sitting b v ∘ L = canon (X.S m) (X.choice m) E.p E.r v b := by
    funext ;change X.J m (input G m 0 * v) _ = _; rw [input_zero, one_mul];rfl
  unfold full thick; rw [← ho]
  ext i j
  simp only [toBlocks₁₁,Matrix.of_apply, damage, LinearMap.toMatrix₂_apply,
    Work.F05.bend_apply, podium, Module.Basis.prod_apply]
  rw [wired L (by rw [map_zero]; exact h.analyticAt),map_zero]
  congr 1; funext i;fin_cases i <;> rfl

lemma full_shape :
    X.full b v = fromBlocks (X.thick b v) (X.spat b v) (X.spat b v)ᵀ (X.alto b v) := by
  rw [← X.full_up h]
  ext (i|i) (j|j) <;> try rfl
  exact congr($(damage_symm (X.podium m) h) (.inl j) (.inr i))

lemma thick_tr : (X.thick b v)ᵀ = X.thick b v := by
  rw [← X.full_up h];ext i j
  exact congr($(damage_symm (X.podium m) h) (.inl i) (.inl j))

lemma vibrant_shape :
    X.vibrant b v = Det.joint (X.settings b) (X.thick b v) (X.spat b v) (X.throat b v) := by
  rw [vibrant,X.full_shape h,fromBlocks_add]; simp [Det.joint,throat]

lemma full_charge (x y : X.Hall m) :
    iteratedFDeriv ℝ 2 (X.sitting b v) 0 ![x,y] =
    dotProduct (cash (helmets _ _ _) x.1) ((X.thick b v *ᵥ cash (helmets _ _ _) y.1) + X.spat b v *ᵥ y.2) +
    dotProduct x.2 (((X.spat b v)ᵀ *ᵥ cash (helmets _ _ _) y.1) + X.alto b v *ᵥ y.2) := by
  rw [← detracts (X.podium m)]
  change dotProduct _ ((X.full b v) *ᵥ _)=_
  simp only [X.full_shape h,podium,halvesC,cash_pocket, Matrix.fromBlocks_mulVec,Sum.elim_comp_inl,Sum.elim_comp_inr,halvesP]
omit h

end BlockTie

section derivatives
variable {Z Y : Type} [NormedAddCommGroup Z] [NormedAddCommGroup Y] [NormedSpace ℝ Z] [NormedSpace ℝ Y]

lemma riding {F : Z → ℝ} {g : Y→ Z} {y : Y} (v : Z)
    (hF : ContDiffAt ℝ ω F (g y)) (hg : ContDiffAt ℝ ω g y)
    (h : ∀ᶠ z in 𝓝 y, fderiv ℝ F (g z) v = fderiv ℝ F (g y) v) (x : Y) :
    iteratedFDeriv ℝ 2 F (g y) ![v,fderiv ℝ g y x] = 0 := by
  have hu : ContDiffAt ℝ ω (fun z => fderiv ℝ F z v) (g y) :=
    (hF.fderiv_right (le_rfl : ω+1 ≤ ω)).clm_apply contDiffAt_const
  have hh := fderiv_comp y (hu.differentiableAt (by simp)) (hg.differentiableAt (by simp))
  have h : ((fun z => fderiv ℝ F z v) ∘ g)=ᶠ[𝓝 y] (fun _ => fderiv ℝ F (g y) v) := h
  rw [h.fderiv_eq, (hasFDerivAt_const ..).fderiv] at hh
  rw [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_zero,
    show _ = _ from hF.isSymmSndFDerivAt le_top
    v (fderiv ℝ g y x)]
  have ht := DFunLike.congr_fun hh.symm x
  rw [ContinuousLinearMap.comp_apply,divided _ _ hF,iteratedFDeriv_two_apply] at ht
  exact ht

end derivatives

namespace BlockTie
variable {G : Gauge} {E I : Pylon G} {m : Side} (X : BlockTie E I)
variable {b : Joint G m (X.up m)} {v : Config G m} (h : ContDiffAt ℝ ω (X.sitting b v) 0)

include h
lemma spat_stood :
    (X.spat b v)ᵀ * stood (X.S m) b = 0 := by
  let S := X.S m
  let F := X.sitting b v
  let g (z : BaseSites G (X.up m)) : X.Hall m := (parade S b z, 0)
  have ho : g 0=0 := Prod.ext (parade_zero ..) rfl
  have hh : ContDiffAt ℝ ω F (g 0) := ho.symm ▸ h
  have hd := parade_diff S b
  have hp : ContDiffAt ℝ ω g 0 := hd.prodMk contDiffAt_const
  have ht : fderiv ℝ g 0 = (corps S b).prod 0 :=
    ((hd.differentiableAt (by simp)).hasFDerivAt.prodMk (hasFDerivAt_const ..)).fderiv
  apply testers; intro y z
  have hh := riding (v:=((0,y):X.Hall m)) hh hp ?_ z
  · rw [ht,ho] at hh
    change iteratedFDeriv ℝ 2 (X.sitting b v) 0 ![(0,y),(corps S b z,0)]=0 at hh
    rw [X.full_charge h] at hh
    simp only [← Matrix.mulVec_mulVec,stands,zero_mulVec]
    simpa using hh
  let L (x:Vault G m (X.up m)) (w:Link G m) := (x,w)
  have P (x) := (hasFDerivAt_const (𝕜:=ℝ) (x:Vault G m (X.up m)) (0:Link G m)).prodMk
    (hasFDerivAt_id (𝕜:=ℝ) 0)
  filter_upwards [hp.continuousAt.tendsto.eventually (hh.eventually (by simp)),
    parade_read S b] with z hg hb
  have hk : F ∘ L (parade S b z)=F ∘ L (parade S b 0) := by
    funext i; change X.J m (input G m i*v) (Stationary.extend _*b)=X.J m _ (Stationary.extend _*b)
    rw [hb,parade_zero,extend_zero,one_mul]
    simpa only [gauge_one] using
      root_wages S (X.choice m) X.branches b 1 (switchSite z) E.p E.r E.paths (input G m i*v)
  have hi := ((hg.differentiableAt (by simp)).hasFDerivAt.comp 0 (P (parade S b z))).fderiv
  have hi' := ((hh.differentiableAt (by simp)).hasFDerivAt.comp (f:=L (parade S b 0)) 0 (P (parade S b 0))).fderiv
  exact DFunLike.congr_fun (hi.symm.trans ((congr_arg (fun f=> fderiv ℝ f 0) hk).trans hi')) y

omit h
abbrev Stable (b : Joint G m (X.up m)) (v : Config G m) := Shell (X.S m) (X.choice m) E.p E.r v b
include h

lemma wort (s : X.Stable b v) :
    X.thick b v * stood (X.S m) b = 0 ∧ (X.spat b v)ᵀ * stood (X.S m) b=0 ∧ (X.thick b v)ᵀ = X.thick b v :=
  ⟨honors _ _ X.branches E.paths (X.choice m) s, X.spat_stood h, X.thick_tr h⟩

omit h
structure Fronds {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (r : Y → Vault G m (X.up m)) (d : Y → Link G m)
    (b : Joint G m (X.up m)) (v : Config G m) : Prop where
  sr : ContDiffAt ℝ ω r 0
  v0 : r 0=0
  sd : ContDiffAt ℝ ω d 0
  d0 : d 0=0
  live : ∀ᶠ z in 𝓝 0, X.Stable (Stationary.extend (r z) * b) (input G m (d z) * v)

section fronds
variable {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
variable {r : Y → Vault G m (X.up m)} {d : Y → Link G m} (u : X.Fronds r d b v)

include h u
private lemma fronds_trail :
    ∀ᶠ z in 𝓝 0, ∀ x, fderiv ℝ (X.sitting b v) (r z,d z) (x,0) = 0 := by
  let g z := ((r z,d z):X.Hall m)
  have ho : g 0=0 := Prod.ext u.v0 u.d0
  have h' : ContDiffAt ℝ ω (X.sitting b v) (g 0) := ho.symm ▸ h
  filter_upwards [u.live, (u.sr.prodMk u.sd).continuousAt.tendsto.eventually (h'.eventually (by simp))] with z hz hh x
  have hip : Thaw (fun w : Vault G m (X.up m)=> Stationary.extend w * b) (r z) :=
    (Thaw.through contDiffAt_id).mul (Thaw.fixed _ _)
  have hc := ((hh.differentiableAt (by simp)).hasFDerivAt.comp
     (f:=fun w=> (w,d z)) (r z)
     ((hasFDerivAt_id _).prodMk (hasFDerivAt_const ..))).fderiv
  exact DFunLike.congr_fun (hc.symm.trans (Shell.chain hz hip rfl)) x

lemma fronds_bend (a:Y) :
    let x := fderiv ℝ r 0 a
    let y := fderiv ℝ d 0 a
    X.thick b v *ᵥ cash (helmets _ _ _) x + X.spat b v *ᵥ y = 0 := by
  dsimp only
  apply dotProduct_eq_zero_iff.mp; intro w
  obtain ⟨w,rfl⟩ := (cash (helmets G m (X.up m))).surjective w
  rw [dotProduct_comm]
  have ht := X.fronds_trail h u
  let g z := ((r z,d z):X.Hall m)
  have ho : g 0=0 := Prod.ext u.v0 u.d0
  have h' : ContDiffAt ℝ ω (X.sitting b v) (g 0) := ho.symm ▸ h
  have hh := riding (w,0) h' (u.sr.prodMk u.sd)
    (ht.mono fun z hz => (hz w).trans (ht.self_of_nhds w).symm) a
  rw [ho, X.full_charge h,
      ((u.sr.differentiableAt (by simp)).hasFDerivAt.prodMk
        (u.sd.differentiableAt (by simp)).hasFDerivAt).fderiv] at hh
  simpa only [zero_dotProduct,add_zero, ContinuousLinearMap.prod_apply] using hh

end fronds

abbrev Rest (r : Link G m → Vault G m (X.up m)) (b : Joint G m (X.up m)) (v : Config G m) :=
  X.Fronds r id b v

section rest
variable {r : Link G m → Vault G m (X.up m)} (u : X.Rest r b v)
include h u

lemma rest_coarse (x : Link G m) :
    X.thick b v *ᵥ cash (helmets _ _ _) (fderiv ℝ r 0 x) + X.spat b v *ᵥ x=0 := by
  simpa only [fderiv_id, ContinuousLinearMap.id_apply] using X.fronds_bend h u x

lemma rest_law :
    let C := billsM (pocket _) (helmets _ _ _) (fderiv ℝ r 0)
    damage (pocket _) (fun y => X.sitting b v (r y,y)) 0 =
    X.alto b v + (X.spat b v)ᵀ * C := by
  let g : Link G m → X.Hall m := fun y => (r y,y)
  have hg : g 0 = 0 := Prod.ext u.v0 rfl
  have hs : ContDiffAt ℝ ω (X.sitting b v) (g 0) := hg.symm ▸ h
  have hp := u.sr.prodMk u.sd
  let C := billsM (pocket _) (helmets _ _ _) (fderiv ℝ r 0)
  have hd := ((u.sr.differentiableAt (by simp)).hasFDerivAt.prodMk (hasFDerivAt_id (𝕜:=ℝ) 0)).fderiv
  apply damage_eq (pocket _); intro x y
  have hh := pay_second hs hp x y
  rw [detracts]
  refine hh.trans ?_;rw [hg]
  have ho : (iteratedFDeriv ℝ 2 g 0 ![x,y]).2=0 := by
    let L := ContinuousLinearMap.snd ℝ (Vault G m (X.up m)) (Link G m)
    rw [show (iteratedFDeriv ℝ 2 g 0 ![x,y]).2 = iteratedFDeriv ℝ 2 (L ∘ g) 0 ![x,y] from by
          rw [L.iteratedFDeriv_comp_left (f:=g) hp le_top];rfl,show L ∘ g=id from rfl,
        iteratedFDeriv_two_apply,show fderiv ℝ (id:Link G m → _)=_ from funext fun _=>fderiv_id ..]
    simp
  let V := iteratedFDeriv ℝ 2 g 0 ![x,y]
  have ht := (X.fronds_trail h u).self_of_nhds V.1
  rw [show (r 0,id 0)=((0):X.Hall m) from hg,← show V.2=0 from ho, Prod.eta] at ht
  change fderiv ℝ (X.sitting b v) 0 (iteratedFDeriv ℝ 2 g 0 ![x,y])=0 at ht
  change fderiv ℝ g 0 = _ at hd
  rw [ht,zero_add,hd, X.full_charge h,ContinuousLinearMap.prod_apply,
      ContinuousLinearMap.prod_apply,ContinuousLinearMap.id_apply,
      ContinuousLinearMap.id_apply]
  dsimp only
  rw [X.rest_coarse h u, dotProduct_zero,zero_add, Matrix.add_mulVec, ← Matrix.mulVec_mulVec,
      bill_at,cash_pocket,cash_pocket,add_comm]

omit h in
lemma Rest.stable : X.Stable b v := by
  have hu := u.live.self_of_nhds
  rw [u.v0, extend_zero,one_mul,id_eq,input_zero,one_mul] at hu
  exact hu

def schur (b : Joint G m (X.up m)) (v : Config G m) :=
  Det.schur (X.thick b v) (X.spat b v) (X.throat b v) (X.restored b)

lemma rest_schur (hw : Explosives (X.S m) (X.choice m) 1 b) (hk : IsUnit (X.high b v).det) :
    X.schur b v = damage (pocket _) (fun y => X.sitting b v (r y,y)) 0 + mail v*(mail v)ᵀ := by
  have hg := X.wort h (Rest.stable X u)
  rw [schur, X.rest_law h u,
    Det.schur_graph (stood (X.S m) b) (billsM (pocket _) (helmets _ _ _) (fderiv ℝ r 0))
      _ _ _ _ (by rw [X.restored_stood hw]; exact fund_det (grenade_safe _ X.hμ)) hg.1 hg.2.1 ?_ hk]
  · unfold throat;abel
  apply testers; intro x y
  rw [←cash_pocket y,Matrix.add_mulVec,← Matrix.mulVec_mulVec,bill_at,cash_pocket, X.rest_coarse h u, zero_mulVec]
end rest

end BlockTie
end ExactRunning
