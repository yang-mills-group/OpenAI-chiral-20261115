import YM.SU5.Aria.Miasma
import YM.SU5.Twilight.Hankel
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 220000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
namespace Spine
variable (P: Spine) (j:Axis) (x:P.Spectrum0 j)
local notation "T"=> P.par
local notation "X"=>P.ColorHil j x
open Aria Set TopologicalSpace Metric
local notation "ω"=> P.colorZero j x
local notation "M"=> timeMesh P.par
local notation "Γ"=> marks M
local notation "κ"=> P.voyageF j x
local notation "V" i:max=> ((κ).crew i).play
local notation "F"=> look j
local notation "v"=> P.visitors j x
local notation "S"=>P.seasons j x
local notation "A"=> P.Viewers j x
local notation "Ω"=> P.heaven j x
local notation "ω'"=> P.bank j x
local notation "ϑ"=> P.enter j x
-- spacetime for marks here uses fermion units (same ruler as `Flight`). Real Ranks in each coordinate arbitrary.
abbrev Vantage := Axis→ℝ
abbrev VMark := Axis→ (marks (timeMesh P.par))
local notation "Γ'"=> P.VMark
local notation "R"=> P.wealth j x
def laysM (r:Γ'): Vantage:= fun i=> (r i:ℝ)
abbrev VClose (r:Vantage)(δ:ℝ): Prop := ∀ i:Axis,|r i| < δ
def gentle (r:Vantage) (D:ℕ→ Mist P.VMark):Prop:=∀ e>0, ∀ᶠ i in atTop,(D i).holds (fun z=> VClose (P.laysM z-r) e)
lemma lays_add (a b:Γ'): P.laysM (a+b)=P.laysM a + P.laysM b:= rfl
lemma lays_zero : P.laysM 0=0:=rfl
lemma lays_neg (a:Γ') : P.laysM (-a)= -P.laysM a:=rfl
lemma vantage_near (g : Γ'): ContinuousAt (P.laysM) g := (continuous_pi_iff.mpr (fun i:Axis=> continuous_subtype_val.comp (continuous_apply i))|>.continuousAt)
lemma marksDense:DenseRange P.laysM:= DenseRange.piMap fun i:Axis=>(daylight M).denseRange_val
-- actors
abbrev truck (y:P.VMark) : (P.ColorHil j x).Op:= (κ).raw (look j) (y ∘ Subtype.val)
lemma truck_norm (y:Γ')(b:X): ‖P.truck j x y b‖=‖b‖:=by
  let p:= y ∘ (Subtype.val : Trans j→Axis); change ‖(κ).raw F p b‖=_; generalize F=L; induction L with
  | nil=> rfl
  | cons i L ih=> rw [raw_step,ContinuousLinearMap.comp_apply,Players.wins,ih]
lemma truck_pay (y:Γ'): ‖P.truck j x y‖≤1:=ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun b=> by rw [P.truck_norm,one_mul])
lemma truck_zero : P.truck j x 0=ContinuousLinearMap.id ℂ _:= (κ).raw_zero F
lemma truck_paves (y z: Γ'): P.truck j x (y+z)=(P.truck j x y).comp (P.truck j x z):= (κ).travelR ..
lemma truck_commutes (y z:Γ'): (P.truck j x y).comp (P.truck j x z)= (P.truck j x z).comp (P.truck j x y):= by rw [←P.truck_paves,←P.truck_paves,add_comm]
lemma truck_empty (y:Γ'): P.truck j x y (P.colorZero j x)=P.colorZero j x:=by
  unfold truck; generalize look j=L; induction L with
  | nil=>rfl
  | cons t L i=>rw [raw_step,ContinuousLinearMap.comp_apply,i,P.colorFresh]
lemma truck_inner (y:Γ')(u a:X): inner ℂ (P.truck j x y u) a= inner ℂ u (P.truck j x (-y) a) := by
 let U:=P.truck j x; let U₀:= (show (P.ColorHil j x).space →ₗᵢ[ℂ] (P.ColorHil j x).space from {(U y).toLinearMap with norm_map':= P.truck_norm j x y })
 have hv: U₀ (U (-y) a)=a:=by
   change P.truck j x y (P.truck j x (-y) a)=a; rw [←ContinuousLinearMap.comp_apply,P.truck_paves j x y (-y)|>.symm,add_neg_cancel,P.truck_zero]; rfl
 exact (congrArg (inner ℂ (U₀ u)) hv.symm).trans (U₀.inner_map_map ..)

-- real
abbrev cartage (y:Vantage) : (P.ManyF j x).Op:= Alliance.aviation (P.voyageF j x) (daylight (timeMesh P.par)) (look j) (y ∘ Subtype.val)
lemma cart_paves (a b:Vantage): P.cartage j x (a+b)=(P.cartage j x a).comp (P.cartage j x b):= (Alliance.aviation_group ..).symm
lemma cart_zero : P.cartage j x 0=ContinuousLinearMap.id ℂ _ := Alliance.aviation_zero ..
lemma cart_cont (a:P.ManyF j x): Continuous (fun y:Vantage=>P.cartage j x y a):= Alliance.aviation_cont (κ) (daylight M) F (fun y:Vantage=> y ∘ Subtype.val) (fun i _=> show Continuous (fun y:Vantage=> y (i:Axis)) from continuous_apply _) a
lemma cart_norm (r:Vantage)(a:P.ManyF j x): ‖P.cartage j x r a‖=‖a‖:=Alliance.aviation_unit ..
lemma cart_and (y:Γ')(a:P.ManyF j x): P.truck j x y (ϑ a)=ϑ ((P.cartage j x (P.laysM y)) a):= by
  let p : Trans j→Γ := y ∘ Subtype.val
  let r:= transverse j (fun i=> (p i:ℝ))
  exact (congrArg (fun z:(P.ManyF j x).Op=>ϑ (z a)) (P.sails_smooth j x (fun i=> (p i:ℝ))).symm |>.trans (P.lift_motions j x p a)).symm
variable (ρ : P.Register)
include ρ
lemma colorPopulation : SeparableSpace (P.ColorHil j x).space:=by
 haveI: SeparableSpace (P.Slabs j):= P.slabs_separable j ρ
 haveI: SecondCountableTopology (P.Slabs j):=inferInstance
 haveI: SeparableSpace (P.Physical j):=inferInstanceAs (SeparableSpace ↥(P.neutralSlabs j : Set (P.Slabs j)))
 let φ:=P.restrictPortion j x
 exact (gns_dense φ).separableSpace (gns_operator_cont φ)
omit ρ
-- book with χ harmonized all axes once
abbrev advocate (k:Axis):= P.otherSpectrum j k x
structure Ellis : Type where
 mistT : ℕ→ Mist (VMark P)
 owned: P.gentle 0 mistT
 shaky(k:Axis)(x₁: P.ColorHil k (P.advocate j x k)): Tendsto (fun i=> (mistT i).mean (fun g=>P.truck k (P.advocate j x k) g x₁)) atTop (𝓝 (P.enter k (P.advocate j x k) (P.wealth k (P.advocate j x k) x₁))) -- v notation collision
include ρ
lemma ellisP : Nonempty (P.Ellis j x):=by
 let Z₀:= Σ i:Axis, Trans i; let H(z:Z₀):=P.ColorHil z.1 (P.advocate j x z.1); let U(i:Axis):=P.voyageF i (P.advocate j x i); let J(z:Z₀):Players (marks (timeMesh P.par)) (H z):=(U z.1).crew z.2
 haveI(z:Z₀): SeparableSpace (H z).space:= P.colorPopulation z.1 _ ρ
 obtain ⟨K,h₁,h₂⟩:=worldP J; let D(i:ℕ):=climate (K i) Vacancy.ordinate
 refine ⟨D,fun e q=> (h₁ e q).mono (fun i z=> ?_),fun k y=> ?_⟩ -- maybe Nonempty got projected wrong
 · exact (D i).promotes (fun a p=>by simp only [sub_zero]; exact p) (held_at (K i) Vacancy.ordinate Vacancy.ordinate_one z)
 let x':=P.advocate j x k; let t:= look k
 have eat: Tendsto (fun i=> projected (K i) (U k) t y) atTop (𝓝 ((U k).stackS t y)):= translated (U k) t K (fun i _ z=>h₂ ⟨k,i⟩ z) y
 apply eat.congr; intro n; let L:=K n; let r(g:Γ'):= P.truck k x' g y
 change (projected L (U k) t) y=(climate L Vacancy.ordinate).mean r
 rw [climate_perm _ _ _ (Vacancy.normal k)]; exact (normaliaz L (U k) Subtype.val Subtype.val_injective t (look_one k) k (fun i _=>Ne.symm i.property) y).symm
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.ellisP
