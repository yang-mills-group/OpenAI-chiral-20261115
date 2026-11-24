import ZecaWrack
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 250000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry

open TopologicalSpace
namespace Spine
open Lamour.Bridge.Celeste
open Lamour.Bridge.Celeste.Morn
open Py.Rate.LocalLimit.Papal (Weaver household)
open TopologicalSpace Tapestry.Exhibition
variable (P:Spine)(R : P.Register)(j:Axis)
local notation "φ"=> P.groundZero j
local notation "μ"=> P.pillars j
local notation "W"=> P.calibration
local notation "Q"=> P.par.block
local notation "ℓ"=> P.calibration.ℓ
open Papal Regis.Head Gleam
/-! # Price of ensemble-of-trips. Exactly composed on printed test level before estimation. -/
open Clock Clock.Hookah Clock.Hookah.Blaze
open Preparation.Yoke Yoke.Travel Regis.Head.Garland
open QuadClock Again Pressure
variable {s t f r v i k:ℕ}
local notation "Y"=> P.run
local notation "Λ"=> P.par
local notation "L"=> P.par.R.L
local notation "H"=>P.large
local notation "F" s:max=>hat P.par.R.L P.par.x s
local notation "N" s:max i:max => Journey.side P.run i s
/-! # Buy height and travel together. Keep both actual calibration and rank resolution schedule. -/
open CF.Pannier.Chancel CF.Py.Rate.LocalLimit.Preparation.Yoke
open Worth Pays CF.BProof
open Real (log)
open Aria Casting MacroGrid
open YM.Stationary (Gaia)
open CF.Onyx (riseX moor)

local notation "z'"=> Yoke.witnessZ
local notation "κ"=>P.sidesPerTick
local notation "κz"=> (P.sidesPerTick:ℤ)


variable (α β:Bool)
def thyme (d:Bool)(r:ℕ)(f:ℕ):Cover:=
  if d then opposeQ 3 (P.granule (P.megaK f r)) else P.granule (P.megaK f r)
abbrev carbcrownPose (α:Bool)(f r:ℕ)(p:Plume_LocalFieldBounds)(b:Cover):Cover:=
 P.thyme α r f + κ • (P.spacedPitch r p + b)
variable (f)(p q:Plume_LocalFieldBounds)(a b:Cover)(W₀:5∣P.par.R.L.val)
lemma thyme_t : Tendsto (fun r=>(P.thyme α r f j:ℝ)/P.jetR r) atTop (𝓝 0):=by
 let err0 r:= P.persistN (P.megaK f r)
 have hu(r):0≤ (err0 r:ℝ):= (P.tiny_one_ledger r _).1
 have hl:Tendsto (fun r=>(err0 r:ℝ)/P.jetR r) atTop (𝓝 0):=
    squeeze_zero (fun r=> div_nonneg (hu r) (P.jetR_pos r|>.le))
    (fun r=> div_le_div_of_nonneg_right (P.tiny_one_ledger r _).2 (P.jetR_pos r |>.le))
       (tendsto_const_nhds.div_atTop (a:=(P.echoFoot:ℝ)) P.jetR_go)
 suffices v:(fun r=>(P.thyme α r f j:ℝ)/P.jetR r)=(fun r=>(err0 r:ℝ)/P.jetR r) ∨
      (fun r=>(P.thyme α r f j:ℝ)/P.jetR r)=(fun r=>-((err0 r:ℝ)/P.jetR r)) by
   rcases v with e|e
   · rw [e];exact hl
   rw [e]
   simpa only [neg_zero] using hl.neg
 cases α
 · exact Or.inl (by funext r;unfold thyme; rw [if_neg ((by decide):¬false=true)])
 by_cases n:j=3
 · right;funext i
   unfold thyme; rw [if_pos rfl]
   simp only [opposeQ,mirrorΩ,if_pos n, Int.cast_neg,neg_div]
   rfl
 left;funext r
 unfold thyme;rw [if_pos rfl]
 simp only [opposeQ,mirrorΩ,if_neg n]
 rfl

include W₀
lemma carbgrain : Tendsto (fun r:ℕ=> (P.carbcrownPose α f r p a j:ℝ)/P.jetR r) atTop (𝓝 (p.pose j)):=by
 let err r:= P.thyme α r f j
 have hu':Tendsto (fun r=>(err r:ℝ)/P.jetR r) atTop (𝓝 0):=P.thyme_t j f α
 have he:= tendsto_const_nhds.div_atTop 
     (a:=((κ:ℝ)*(a j))) P.jetR_go
 have hz:Tendsto (fun r:ℕ=> ((err r:ℝ)/P.jetR r+(p.pose j))+(κ:ℝ)*a j/P.jetR r)
    atTop (𝓝 (p.pose j)):=by simpa only [zero_add,add_zero] using (hu'.add_const (p.pose j)).add he
 refine hz.congr' ?_
 filter_upwards [P.spaced_prepare W₀ p] with r g
 have hp:(P.carbcrownPose α f r p a j:ℝ)= (err r:ℝ)+(κ:ℝ)*(p.pose j*P.plannedK r+a j):=by
   have he : P.carbcrownPose α f r p a j=
     err r+ (κ:ℤ)*(P.spacedPitch r p j+a j):=by
     rw [carbcrownPose,Pi.add_apply,Pi.smul_apply,nsmul_eq_mul,Pi.add_apply]
   conv_lhs => rw [he]; simp only [Int.cast_add,Int.cast_mul,Int.cast_natCast,g]
 rw [hp]
 let u:=err r
 let v:=p.pose j
 let V:=P.jetR r
 change ((u:ℝ)/V+v)+(κ:ℝ)*a j/V = ((u:ℝ)+(κ:ℝ)*(v*P.plannedK r+a j))/V
 rw [mul_add,show (κ:ℝ)*(v*P.plannedK r)=v*V from by unfold V jetR; ring,add_div,add_div]
 have hv:0<V:=P.jetR_pos r
 field_simp
 ring

local notation "e" r:max=>P.carbcrownPose α f r p a
local notation "θ" r:max=> opposeQ 3 (P.carbcrownPose α f r p a)
local notation "d" r:max=>P.carbcrownPose β f r q b
local notation "Jr" => P.jetR
lemma carbbend : Tendsto (fun r=>riseX (Jr r) (d r - θ r)) atTop (𝓝 (tendril p q)):=by
 have hv(j:Axis): Tendsto (fun r=> (((θ r) j):ℝ)/(Jr r)) atTop (𝓝 (if j=3 then -(p.pose j) else p.pose j)):=by
   simp only [opposeQ,mirrorΩ]
   by_cases h:j=3
   · simp only [h,if_true,Int.cast_neg,neg_div]
     exact (P.carbgrain 3 f α p a W₀).neg
   rw [if_neg h]
   simp only [if_neg h]
   exact (P.carbgrain j f α p a W₀)
 have hw(j):= (P.carbgrain j f β q b W₀).sub (hv j)
 refine (PiLp.continuous_toLp 2 _).continuousAt.tendsto.comp
     (f:=fun r:ℕ=>fun j:Axis=>↑((d r-θ r) j)/((Jr r):ℝ)) (tendsto_pi_nhds.mpr ?_)
 intro j; simp only [Pi.sub_apply,Int.cast_sub,sub_div]
 exact hw j

-- Eligibility cost: divide by Kv_r and bound using carbgrain.
open Regis.Circuit
omit W₀ in
private lemma carbceiling_c' {c:ℝ} (h:P.depthCap<c)(A:ℝ) (hp:0≤A):
 ∀ᶠ r:ℕ in atTop,A*(P.plannedK r)≤ scout P.par c r:=by
 have h₁ := (turnover P.par).eventually (leap (p:=c) (w:=0) (q:=0)
   (f:=fun x:ℝ=> A* ((↑(L).val:ℝ)*trailℓ P.depthCap x))
    (Pays.scale _ (Pays.scale _ (Pays.whole 0 P.depthCap 0))) (Or.inr (Or.inl ⟨rfl,h⟩)))
 filter_upwards [h₁,P.planned_ceiling] with r t v
 exact (mul_le_mul_of_nonneg_left v hp).trans (t.trans (Nat.le_ceil _))

lemma carbcrown_elig {c:ℝ} (h:P.depthCap<c):
 ∀ᶠ r:ℕ in atTop,∀ j:Axis,(P.carbcrownPose α f r p a j).natAbs ≤ scout P.par c r:= by
 refine eventually_all.2 fun j=>?_
 let X:= |p.pose j|+1
 filter_upwards [(P.carbceiling_c' h (X*κ) (mul_nonneg (show 0≤ X by unfold X; positivity)
      (Nat.cast_nonneg _))), (P.carbgrain j f α p a W₀).abs.eventually (ge_mem_nhds
           (show |p.pose j|< X from lt_add_one _))] with r w z
 let n:=P.carbcrownPose α f r p a j
 have p0:|((n:ℝ)/P.jetR r)|≤X:=z
 rw [abs_div,abs_of_pos (P.jetR_pos _)] at p0
 have h' :=((div_le_iff₀ (P.jetR_pos r)).mp p0).trans (le_trans
    (le_of_eq (mul_assoc X (κ:ℝ) (P.plannedK r)|>.symm)) w)
 have e' : |n|≤ (scout P.par c r : ℤ):= by exact_mod_cast h'
 exact Int.ofNat_le.mp (show (n.natAbs:ℤ)≤ _ from by rwa [Int.natCast_natAbs])

omit W₀ in
private lemma carbopposed_natAbs (x:Cover)(j:Axis):
   (opposeQ 3 x j).natAbs=(x j).natAbs:=by
 simp only [opposeQ,mirrorΩ]
 split
 · subst j; rw [Int.natAbs_neg]
 rfl

omit W₀ in
private lemma carbapproved_bend (x y:Cover)(n:ℕ)
 (f:∀ j,(x j).natAbs ≤n)(g:∀ j,(y j).natAbs≤n):
 CoversT (twinTrip y (opposeQ 3 x)) n:=by
 intro m j
 cases m with
 | true=> exact g j
 | false=> 
    change (opposeQ 3 x j).natAbs ≤ _
    rw [carbopposed_natAbs]
    exact f j

lemma carbbending_cost {c:ℝ} (h:P.depthCap<c):
 ∀ᶠ r:ℕ in atTop,CoversT (twinTrip (d r) (θ r)) (scout P.par c r):=by
 filter_upwards [P.carbcrown_elig f α p a W₀ h,P.carbcrown_elig f β q b W₀ h] with r hp hq
 exact carbapproved_bend (e r) (d r) _ hp hq

abbrev carbbendMiss (r:ℕ) (x:P.Spectrum0 3) := P.mistake 3 z' r (Jr r) (d r) (θ r) (tendril p q) x

#print carbbendMiss

variable {C:ℝ}
 (A₀:∀ᶠ s in atTop,∀ᶠ i in atTop,∀ k:ℕ,(P.run.voyage i).kick ≤ k → s ≤ P.run.uv k → ShelterCost C P.run s i k)

include W₀ A₀
lemma carbbending_go :
 Tendsto (fun r:ℕ=>∫ x,P.carbbendMiss f α β p q a b r x∂P.pillars 3) atTop (𝓝 0):=by
 let t:=8*P.depthCap+1; have hp:=P.depthCap_pos; let A:=14+2*t; let v:= P.depthCap+6*A+2*t+1
 have ht:0<t:=by unfold t; linarith only [hp]
 have hV:P.depthCap < v:=by unfold v; unfold A; linarith only [ht]
 exact P.mistake_go 3 z' A t v A₀ P.jetR_pos P.jetR_go (P.carbbend f α β p q a b W₀) (tendril_live p q)
    (P.carbbending_cost f α β p q a b W₀ hV) (P.planned_heatCost t (lt_add_one _))
    (by unfold A; linarith) ht (by unfold v; linarith only [hp])

omit W₀ A₀
#print axioms carbbending_go
