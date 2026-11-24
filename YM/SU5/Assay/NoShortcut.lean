import SatinFixedContrastNovember4
import YM.SU5.Assay.FloorService
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4900
set_option maxHeartbeats 420000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
open Function Filter NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
variable {P:Spine}{j:Axis}{s v w:ℕ}{f g:P.Test}
local notation "Λ"=> P.par
local notation "Y"=> P.run
local notation "K"=> P.calibration
local notation "H"=> P.large
local notation "b"=> ruler (Λ).block
local notation "V"=> P.law
local notation "L"=> (Λ).R.L.val
local notation "π"=> P.history
local notation "Qt"=> P.projection.clipped
local notation "C₀"=> P.room j
local notation "σ"=> P.shifts j

local notation "μ"=> P.meanBox
local notation "ν"=> P.euclOp
local notation "T"=> P.shiftOp
local notation "Ν"=> whenly (timeMesh (Λ))
local notation "Ω"=> P.floorVec
local notation "S"=> enclave K
local notation "B" M:max=> bay K M true
variable {k:ℤ}{Z U D:Finset Cover}{x:P.Spectrum0 j}{a n r l:ℕ}{d δ:ℝ}
local notation "Q"=> P.viewFrom j a n w k f
local notation "E"=> P.E s
local notation "W"=> P.singleState j s x
local notation "m₀"=> P.period
local notation "h₀"=> P.cutoff
local notation "A"=>P.sterling s
open Aria Six Germ Alliance Set
/-!
 A payment on the declared chart on the regulators. No identification
 of bare separated prices by a *product* of ascended marks is needed;
 here support billing at precisely the claimed hosted resolution. The
 torus on the cone can be taken so ample that on this chart every
 relevant physical coordinate separation retains its value without
 shortcuts through periods, even for all points of poses & shields,
 on the estimates with viewers. Hospitality for the expended sites
 included as before. As in Satin we charge 1/(2ρ) units for Cover
 step on `More σ`; thus `(2σ)/(2ρ)` per period.
-/
local notation "σ₀"=>Journey.side Y (m₀ r) s
local notation "ρ"=>precisionAt (Λ) s
variable (P s r) in
def circuitMoney :ℝ:= (↑((σ₀).val):ℝ) / ρ
local notation "c"=> P.circuitMoney s
lemma circuitMoney.size (P:Spine)(s r:ℕ):(↑(More (side P.run (P.period r) s)).val:ℝ)/(2*precisionAt P.par s)=P.circuitMoney s r:=by
 let g:= (side P.run (P.period r) s).val; let t:=precisionAt P.par s
 change (↑(g*2:ℕ):ℝ) / (2*t)=(g:ℝ)/t
 push_cast; field_simp
variable(P s) in
lemma circuitMoney_tends : Tendsto (P.circuitMoney s) atTop atTop:=by
 let m:ℕ→Side:=fun r=>momentm Y (m₀ r) s
 let z:ℕ→ℕ:=fun r=>(side Y (m₀ r) s).val
 have u(r:ℕ): (m r).val≤z r:=by
    have h:(K).c (m r)=(side Y (m₀ r) s):= terrain Y H _ _
    change _≤ (side Y (m₀ r) s).val;rw [←h]
    unfold Calibration.c Vale.cell Vale.mesh
    rw [pow_zero,mul_one]
    change (m r).val ≤ (m r).val*2*((K).B).val
    exact (show ((m r).val)≤ (m r).val*2 by omega).trans (Nat.le_mul_of_pos_right _ (K).B.property)
 have q:Tendsto z atTop atTop:= tendsto_atTop_mono u ((raised Y s).tendsto_atTop.comp (V).pick.grow_i.tendsto_atTop)
 refine tendsto_atTop.mpr (fun b' => ?_)
 have ht:Tendsto (fun r=>(z r:ℝ)) atTop atTop:=tendsto_natCast_atTop_atTop.comp q
 exact (ht.eventually_ge_atTop (b' * ρ)).mono fun i h=>(le_div_iff₀ (positiveScale ..)).mpr h

abbrev ArcLimit (M:Set Vantage):Prop :=∃u:Vantage, ∀v∈M,∀i,|v i| ≤ u i
variable {M L':Set Vantage}
lemma ArcLimit.merge (p:ArcLimit M)(q:ArcLimit L'):ArcLimit (M∪L'):=by
 obtain ⟨u,t⟩:=p;obtain ⟨v,g⟩:=q
 refine ⟨fun i=>max (u i) (v i),?_⟩
 rintro _ (h|h) i
 · exact le_max_of_le_left (t _ h i)
 exact le_max_of_le_right (g _ h i)

lemma FrameFloor.arc (p:P.FrameFloor s M):ArcLimit M:=by
 choose a₁ b₁ k₁ w₁ y using p
 refine ⟨fun i=>max (-a₁ i) (b₁ i),fun v u i=> abs_le.mpr ?_⟩
 let h:=y i
 exact ⟨neg_le.mp (le_max_of_le_left (neg_le_neg (h.left.trans (h.buys v u).1))),le_max_of_le_right ((h.buys v u).2.trans h.right)⟩
local notation "Φ"=> P.pinFoot s
variable(P s Z) in
lemma pin_arc : ArcLimit (Φ Z):=by
 have t:= positiveScale (Λ) s
 induction Z using Finset.induction with
 | empty=>exact ⟨0,fun _ ⟨i,h,_⟩=> (Finset.notMem_empty _ h).elim⟩
 | @insert i A₀ u h=>
    rw [←Finset.singleton_union,P.pin_union]
    refine ArcLimit.merge ?_ h
    refine ⟨fun j=> (|((i j):ℝ)|+(K).ℓ)/(2*ρ),?_⟩
    rintro y ⟨x',v,p⟩ j
    rw [Finset.mem_singleton] at v;subst x'
    have z: |ρ*(2*y j)-(i j:ℝ)|≤(K).ℓ:=p j
    rw [le_div_iff₀ (by positivity:0<2*ρ), mul_comm,← abs_of_pos (by positivity:0<2*ρ),←abs_mul]
    rw [show 2*ρ*y j=(i j:ℝ)+(ρ*(2*y j)-(i j:ℝ)) by ring]
    exact (abs_add_le ..).trans (by linarith only [z])
-- no regulator shortcuts at this height
variable(P s) in
def Unfolds (M:Set Vantage)(r:ℕ):Prop:=∀i:Axis,∀y∈M,∀z∈M,∀t:ℤ,t≠0→|y i-z i| < |y i-z i+t*c r|
variable (P s) in
lemma ArcLimit.opens (p:ArcLimit M):∀ᶠ r in atTop,P.Unfolds s M r:=by
 obtain ⟨u,y⟩:=p
 refine eventually_all.mpr (fun i=>?_)
 filter_upwards [(P.circuitMoney_tends s).eventually_gt_atTop (4*u i)] with r e Y' p Z' q t h
 have hl:=abs_le.mp (y _ p i)
 have hr:=abs_le.mp (y _ q i)
 have v:|Y' i-Z' i|≤ 2*u i:= (abs_sub _ _).trans (by linarith only [y _ p i,y _ q i])
 have g:0< c r:=by linarith only [e, hl]
 rcases lt_or_gt_of_ne h with l|l
 · have w:(t:ℝ)*c r≤ (-1)*c r:=
    mul_le_mul_of_nonneg_right (by exact_mod_cast (show t≤ -1 by omega)) g.le
   exact lt_of_lt_of_le (by linarith only [hl,hr,e,w,v]) (neg_le_abs _)
 have w:c r ≤ (t:ℝ)*c r:=le_mul_of_one_le_left g.le (by exact_mod_cast (show 1 ≤ t by omega))
 exact lt_of_lt_of_le (by linarith only [hl,hr,e,w,v]) (le_abs_self _)

-- Add to the Flight at will, still eventual & everywhere on the cone.
lemma FloorService.carries (p:P.FloorService j s x M k w Z n δ a f U D d)(v:P.FrameFloor s M):
 ∀ᶠ i in atTop,P.Unfolds s (M∪Φ (U∪Z∪D)) i ∧∀l,legacy Y ((m₀) i) ((h₀) l)→ P.Flight j s x k w Z n δ a f U D i l:=
 ((v.arc.merge (P.pin_arc s _)).opens P s).and p.purchase
#print axioms FloorService.carries
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
