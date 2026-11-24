
import ZecaMosaic
import ZecaBraid
import ZecaClover
import SatinThinErie
import SatinThinHalo
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 500000
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
/-! # Train cost comparison on elected printed heights. -/
-- support of tested pair. Need dSpacing condition eventually at roots. Using real checkpoint geometry. Only prices here. 
variable (X:Cover){C e A:ℝ}{d:ℕ}
open CF.Pannier.Chancel CF.Py.Rate.LocalLimit.Preparation.Yoke
local notation "aK"=>P.nomadic
local notation "bK"=>P.engine
set_option linter.unusedSectionVars false
-- One common regulator convergence workflow. P HERE chosen Station. 

set_option maxHeartbeats 850000

variable {b :ℝ}{δ:ℕ→ℝ}{κ:ℕ→ℕ}(K:lender A C f r v δ b κ P)

abbrev gum(S:Spine)(u f t:ℕ):= S.par.R.L.val^(t-f)*u
-- gummy calibration
-- -- hmmm don't, clashes local
structure Odessa(j:Axis)(X:Cover)(f w:ℕ)(P:Spine):Prop where
 pos:0<w
 lower:Plans j X f P
 upperD: nodeC X j+ P.labW f ≤ ruler P.par.block * w
 upperT: nodeC X j+ ((frameRadius j:ℤ)+(P.calibration.ℓ:ℤ)) ≤ ruler P.par.block * w
 sizes:plusAgain P.par.block (P.labW f) ≤ 2*spanSites P.par.block w
 rent:14* Worth.meterC (hat P.par.R.L P.par.x f) * (((8*spanSites P.par.block w:ℕ):ℝ))^4 ≤ 1

variable {w:ℕ}(g:Odessa j X f w P)

local notation "bx" s:max=>P.clockPlate f s X
local notation "πx" s:max=>frameOne (bx s)
local notation "vx" s:max=>(P.visitOne s (bx s)).val
local notation "Rx" s:max=>ruler P.par.block*(P.gum w f s)
lemma gum_pos (h:0<w):0<gum P w f v:= Nat.mul_pos (pow_pos P.par.R.L.property _) h
lemma gum_step (u:f≤r)(t:r≤v): P.par.R.L.val^(v-r)*gum P w f r=gum P w f v:=by
 unfold gum; rw [←mul_assoc,←pow_add,show v-r+(r-f)=v-f from by omega]
include g
lemma seed_color:
 Cardigan.InBend j 0 (ruler P.par.block*w) (P.labW f)
   (node (P.rootAt f i X)):=by
 unfold rootAt; rw [node_of]
 exact ⟨nodeC X j,rfl,by rw [zero_add]; exact g.lower.seat,g.upperD⟩

lemma olive:
 Between P.calibration j 0 (Rx s) (πx s):= by
 intro i hi
 refine ⟨P.frame_rise j X g.lower i hi,?_⟩
 obtain ⟨_,_,u⟩:= mem_biUnion.mp hi
 obtain ⟨y,p,rfl⟩:= mem_image.mp u
 have h:(y j).natAbs ≤ frameRadius j:= Finset.le_sup (f:=fun x:Cover=> (x j).natAbs) p
 have a:= g.upperT
 let z:= P.par.R.L.val^(s-f)
 have q: 1≤ (z:ℤ):=by exact_mod_cast (Nat.succ_le_of_lt (pow_pos P.par.R.L.property _))
 let D:ℤ:=(frameRadius j:ℤ) + (P.calibration.ℓ:ℤ)
 have az:=(add_le_add_left
      (le_mul_of_one_le_left (show 0≤ D from by unfold D; positivity) q)
       ((z:ℤ)*nodeC X j)).trans (show _≤(z:ℤ)*(ruler P.par.block*w) from by
           rw [←mul_add, add_comm D]; exact mul_le_mul_of_nonneg_left a (by omega))
 change y j + (z • nodeC X) j + (P.calibration.ℓ:ℤ)
    ≤ ruler P.par.block*((↑(z*w)):ℤ)
 rw [Pi.smul_apply,nsmul_eq_mul, Nat.cast_mul,mul_left_comm]
 unfold D at az; omega


local notation "aζ" i:max=> P.nomadic (κ i)
local notation "kζ" i:max=> P.engine (κ i)
local notation "Kζ"=> tent P.run P.large
omit g
include K
lemma odessa_pos:0<violet P.par f A:=by
 obtain ⟨_,_,t⟩:= K.treasury.room.exists
 exact violet_pos P.run _ _ t
include g
lemma sparse_floret:
 ∀ᶠ i:ℕ in atTop, ∀ y:Ferry P.run r (aζ i) (kζ i),
   SparseAt P.run P.large r (aζ i) (kζ i) y j (P.gum w f r) (vx r) (fareMin P.par.R.L (r-f)*violet P.par f A):=by
 set n:=P.nomadic ∘ κ; set k:=P.engine ∘ κ
 let hp:=K.treasury.price.le
 filter_upwards [K.earn.tendsto_atTop.eventually K.treasury.room] with i t y
 let ctr:= P.rootAt f (n i) X; let V:= (RootBook Y (n i) (k i) f).p.B
 have hV: V=P.thresholdF f:= (congrArg BudgetPoint.B
     (Papal.prices_plot P.run f (n i) (k i) (hp.trans y.enters)).1)
 have hx:
  distribute Y H r (n i) (vx r) = Yoke.principal Y (n i) (k i) hp 1 ctr:=by
   have e:=P.eerieT (P.high_root hp (i:=aK (κ i)) X).symm y.enters 1
   rw [Complex.ofReal_one,one_smul] at e; exact e
 refine ⟨_,_,_,_,_,_,_,_,_,ctr, g.pos,
     pow_pos P.par.R.L.property _,rfl,odessaScale Y _ hp,
     violetGrace Y _ _ hp (κ:=P.thresholdF f) P.large y, g.sizes,hx,
     P.seed_color j X g, fun l h N₀=>?_⟩
 let z:=t.1.Q.part P.run _ _ (le_refl f) hp K.treasury.step
 have v':PaysTilt P.run (n i) (k i) f r r A:=
     cost_delivers P.run _ _ le_rfl K.treasury.price z
 apply violet_principal Y _ _ hp l t.2 (8*spanSites _ _) g.rent N₀ v'
 change outdoor (rural V) l; rw [hV]; exact h

lemma sparse_gap:
 ∀ᶠ i:ℕ in atTop, ∀ y:Ferry P.run v (aζ i) (kζ i),
   SparseAt P.run P.large v (aζ i) (kζ i) y j (P.gum w f v)
     (P.bookT (κ i) f r v (δ (κ i)) X) (violet P.par f A):=by
 let n:=P.nomadic ∘ κ; let k:=P.engine ∘ κ
 let hp:=K.treasury.price.le; let hz:=K.treasury.step
 filter_upwards [K.earn.tendsto_atTop.eventually K.treasury.room,
   K.earn.tendsto_atTop.eventually K.pays,
   K.earn.tendsto_atTop.eventually (P.touring_fee X hp hz)]
    with i t β r₀ y
 obtain ⟨b',z',t',_,D,e⟩:= β.2; rw [e]
 let ctr:=P.rootAt f (n i) X
 refine ⟨_,_,_,_,_,_,_,_,_,ctr, g.pos, pow_pos P.par.R.L.property _,rfl,
      odessaScale Y _ (hp.trans hz),
      shrubGrace Y _ _ hp hz (κ:=P.thresholdF f) P.large y,
      g.sizes,r₀ b' z',P.seed_color j X g,fun l h N₀=>?_⟩
 apply violet_gap Y _ _ hp hz l t.2 (8*spanSites _ _) g.rent N₀ D
 let V:= (RootBook Y (n i) (k i) f).p.B
 change outdoor (rural V) l
 rw [show V=P.thresholdF f from congrArg BudgetPoint.B (Papal.prices_plot P.run f _ _ ((hp.trans hz).trans y.enters)).1]
 exact h

local notation "D"=> P.projection.refine
def odessaGap(P:Spine)(f r v:ℕ)(X:Cover)(b:ℝ):Family P.calibration :=
 (↑(zoomM P.par.R.L^(r-f)):ℂ) •
  ((b:ℂ) • (P.visitOne v (P.clockPlate f v X)).val-
   stream P.run P.large P.projection.refine r (v-r) (P.visitOne r (P.clockPlate f r X)).val)
-- B1: gap mosaic for ANY mean entry equal to this prospect
local notation "Tζ" s:max=>Entry Y H s j false (P.gum w f s)
local notation "QV"=>P.projection.clipped
local notation "B" s:max elt:max=>boxOp P.run P.large P.law s P.history QV j false (P.room j) _ elt (P.gum_pos g.pos)
variable (O:P.NightCop)
include O
lemma norm_odessa_floret
 (Z:Tζ r) (h:Z.val.val=vx r):
 ‖B r Z‖ ≤ 2*(fareMin P.par.R.L (r-f)*violet P.par f A):=by
 apply mosaic_norm Y H P.law _ P.history QV j false (P.room j)
   _ Z _ K.earn O (P.olive j X g) ?_ ?_ (P.sparse_floret j X K g)
 · rw [h]; exact stayQueue Y H P.basesT
 · unfold fareMin
   have hℒ: (0:ℝ)<P.par.R.L.val:=by exact_mod_cast P.par.R.L.property
   exact mul_pos (by positivity) (P.odessa_pos K)

lemma norm_odessa_gap(Z:Tζ v)(h:Z.val.val = P.odessaGap f r v X b):
 ‖B v Z‖≤2*violet P.par f A:=by
 let he(t:ℕ): InTest W true (πx t) false (vx t):=P.basesT
 let s₀:=πx v; let t₀:= volumeAround Λ P.width (v-r) (πx r)
 let S:= s₀∪ t₀
 have ht: Between W j 0 (Rx v) S:=by
   have a: Between W j 0 (Rx v) t₀:=by
      have q:=expands_shape Y H (P.olive j X (s:=r) g) (v-r)
      rw [←P.gum_step K.treasury.price.le K.treasury.step,
           Nat.cast_mul,Nat.cast_pow, mul_left_comm]; exact q
   intro y p; rcases mem_union.mp p with h|h
   · exact P.olive j X g y h
   exact a y h
 apply mosaic_norm Y H P.law _ P.history QV j false (P.room j)
   _ Z _ K.earn O ht ?_ (P.odessa_pos K) (P.sparse_gap j X K g)
 rw [h]
 exact (( (stayQueue Y H (he v)).scale
     (Complex.continuous_ofReal.continuousAt.tendsto.comp K.future)).subtract
   ((queue_easy Y H P.law r P.history _ _ (he r) (v-r)).reindex K.earn.tendsto_atTop)).scale tendsto_const_nhds

end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.norm_odessa_gap
