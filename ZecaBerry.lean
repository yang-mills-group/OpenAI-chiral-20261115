import ZecaUmbel
import ZecaNib
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
local notation "Λ"=> P.par
local notation "L"=> P.par.R.L
local notation "H"=>P.large
local notation "N" s:max i:max => Journey.side P.run i s
/-! # Buy height and travel together. Keep both actual calibration and rank resolution schedule. -/
open CF.Pannier.Chancel CF.Py.Rate.LocalLimit.Preparation.Yoke
open Worth Pays CF.BProof
open Real (log)
open Aria Casting MacroGrid
local notation "z'" => witnessZ
open Regis.Head.Etch Push.Local AnalyticBridge.VerifiedReset
local notation "Δ" t:max x:max => P.tariffQ z' t x
variable (x : P.Spectrum0 3)

local notation "ξ"=> P.advocate 3 x j
local notation "EH"=>P.physicalEnergy j ξ
local notation "M"=> P.ColorHil j ξ
local notation "Ω"=> P.colorZero j ξ
local notation "Μ"=> timeMesh P.par

variable (l: List Axis)
local notation "w"=>P.roseWide j s
local notation "Roof"=>P.rosePad j s
local notation "m" t:max=>P.gum w s t
local notation "ζ"=>P.roseRoot f s l
local notation "Y" t:max =>P.clockPlate s t ζ
local notation "zc" t:max => P.centeredQ x t (Y t)
local notation "D" t:max=> (P.basePlay x f t).pivot P l
local notation "X" t:max=> P.granPos f t l
local notation "R₀"=>P.roseHub f s l

local notation "G"=> P.ManyF j ξ
local notation "N₁"=> P.Nib j ξ
local notation "T" i:max=> (D i).realWidth P j
lemma berry_tight : Tendsto (fun v=> (T v)) atTop (𝓝 0):=by
 have h:Tendsto (fun v=> P.roomy*P.macroStep v) atTop (𝓝 0):=
  (mul_zero (P.roomy:ℝ)) ▸ (P.macroStep_zero.const_mul (P.roomy:ℝ)) -- f binder re-shadow?
 exact h.congr (fun i=> ((Apron.pivot_w j P _ l).trans (P.play_width x f i j)).symm)

-- o shift needed in ruby
lemma berry {a b:ℝ}
 (u:(T v) ≤ a-(X v) j)(v':(T v) ≤ b+(X v) j)
 (e:0≤a+(X v) j)(g:0≤b-(X v) j):
  P.dazzle j ξ (X v)
   (P.buff j ξ (a+(X v) j) (b-(X v) j)
   (P.crop j x f v l a b)) =
       P.ruby j ξ (D v) 0 (2*a) (2*b):=by
 unfold crop
 rw [P.ruby_large _ _ _ _ _
    (show a+(X v) j+(a-(X v) j)=2*a from by ring)
    (show b+(X v) j+(b-(X v) j)=2*b from by ring)
    e g u v',P.ruby_turn,add_neg_cancel]

variable {u:ℕ→ℕ}{c:ℕ→ℝ}
lemma berry_read (p:Tendsto u atTop atTop)
   {a b:ℝ}{V:(P.ManyF j ξ).Op}(ha:0<a)(hb:0<b)
   (q:Tendsto (fun i=>(c i:ℂ) • P.crop j x f (u i) l a b) atTop (𝓝 V)):
 Glaze_LocalFieldBounds (P.ManyF j ξ) atTop
     (fun i=>(c i:ℂ) • P.ruby j ξ (D (u i)) 0 (2*a) (2*b)) (P.buff j ξ a b V):=by
 let d(i:ℕ):= P.granPos f (u i) l
 have hd:Tendsto d atTop (𝓝 0):=(P.granPos_zero l).comp p
 have r':Tendsto (fun i=>d i j) atTop (𝓝 0) := tendsto_pi_nhds.mp hd j

 have h₁:=((Glaze_LocalFieldBounds.pops (U:=P.ManyF j ξ) q).buff (r'.const_add a) (r'.const_sub b)).dazzle hd
 rw [add_zero, sub_zero,P.dazzle_zero] at h₁
 have ds:= (P.berry_tight (f:=f) j x l).comp p

 have h₀ := (ds.add r').eventually (ge_mem_nhds (by simpa only [zero_add] using ha:0+0<a))
 have h₂ := (ds.sub r').eventually (ge_mem_nhds (by simpa only [sub_zero] using hb:0-0<b))
 refine h₁.congr' ?_
 filter_upwards [h₀,h₂,
    (r'.neg.eventually (ge_mem_nhds (show -(0:ℝ)<a from (neg_zero).trans_lt ha))),
    (r'.eventually (ge_mem_nhds hb))] with i h n y z
 let e:= (X (u i)) j
 change _ + e ≤ a at h
 change _ - e ≤ b at n
 exact ((congrArg _ (map_smul ..)).trans (map_smul ..)).trans (congrArg _ (P.berry _ _ _
    (le_sub_iff_add_le.mpr h) (sub_le_iff_le_add.mp n)
    (neg_le_iff_add_nonneg.mp (show -e ≤ a from y)) (sub_nonneg.mpr (show e≤b from z))))

lemma berry_bundle (p:Folding P x f u c) :
 ∃ F:P.Nib j ξ, NibLine P j ξ F (fun i=>D (u i)) (fun i=>(c i:ℂ)):=by
 choose! V h using p.charge j l
 let F:P.Nib j ξ:=fun a b=>P.buff j ξ (a/2) (b/2) (V (a/2) (b/2))
 refine ⟨F, ?_, (P.berry_tight (f:=f) j x l).comp p.goes,?_⟩

 · obtain ⟨B,d,np,ub⟩:=p.bill
   refine ⟨B*2^d,d,by positivity,?_⟩
   intro t e q
   have a:=half_pos e
   refine (P.buff_pay ..).trans ?_
   have v:=ub _ a (le_trans (half_lt_self e).le q)
   have i: ‖V (t/2) (t/2)‖≤ B / (t/2)^d:=le_of_tendsto (h _ _ a a).norm
                (v.mono fun i ht=> ht _ _ le_rfl le_rfl j l)
   rw [div_pow,div_div_eq_mul_div] at i; exact i
 intro a b e g
 have d:=P.berry_read _ _ _ p.goes (half_pos e) (half_pos g) (h _ _ (half_pos e) (half_pos g))
 rw [show 2*(a/2)=a by ring, show 2*(b/2)=b by ring] at d
 exact d
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
