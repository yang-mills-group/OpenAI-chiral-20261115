import YM.SatinExist.Glacis
import SatinThinSegno

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
/-! # Train cost comparison on elected printed heights. -/
-- support of tested pair. Need dSpacing condition eventually at roots. Using real checkpoint geometry. Only prices here. 
variable (X:Cover){C e A:ℝ}
open CF.Pannier.Chancel CF.Py.Rate.LocalLimit.Preparation.Yoke
local notation "aK"=>P.nomadic
local notation "bK"=>P.engine
set_option linter.unusedSectionVars false
variable {d x y:ℝ}{ε T₁:ℕ}(w:ℕ)
local notation "ν" v:max=> Journey.side Y i v
noncomputable def longtruck (w f v:ℕ) := P.par.R.L.val^(v-f)*w
lemma risingtruck (w:ℕ){f v:ℕ}(p:0<w):0< P.longtruck w f v:= Nat.mul_pos (pow_pos P.par.R.L.property _) p
-- era registration. must pay NP.On banner using clock DOT conventions.
open SlabMark.Biscuit
-- transport identity & exact torus bill, no BQueue used at this step. stamps apply family reader. 
lemma single_banner {f v i k:ℕ}(F:Site (side P.run i f)→Mark (side P.run i v))(R:Family P.calibration)(g:Ferry P.run v i k)(p:f≤v){n:ℕ}(hw:0<w)(h1:0<n)
   (D: GraceA P.par.block ε T₁ F (solder P.run i k g.depth v) (highTurn P.par f v) P.calibration.ℓ)
   (S:TestFamily P.calibration true R)
   (a:Biscuit.Foot j X F ε T₁ 0 (ruler P.par.block*w) (distribute P.run P.large v i) 1 R)
   (b:∀ l:List (Site (side P.run i f)),outdoor T₁ l → ‖Journey.compass P.run i k v (l.map F).prod‖ ≤ x^l.length * Real.exp (y*((More (side P.run i f)).val:ℝ)^4))
   (c:∀ l:List (Site (side P.run i f)), Envelope (l.map F).prod)
   (u:pay R d)
   (hx:0<x)(hy:0≤y)
   (B: d*(16/truckBill P.par.block w ε x y) ≤ ((side P.run i v).val:ℝ))
   (e:IcePlot P.run v i k)
   (y':plusAgain P.par.block ε ≤ (side P.run i f).val)
   (g₀:2*(ruler P.par.block*P.longtruck w f v*n) ≤ ((side P.run i v).val:ℤ))(g₁: ((side P.run i v).val:ℤ) ≤ 4*(ruler P.par.block*P.longtruck w f v*n)):
   ∀ z:ℤ, ‖hot P.run P.large v i k (SlabMark.banner j (P.longtruck w f v) ((P.longtruck w f v:ℕ)*z) n R)‖ ≤ ((2*truckBill P.par.block w ε x y)^2)^(2*n):=by
 intro z
 let T:=distribute Y H v i; let u0:=solder Y i k g.depth v; let f':ℕ:=(L).val^(v-f); have he:0<f':=pow_pos (L).property _
 let N:=Journey.side P.run i v; let R':= SlabMark.banner j (P.longtruck w f v) ((P.longtruck w f v:ℕ)*z) n R
 have κ:(side Y i v).val=f'*(side Y i f).val:=by rw [←refine_side Y, Nat.add_sub_of_le p] -- tune defeq let f'
 have Hq:P.longtruck w f v=f'*w:=rfl; have hz:0<(w:ℤ):=by exact_mod_cast hw
 let W₀:=distribute_arith Y H v i
 rw [Hq,κ] at g₀ g₁; zify at g₀ g₁; push_cast at g₀ g₁; -- loop
 have Hg:2*(ruler P.par.block*w*(n:ℕ)) ≤ ((side Y i f).val:ℤ):= by
    apply le_of_mul_le_mul_left _ (show 0<(f':ℤ) by exact_mod_cast he); exact g₀.trans' (le_of_eq (by ring))
 have Ht: (side Y i f).val ≤ (4*n)*(16* P.par.block.val*w):=by
    let k:=4*(ruler P.par.block * w * n); have Hc: ((side Y i f).val:ℤ) ≤ k:=by apply le_of_mul_le_mul_left _ (show 0<(f':ℤ) by exact_mod_cast he); apply g₁.trans_eq; unfold k; ring
    zify; push_cast; exact Hc.trans_eq (by unfold k ruler Preparation.block; push_cast; ring)
 obtain ⟨l,o,hv,h'_0,q⟩:= Biscuit.trail D j (w:ℕ) hz X f' (fun k=> by unfold highTurn f'; rw [Nat.cast_pow]) T (fun f g=>(W₀ _ _ 0).2.1) (W₀ 1 1 1).2.2.2.1 (fun s F=>(W₀ F F 0).2.2.2.2 _ _) a Hg ((w:ℤ)*z)
 have v':T R'= (l.map F).prod:=by unfold R'; rw [Hq]; push_cast; rw [mul_assoc (f':ℤ) w]; exact h'_0
 have hr: pay R' (d^(4*n)):= (main_bill j _ _ n S u).2
 have hP(X':Fields N): ‖(l.map F).prod X'‖ ≤ d^(4*n):=by
    rw [← v']
    have payt {m n₀:Side}(h:m=n₀)(R:Mark m)(v:∀ x:Fields m, ‖R x‖ ≤ d^(4*n))(x:Fields n₀): ‖ship h R x‖ ≤ d^(4*n):=by subst n₀; exact v x
    exact payt (terrain ..) _ (hr _) X'
 have Qv:= eternal P.run i k w ε j h1 D hx hy (pay_nonneg u) b c p g rfl e l o hv q hP y' Ht B
 rw [← pow_mul,show 2*(2*n)=4*n from (by omega),hot,dif_pos g.depth]
 change ‖u0 (T R')‖≤_; rw [v']; exact Qv -- defeq
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
