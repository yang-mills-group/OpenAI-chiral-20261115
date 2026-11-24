import SatinThinMill
import Velour.Crepe.Dye
import Velour.Crepe.Rent
/-! # Centering a clover. Purchase ironed cap.

The centering term is of course scalar*heat; its vacuum scalar
is the very elected expectation seen from this same width. -/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 800000
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
open Aria Set TopologicalSpace Metric
local notation "Λ"=> P.par
local notation "K"=> P.calibration
local notation "H"=> P.large
local notation "Y₀"=> P.run
local notation "Φ" => P.colorSpace j x
local notation "ω"=>P.colorZero j x
local notation "u"=> enclave P.calibration
local notation "X"=> P.ColorHil j x

local notation "E"=> (P.physicalEnergy j x).E
local notation "m"=> timeMesh P.par
local notation "Q" => P.shifts j
local notation "L"=> P.par.R.L.val
variable {s t v w:ℕ}
lemma thread_door {w:ℕ}(a:P.Card j s w)(p:0<w)(h:P.voxTest j s a.val∈ enclave K) :
    ∃ T:(P.ColorHil j x).Op, P.ThreadOp j x s w (P.voxTest j s a.val) T ∧ ‖T‖ ≤ ‖P.Box j s w p a‖:=
 ⟨_,⟨a,p,h,rfl,rfl⟩, NonUnitalStarAlgHom.norm_apply_le Φ _⟩
variable {P j x}
lemma ThreadOp.worth {f:P.Test}{T:(P.ColorHil j x).Op}(q:P.ThreadOp j x s w f T):
    ‖P.singleState j s x f‖ ≤ ‖T‖:=by
    rw [← q.expected]
    refine (norm_inner_le_norm ..).trans ?_
    rw [P.norms_color j x,one_mul]
    exact (ContinuousLinearMap.le_opNorm ..).trans (mul_le_of_le_one_right (norm_nonneg _) (P.norms_color j x).le)



lemma ThreadOp.center {f:P.Test}{T:(P.ColorHil j x).Op}(q:P.ThreadOp j x s w f T):
   ∃ U, P.ThreadOp j x s w (f-P.singleState j s x f • (1:P.Test)) U ∧ ‖U‖≤2*‖T‖:=by
 let t:=whenly m s w
 refine ⟨_,q.sub ((ThreadOp.heat q.pos).smul (P.singleState j s x f)),?_⟩
 refine (norm_sub_le ..).trans ?_
 rw [norm_smul,two_mul]
 exact add_le_add_right ((mul_le_of_le_one_right (norm_nonneg _) ((P.physicalEnergy j x).shrinks t)).trans q.worth) _
end Spine


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
local notation "Ω"=>P.Hil j
local notation "φ"=> P.groundZero j
local notation "μ"=> P.pillars j
local notation "W"=> P.calibration
local notation "Q"=> P.par.block
local notation "ℓ"=> P.calibration.ℓ
local notation "Ξ"=> household W
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
/-! # Fix ranks independently of layout and period. Extract for every *fixed* v from very same P (no law mutation). -/
local notation "aK"=>P.nomadic
local notation "bK"=>P.engine
variable {A C U:ℝ}

open CF.Pannier.Chancel CF.Py.Rate.LocalLimit.Preparation.Yoke Worth VelourBoard
variable {B:ℕ}{X:Cover}

open Aria Casting MacroGrid
variable (x:P.Spectrum0 3)(l:List Axis)
local notation "ξ"=> P.advocate 3 x j
local notation "G"=>P.ColorHil j ξ
local notation "D△" d:max v:max=> (P.basePlay x d v).pivot P l
local notation "R!" s:max v:max => P.clockPlate s v X
local notation "Q!" s:max v:max=> P.centeredQ x v (R! s v)
lemma boughtVelourEntry (h:Basque s B X P) (v:ℕ):
    ∃ U,P.ThreadOp j ξ v (P.reachLeaf s v B) (P.centeredQ x v (P.clockPlate s v X)) U ∧
        ‖U‖≤2*‖P.soakOp j h v‖:=by
 have e:P.voxTest j v (P.bobCard j h v).val∈enclave W:= P.clock_colors _
 obtain ⟨T,q,r⟩:= P.thread_door j ξ _ (P.reach_w v h.stride) e
 obtain ⟨U,g,b⟩:=q.center
 refine ⟨U,?_,b.trans (mul_le_mul_of_nonneg_left r (by norm_num))⟩
 unfold centeredQ
 rw [←P.single_agrees 3 j x v]
 exact g

local notation "q!" d:max v:max=> pivotQ (P.granule (P.megaK d v)) l
variable {d m:ℕ}
lemma boughtVelour (h:Basque s B X P) (p:Cover) (a:ℝ)
     (e:R! s v=(q! d v)+P.sidesPerTick • p)
     (r:P.roomy*P.macroStep v≤ P.meshPose v p j)
     (r':P.roomy*P.macroStep v≤P.reachLeaf s v B*P.macroStep v - P.meshPose v p j)
     (z:P.reachLeaf s v B*P.macroStep v ≤ a):
  (D△ d v).realWidth P j ≤ a ∧
   ‖(D△ d v).velour P j ξ a‖ ≤ 2*‖P.soakOp j h v‖:=by
 obtain ⟨U,g,b⟩:=P.boughtVelourEntry j x h v
 have f:P.centeredQ x v (P.clockPlate s v X)=P.chartAll p (D△ d v).F:=by rw [P.baseP_F,P.chart_center,e]
 have v':(D△ d v).s=v:=(P.basePlay x d v).pivot_s P l
 have w:(D△ d v).realWidth P j=P.roomy*P.macroStep v:= by rw [Apron.pivot_w,P.play_width]
 let M:=timeMesh P.par
 have t: bell M v (P.reachLeaf s v B) = P.reachLeaf s v B * P.macroStep v:=by unfold bell; rw [Int.cast_natCast]; rfl
 obtain ⟨r,b'⟩:= (D△ d v).buyDye P j ξ p (g.mono rfl f) v' (w.le.trans r)
        (w.le.trans (by rw [t];exact r')) a (t.le.trans z)
 exact ⟨r,b'.trans b⟩


abbrev flourish(A:ℝ):=2* (4*zoomC P.par.R.L) * P.dayRate A
lemma flourish_pos: 0<P.flourish A:=by
 have h:=zoomC_p L
 exact mul_pos (mul_pos (by norm_num) (mul_pos (by norm_num) (lt_of_lt_of_le zero_lt_one h))) (P.day_p (A:=A))

private lemma crepe_cost_exact (u:P.NightCop)(g:Basque (k+k) B X P)
     {a: ℕ×ℕ→ℝ}{c:ℕ→ℕ×ℕ→ℝ}{w:ℕ→ℕ}
     (p:d < m)(q:m ≤ k+k)(q':k+k+1 < v)
     (h:Workforce A C d v P c a w)
     (e:0 < P.par.slotFee (k+k))
     (z:P.singleQuiet (k+k+1) token)
     (z0:P.cordRate A (k+k) (k+k+1) token ≤ P.dayRate A)
     (y:P.RentBox (k+k) B)
     (y':P.RentBox (k+k+1) (P.reachLeaf (k+k) (k+k+1) B))
     (a0:‖(D△ d v).velour P j ξ (P.macroStep k)‖ ≤ 2*‖P.soakOp j g v‖):
  ‖(a (d,m):ℂ) • (D△ d v).velour P j ξ (P.macroStep k)‖ ≤
     P.flourish A * ((zoomC P.par.R.L)^2)^k:=by
 let Z:=zoomC L
 have hZ:=zoomC_p L


 have t:=P.backers j u g (Nat.lt_succ_self _) q' z tk_budget.2 e y' y h
            (d:=d) (h:=m) ⟨le_refl _,p,by dsimp; omega⟩ (by omega) (by omega)
 rw [norm_smul] at *
 apply le_trans (mul_le_mul_of_nonneg_left a0 (norm_nonneg _))
 rw [mul_left_comm]
 refine (mul_le_mul_of_nonneg_left t (by norm_num : (0:ℝ)≤2)).trans ?_
 have zz: Z^(k+k+1-m) ≤ (Z^2)^k*Z := by
    rw [←pow_mul, two_mul k,←pow_succ]; exact pow_le_pow_right₀ hZ (by omega)
 have h0:0≤Z:=zero_le_one.trans hZ
 have t' := mul_le_mul (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left zz
      (by norm_num: (0:ℝ)≤4)) (by norm_num : (0:ℝ)≤2)) (le_refl (P.dayRate A)) (P.day_p.le) (show 0≤2*(4* ((Z^2)^k*Z)) by positivity)
 rw [←mul_assoc]
 refine ((mul_le_mul_of_nonneg_left z0 (show 0≤2*(4*Z^(k+k+1-m)) by positivity)).trans t').trans ?_
 unfold flourish Z
 exact le_of_eq (by ac_rfl)


/-- At ANY choice of character; for all lists of turned axes; with
price growing as a *power of resolution k inverse macroStep*.
Number of levels needed from Workforce is at most 2k+2
(in addition to v). Estimate in the whole ColorHil, not just vacuum.
It's fine that the "v sufficiently high" qualification might depend
on the pivot. -/
theorem clover_cap (u:P.NightCop)(p:d < m)(o:Odd P.par.R.L.val)(A C:ℝ):
  ∀ᶠ k:ℕ in atTop, ∀ j:Axis,∀ l:List Axis,
    ∀ᶠ v:ℕ in atTop, ∀{a:ℕ×ℕ→ℝ}{c:ℕ→ℕ×ℕ→ℝ}{w:ℕ→ℕ}, 
      Workforce A C d v P c a w →
      ∀ x:P.Spectrum0 3,
       let D:= (P.basePlay x d v).pivot P l
       D.realWidth P j ≤ P.macroStep k ∧
       ‖(a (d,m):ℂ) • D.velour P j (P.advocate 3 x j) (P.macroStep k)‖
         ≤ P.flourish A * ((zoomC P.par.R.L)^2)^k:=by
 have y:StrictMono (fun k:ℕ=>k+k):=by intro a b h; dsimp; omega
 filter_upwards [P.thinArc,
      y.tendsto_atTop.eventually (P.paysDay (A:=A)),
      y.tendsto_atTop.eventually P.pays_feasible,eventually_ge_atTop m]
          with k zone e t k0 j l
 let f:= k+k; let root:=P.rootSpace d f l; let B:=P.rentSpan f
 have h:m≤ k+k:=by omega


 filter_upwards [P.quoteBoth j l (p.le.trans h) o,eventually_gt_atTop (f+1)]
     with v q r a c w W0 x
 obtain ⟨d',z,i,i',z'⟩:= q
 let g: Basque f B root P:=P.pricedSeat d l f
 have h0: P.reachLeaf f v B * P.macroStep v ≤ P.macroStep k:=by
    rw [P.reach_size B d'.le]
    exact zone.le
 obtain ⟨h1,h2⟩:=P.boughtVelour j x l g z (P.macroStep k) i i'.le z'.le h0
 exact ⟨h1,crepe_cost_exact P j x l u g p h r W0 e.1 e.2.1 e.2.2 t.1 t.2 h2⟩
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.clover_cap

