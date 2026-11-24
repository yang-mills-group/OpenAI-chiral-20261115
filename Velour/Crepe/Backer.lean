import Velour.Crepe.Wiggle
/-! Demand extensive chessboard to get clover cap. -/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 6200
set_option maxHeartbeats 1200000
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

abbrev RentBox (s B:ℕ) := 14*meterC (F s) *
    ((↑(2*VelourBoard.pitch P.calibration B :ℕ):ℝ)^4) ≤1

lemma vel_ex (i s:ℕ)(J:Buffered.Family P.calibration) :
    exhibit Y H s (P.nomadic i) J=P.freightT s i J:= (Tapestry.arranged ..)
variable (cold:P.NightCop)
variable (g:Basque f B X P)
local notation "a!" v:max=> (frameOne (P.clockPlate f v X))
local notation "c!" v:max=> (P.visitOne v (P.clockPlate f v X)).val
local notation "m!" r:max v:max => P.upperFoot (X:=X) (f:=f) r v
local notation "b!" v:max=> P.bobCard j g v
local notation "o!" v:max=> P.soakOp j g v
open VelourWiggle
section
variable {b:ℝ}{δ:ℕ→ℝ}{κ:ℕ→ℕ}
variable (K:lender A C f r v δ b κ P)
local notation "z!" => zoomM L^(r-f)
local notation "pi!" => (fun e:ℕ=>P.bookT (κ e) f r v (δ (κ e)) X)
local notation "eta!"=>((↑(z!:ℝ):ℂ) • ((b:ℂ) • (c! v)-stream Y H P.refineTest r (v-r) (c! r)))
include K
lemma queueLeaf : BQueue (m! r v) pi! eta!:=by
 have h(s):BQueue (a! s) (fun _=> c! s) (c! s):=P.pallet P.basesT
 have t:=VelourBoard.convoy Y H r P.projection κ K.earn.tendsto_atTop (h r) (v-r)


 have q:=cueSub (cueMono (cue_scale (h v) (fun e=>(δ (κ e):ℂ)) b
       (Complex.continuous_ofReal.continuousAt.tendsto.comp K.future))
         (T:=m! r v) subset_union_left)
        (cueMono t subset_union_right)
 exact cue_scale q _ _ tendsto_const_nhds
variable (rent:P.RentBox f B)
local notation "E!"=> owedF P.par f A 1
include rent g
lemma paysLeaf :
 Settle Y H v P.projection (P.reachLeaf f v B) pi! κ 0 (E!):=by
 have hi:=K.treasury; have tend:=K.earn.tendsto_atTop
 have l:f ≤ r:=hi.price.le; have m:r≤ v:=hi.step
 have q:=P.touring_fee X l m
 unfold Settle
 filter_upwards [tend.eventually hi.room,tend.eventually K.pays,tend.eventually q,tend.eventually (P.history.finance v)] with e t' t q' w d G D hD
 let i:= P.nomadic (κ e)
 let k:= P.engine (κ e)
 let T:= pi! e
 have w':Ferry Y v i k:= w
 obtain ⟨u,z,p,_,read,eq⟩:=t.2
 have hd : (RootBook Y i k f).p.B=P.thresholdF f:=
   congrArg BudgetPoint.B (Papal.prices_plot Y f i k ((l.trans m).trans w'.enters)).1
 have hw : Shield P.calibration B 0 (rural (RootBook Y i k f).p.B+1) 0 (node (P.rootAt f i X)):=by
    rw [hd]; exact ⟨_,g.both,(node_of ..).symm⟩
 have hs: exhibit Y H v i T=gapMark Y i k u z l m (P.rootAt f i X):=by


    unfold T; dsimp only; rw [eq]; exact (P.vel_ex ..).trans (q' u z)
 refine gap_board Y i k H l m B 0 _ T t'.2 read w' hw rent hs d G D ?_
 simp only [Pi.zero_apply,mul_zero]
 exact hD

include cold
lemma wagedCap (p:0<slotFee P.par f) :
  ‖((↑(z!:ℝ):ℂ)) • ((b:ℂ) • (o! v)-(o! r))‖ ≤ 4* (E!):=by
 have h:=P.queueLeaf (X:=X) K
 have q:=P.paysLeaf g K rent
 have l:=K.treasury.price.le; have m:=K.treasury.step
 let t:=P.snugLeaf j v _ h.landing (P.comfy2 j g l m)
 let w:=P.reachLeaf f v B
 have v':0<w:=P.reach_w v g.stride
 have r':0<P.reachLeaf f r B:=P.reach_w r g.stride
 rw [show ((↑(z!:ℝ):ℂ)) • ((b:ℂ) • (o! v)-(o! r))=P.Box j v w v' t from
     (P.upstairs_gap j m (P.reach_R l m B) r' v' _ _ (b! v) (b! r) _ rfl).symm]
 refine boardPrice Y H P.law v P.projection j w pi! _ κ K.earn.tendsto_atTop 0 cold
    (P.fitsOrigin (fun i=>P.comfy2 i g l m)) rfl _ _ ?_ q _ t h
 unfold owedF; positivity 


lemma wagedCap_add
  (p:0<slotFee P.par f) : 
  ‖(b:ℂ) • (o! v)‖ ≤ 4* (E!) / z! + ‖o! r‖:=by
 have t:=P.wagedCap j cold g K rent p
 let z:=z!
 have h:0<z:=pow_pos (zoomM_p _) _
 change ‖(z:ℂ) • _‖≤_ at t
 rw [norm_smul,Complex.norm_real,Real.norm_of_nonneg h.le,mul_comm] at t
 refine (norm_le_norm_sub_add _ (o! r)).trans (add_le_add_left ?_ _)
 exact (le_div_iff₀ h).2 t
end
-- comparison rung r; fees with scale r 
abbrev singleQuiet (r:ℕ)(U:ℝ) :=
 ∀ (i k:ℕ), r ≤ P.run.uv k → 
     ∀τ, Yoke.Quiet U (routeTip P.run i k 1 r τ)
abbrev riches (r:ℕ)(c:ℝ) :=
 ∀ᶠ i in atTop,ShelterCost c P.run r (P.nomadic i) (P.engine i)
include cold g
lemma reserveNorm (q:f≤r)(w:P.singleQuiet r U) (u:0<U)
      (h:P.riches r C)
      (rent:P.RentBox r (P.reachLeaf f r B)) :
 ‖o! r‖≤ 4 * (U * Real.exp 1) :=by


 let Z:=P.reachLeaf f r B
 have t:InTest W true (a! r) false (c! r):=P.basesT
 have b:=P.fitsOrigin (fun i=>P.comfy i g r)
 refine boardPrice Y H P.law r P.projection j Z (fun _=>c! r) (a! r) id tendsto_id 0 cold b
   rfl _ _ (by positivity) ?_ _ (b! r) (P.pallet t)
 unfold Settle
 filter_upwards [h, P.history.finance r] with e earn hr d J G hD
 let i:=P.nomadic e; let k:=P.engine e
 let a:=upRoot Y i q (P.rootAt f i X)
 have hx:wrap (More (N r i)) (P.clockPlate f r X)=node a:= (P.high_root q X).symm
 have qs: exhibit Y H r (P.nomadic e) (c! r)=routeTip Y i k 1 r a:=by
    rw [P.vel_ex, ←P.eerieT hx hr.enters 1]
    rw [Complex.ofReal_one,one_smul]
 have q':Yoke.Quiet U (exhibit Y H r (P.nomadic e) (c! r)):=qs.symm ▸ w i k hr.enters a
 exact quiet_board Y r i k earn H q' hr.depth u.le t b rent hD


abbrev cordRate (A:ℝ) (f r:ℕ) (U:ℝ) :=4*owedF P.par f A 1 / (zoomM P.par.R.L^(r-f))+
    4*(U*Real.exp 1)
local notation "Tier"=> ℕ×ℕ
/-- Renormalize the late cap at denominators from any earlier tier. -/
theorem backers (p:f<r) (q:r<v)
     (w:P.singleQuiet r U) (u:0<U) (e:0<slotFee P.par f)
     (rent:P.RentBox r (P.reachLeaf f r B))
     (pay:P.RentBox f B)
     {b d h:ℕ}
     {a:Tier→ℝ}{c:ℕ→Tier→ℝ}{n:ℕ→ℕ}
     (l:Workforce A C b v P c a n)
     (m:chargeSpan b v (d,h)) (t:h≤r) (x:b≤f):
 ‖(a (d,h) :ℂ) • (o! v)‖ ≤ 4*zoomC P.par.R.L^(r-h)*P.cordRate A f r U:=by
 have y:chargeSpan b v (f,r):=⟨x,p,q.le⟩
 have z:chargeSpan b v (r,r+1):=⟨x.trans p.le,Nat.lt_succ_self _,q⟩
 let k:= l.plans (f,r) y
 have h':P.riches r C:=((l.plans _ z).treasury.room.mono fun i t=>t.2)
 let D:=P.cordRate A f r U
 have u':‖(a (f,r):ℂ) • (o! v)‖ ≤ D:=(P.wagedCap_add j cold g k pay e).trans
    (add_le_add_right (P.reserveNorm j cold g p.le w u h' rent) _)


 let c0:= 4*zoomC P.par.R.L^(r-h)
 have t0 : 0≤ c0:=by unfold c0; have he:=zoomC_p L; positivity
 rw [norm_smul,Complex.norm_real,Real.norm_eq_abs] at u' ⊢
 change _ ≤ c0*_
 exact le_trans (mul_le_mul_of_nonneg_right (l.career _ _ m y t) (norm_nonneg _))
      (by rw [mul_assoc];exact mul_le_mul_of_nonneg_left u' t0)
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.backers

