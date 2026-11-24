import Velour.Crepe.GapSet
import Velour.Crepe.Quiet
import Velour.Board.Relate
import SatinThinBank
import SatinThinAngle
/-! Natural cube card. -/
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


variable {T:Finset Cover}
abbrev snugLeaf (s:ℕ) (J:ℕ) {y:Family P.calibration} (t:InTest W true T false y)
    (h:Between P.calibration j 0 (ruler P.par.block * (J:ℤ)) T): P.Card j s J:=
 ⟨⟨y,(purpose_ok ..).2 ⟨⟨T,t,by rw [SlabMark.area0]; exact fun i u=>(h i u).1⟩,
         by simp⟩⟩,T,t,h⟩
lemma twin_access {s w:ℕ}(g:P.Card j s w) (z:ℂ): ∃ e:P.Card j s w,e.1.1=z • g.1.1:=by
 obtain ⟨S,a,b⟩:=g.2
 exact ⟨P.snugLeaf j s w (a.smul z) b,rfl⟩
lemma upstairs_gap {r v ℓ' w:ℕ}(h:r ≤ v) (p:ℓ'=P.par.R.L.val^(v-r)*w)
 (t:0<w) (u:0<ℓ') (z c:ℂ) (a:P.Card j v ℓ') (b:P.Card j r w) (g:P.Card j v ℓ')
 (x:g.1.1=z • (c • a.1.1 - stream Y H P.refineTest r (v-r) b.1.1)):
 P.Box j v _ u g=z • (c • P.Box j v ℓ' u a - P.Box j r w t b):=by
 subst ℓ'; rw [sub_eq_add_neg,smul_add, smul_neg, smul_smul] at x ⊢

 let e:ℕ:= (L).val^(v-r)*w
 let a':=furnished Y H r P.history j false w b v h
 obtain ⟨m,v₀⟩:=P.twin_access j a' (-z)
 have hp:g.1.1= (z*c) • a.1.1+m.1.1:=by rw [v₀,neg_smul]; exact x
 have q:P.Box j v _ u m=(-z) • P.Box j v _ u a':=PhaseChoice.box_scale
    Y H P.law P.projection j false (P.room j) v e a' m u _ v₀
 rw [P.box_linear j v _ u a m g (z*c) hp, q,neg_smul]
 congr 3
 exact (refined_box Y H P.law r P.history P.projection.clipped j false (P.room j) w b t v h).symm
/-- Room both ways and even with the f-threshold charge. -/
structure Basque (f B:ℕ)(X:Cover)(P:Spine) : Prop where
 stride : 0<B
 both: Secured P.calibration B 0 (rural (P.thresholdF f)+1) 0 (nodeC X)
 rise (j:Axis): (frameRadius j:ℤ)+(P.calibration.ℓ:ℤ) ≤ nodeC X j
 fall (j:Axis): nodeC X j + ((frameRadius j:ℤ)+(P.calibration.ℓ:ℤ)) ≤ ruler P.par.block*(B:ℤ)
abbrev reachLeaf (f s B:ℕ):= (L).val^(s-f)*B
lemma reach_w (s:ℕ)(r:0<B):0<P.reachLeaf f s B:= Nat.mul_pos (pow_pos (L).property _) r


lemma reach_R (p:f≤r)(t:r≤v)(B):P.reachLeaf f v B=(L).val^(v-r)*P.reachLeaf f r B:=by
 unfold reachLeaf; rw [←mul_assoc,←pow_add, show v-r+(r-f)=v-f from by omega]

variable (g:Basque f B X P)
local notation "a!" v:max=> (frameOne (P.clockPlate f v X))
local notation "c!" v:max=> (P.visitOne v (P.clockPlate f v X)).val

include g
lemma comfy (s:ℕ): Between P.calibration j 0 (ruler P.par.block*(P.reachLeaf f s B:ℤ)) (a! s):= by
 intro i h; obtain ⟨v',_,u⟩:=mem_biUnion.mp h; obtain ⟨y,t,rfl⟩:=mem_image.mp u
 have hp: (y j).natAbs ≤ frameRadius j:= Finset.le_sup (f:=fun x:Cover=> (x j).natAbs) t
 let z:ℤ:= ((L).val^(s-f):ℕ)
 have hz: 1 ≤z:=by unfold z; exact_mod_cast (Nat.succ_le_of_lt (pow_pos (L).property (s-f)))
 let c:=nodeC X j; let d:= ruler Q*(B:ℤ)
 have hl:0≤c:=le_trans (by exact add_nonneg (by positivity) (by positivity)) (g.rise j)
 have hr:d-c≥ frameRadius j+ℓ:=by unfold c d; have t':=g.fall j; linarith only [t']
 have ht:P.clockPlate f s X j=z*c:=by unfold clockPlate; rw [Pi.smul_apply,nsmul_eq_mul]
 change _≤ y j + P.clockPlate f s X j ∧ y j+P.clockPlate f s X j+_ ≤ _
 rw [ht]; constructor

 · have q:=le_mul_of_one_le_left hl hz; have w: (frameRadius j:ℤ)+ℓ≤ c:=g.rise j; omega
 have he: z*d= ruler Q*(P.reachLeaf f s B:ℤ):=by
    unfold d reachLeaf z; rw [Nat.cast_mul]; ring
 rw [←he]
 have ht': 0≤d-c:=le_trans (by positivity) hr
 have w:=le_mul_of_one_le_left ht' hz; rw [mul_sub] at w; omega
abbrev bobCard (s:ℕ) : P.Card j s (P.reachLeaf f s B) :=
  P.snugLeaf j s _ (P.basesT (s:=s)) (P.comfy j g s)
abbrev soakOp (s:ℕ):= P.Box j s _ (P.reach_w s g.stride) (P.bobCard j g s)
abbrev upperFoot (r v:ℕ) := (a! v)∪ volumeAround Λ P.width (v-r) (a! r)
lemma comfy2 (p:f≤r)(t:r≤v):
   Between P.calibration j 0 (ruler P.par.block*(P.reachLeaf f v B:ℤ)) (P.upperFoot (X:=X) (f:=f) r v):=by
 intro i h; rcases mem_union.mp h with m|m
 · exact P.comfy j g v i m
 rw [P.reach_R p t,Nat.cast_mul,Nat.cast_pow,mul_left_comm]
 exact expands_shape Y H (P.comfy j g r) (v-r) i m

omit g
lemma fitsOrigin {w:ℕ} (h:∀i,Between P.calibration i 0 (ruler P.par.block*w) T):
    VelourBoard.Parcel P.calibration w 0 0 T:=by
 intro i; unfold Wall; simp only [Pi.zero_apply, mul_zero,zero_add,mul_one]; exact h i


lemma pallet {J:Family P.calibration}(t:InTest W true T false J):
   BQueue T (fun _=>J) J:=by
 obtain ⟨c,e⟩:=Journey.valuation Y H t
 have p:=Tower.pay_nonneg e
 exact BQueue.stay t (show 0<c+1 by linarith) (fun x a=> (e x a).trans (by linarith))

end Spine

namespace VelourWiggle
open Lamour.Bridge.Celeste
open Papal Regis.Head Gleam
-- BQueue combinations adapted from YM/SU5/Silk/Span/Flow
section relay
variable {K:Calibration}{S:Finset Cover}{B:ℕ → Family K}{x:Family K}(h:BQueue S B x)
include h
lemma cueMono{T:Finset Cover}(u:S⊆T): BQueue T B x:= ⟨fun _=> (h.whereTo _).mono u,h.landing.mono u,h.bdd,h.saved⟩
lemma cueSum {Z:ℕ → Family K}{X:Family K}(u:BQueue S Z X): BQueue S (fun i=>B i+Z i) (x+X):=by
 obtain ⟨p,q,⟨C,v,t,g⟩,e⟩:=h; obtain ⟨j,k,⟨D,w,s,r⟩,F⟩:=u
 refine ⟨fun i=>(p i).add (j i), q.add k,⟨_,add_pos v w,pay_add t s,(g.and r).mono fun i ⟨u,v⟩=>pay_add u v⟩,fun a b=>?_⟩
 filter_upwards [e _ (half_pos b), F _ (half_pos b)] with i h u
 have hv:=pay_add h u; rw [add_halves] at hv; rw [show B i+Z i-(x+X)=(B i-x)+(Z i-X) from by abel]; exact hv
lemma cueSub {Z:ℕ → Family K}{X:Family K}(u:BQueue S Z X): BQueue S (fun i=>B i-Z i) (x-X):=by
 obtain ⟨p,q,⟨C,v,t,g⟩,e⟩:=h; obtain ⟨j,k,⟨D,w,s,r⟩,F⟩:=u
 refine ⟨fun i=>InTest.subOp (p i) (j i), InTest.subOp q k,⟨_,add_pos v w,pay_sub t s,(g.and r).mono fun i ⟨u,v⟩=>pay_sub u v⟩,fun a b=>?_⟩
 filter_upwards [e _ (half_pos b), F _ (half_pos b)] with i h u
 have hv:=pay_sub h u; rw [add_halves] at hv; rw [show B i-Z i-(x-X)=(B i-x)-(Z i-X) from by abel]; exact hv
lemma cue_scale (f:ℕ→ℂ)(v:ℂ)(u:Tendsto f atTop (𝓝 v)): BQueue S (fun i=> f i • B i) (v • x):=by
 obtain ⟨p,q,⟨C,g,t,k⟩,e⟩:=h; let D:= ‖v‖+1; have hd:‖v‖<D:=by linarith
 have hD:0<D:=lt_of_le_of_lt (norm_nonneg _) hd; let H:=D*C; have hB:= u.norm.eventually (ge_mem_nhds hd)
 refine ⟨fun i=>(p i).smul _, q.smul _,⟨H,mul_pos hD g,(fun i j=>(pay_scale t v i j).trans (mul_le_mul_of_nonneg_right hd.le g.le)), ?_⟩,fun b r=> ?_⟩
 · filter_upwards [hB,k] with i h v m j; exact (pay_scale v (f i) m j).trans (mul_le_mul_of_nonneg_right h g.le)
 let d:= b/(2*D); let l:= b/(2*C); have ht:Tendsto (fun i=> ‖f i - v‖) atTop (𝓝 0):=by simpa using (u.sub (tendsto_const_nhds (x:=v))).norm
 filter_upwards [hB,e _ (show 0 < d from div_pos r (by positivity)), ht.eventually (ge_mem_nhds (show 0<l from div_pos r (by positivity)))] with i h V z
 rw [show f i • B i-v • x=f i • (B i-x)+(f i-v) • x from by rw [smul_sub,sub_smul]; abel]
 intro m V0; apply (pay_add (pay_scale V _) (pay_scale t (f i-v)) m V0).trans; refine (add_le_add (mul_le_mul_of_nonneg_right h (by unfold d; positivity)) (mul_le_mul_of_nonneg_right z g.le)).trans_eq ?_; unfold d l; field_simp; try ring
end relay
end VelourWiggle

end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.bobCard

