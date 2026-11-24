import YM.SatinExist.Hall
import YM.SatinExist.Fence
import SatinThinRampart
import SatinThinAngle
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
structure Watchdesk:Prop where
 plan:Plans j X f P
 w0:0<w
 width:(nodeC X j:ℤ)*2 ≤ ruler P.par.block * w
variable (h:Watchdesk (f:=f) P j X w)
include h
local notation "p_"=> h.plan
local notation "£" s:max=> P.longtruck w f s
local notation "U!" s:max=> P.risingtruck w (f:=f) (v:=s) h.w0
local notation "V'" s:max=> P.clockPlate f s X
local notation "U₀" s:max=> frameOne (P.clockPlate f s X)
lemma deskFrame (r:ℕ) : Between P.calibration j 0 (ruler P.par.block * ↑(£ r)) (frameOne (V' r)):=by
 have hv':= Plans.test h.plan
 let v₁:ℤ:= (nodeC X j); have hv: 0≤v₁:= by have he:= Plans.seat h.plan; unfold v₁; omega
 let a:ℤ:= r; let d:ℤ:= ((L).val:ℤ)^(r-f); let b:ℤ:= ruler P.par.block*w; have hp:1 ≤ d:= one_le_pow₀ (show (1:ℤ)≤ ((↑(L).val):ℤ) by exact_mod_cast (Nat.succ_le_of_lt P.par.R.L.property))
 have he: P.clockPlate f r X j =d * v₁:=by unfold clockPlate d v₁; simp only [Pi.smul_apply,nsmul_eq_mul,Nat.cast_pow]
 have hy: ruler P.par.block * ↑(£ r)=d*b:=by unfold longtruck d b; rw [Nat.cast_mul,Nat.cast_pow]; ring
 rw [hy]; intro i v;
 obtain ⟨g,y,c⟩:= mem_biUnion.mp v; obtain ⟨t,u,rfl⟩:= mem_image.mp c; have ht:(t j).natAbs≤ frameRadius j:=Finset.le_sup (f:=fun x:Cover=> (x j).natAbs) u
 change 0+(ℓ:ℤ) ≤ t j+P.clockPlate f r X j ∧ t j+P.clockPlate f r X j+(ℓ:ℤ) ≤ _
 rw [he]; have hx:d * v₁ ≥ v₁:= le_mul_of_one_le_left hv hp
 have hz:v₁*2≤b:=h.width; have hk:=mul_le_mul_of_nonneg_left hz (by omega:0≤d)
 have hk':d*v₁+d*v₁≤d*b:=by nlinarith only [hk]
 change _≤ v₁ at hv'; omega
abbrev deskCard (s:ℕ): P.Card j s (P.longtruck w f s):=⟨P.flume j X s h.plan,frameOne (V' s),P.basesT,deskFrame P j X w h s⟩
noncomputable abbrev deskValue (s:ℕ): (P.Hil j).Op:= P.Box j s (P.longtruck w f s) (U! s) (P.deskCard j X w h s)
local notation "Ξ" s:max=> P.deskValue j X w h s
local notation "ι'" r:max v:max=> U₀ v ∪ volumeAround Λ P.width (v-r) (U₀ r)
variable {b:ℝ}{l:ℕ→ℝ}{σ:ℕ→ℕ} (p:f≤r)(u:r≤v)
include p u
lemma dated_hours : (L).val^(v-r)* £ r= £ v:=by
 unfold longtruck; rw [← mul_assoc,←pow_add,show v-r+(r-f)=v-f by omega]
lemma bentC: Between P.calibration j 0 (ruler P.par.block* ↑(£ v)) (ι' r v):=by
 intro i q; rcases mem_union.mp q with v|z; exact deskFrame P j X w h _ _ v
 have g:= expands_shape Y H (deskFrame P j X w h r) (v-r)
 rw [←P.dated_hours j X w h p u, Nat.cast_mul,Nat.cast_pow,mul_left_comm]; exact g i z
-- proof for estate. need b included expand
variable (K': lender A C f r v l b σ P)
include K'
lemma convoy_eight : BQueue (U₀ v ∪ volumeAround P.par P.width (v-r) (U₀ r))
   (fun i=> P.bookT (σ i) f r v (l (σ i)) X) ((P.cameo j X b p u h.plan).val):=by
 let Q':=P.history; let V(s:ℕ):= P.visitOne s (P.clockPlate f s X)
 let M:= P.bookT; let x:ℂ:= zoomM L^(r-f); -- type goes zoomM pow? specify
 have ht : InTest W true (U₀ r) false ((V r).val):=P.basesT; have hxT : InTest W true (U₀ v) false ((V v).val):= P.basesT
 let S:= SlabMark.queue_easy Y H P.law r (gleam_path Y H Q' K'.earn) (V r).val (U₀ r) ht (v-r); let U:= BQueue.enroute (b:=(-1:ℂ)) tendsto_const_nhds S
 obtain ⟨d,t⟩:= valuation Y H hxT; have hx: 0<d+1:=add_pos_of_nonneg_of_pos (pay_nonneg (F:=(V v).val) t) zero_lt_one
 let D:= BQueue.stay hxT hx (fun i x=> le_trans (t i x) (by linarith))
 have hz:Tendsto (fun i=> (l (σ i):ℂ)) atTop (𝓝 (b:ℂ)):= Complex.continuous_ofReal.continuousAt.tendsto.comp K'.future -- name
 let D':= BQueue.enroute hz D; let z:ℂ:= (↑(zoomM L^(r-f)):ℂ)
 have g₀:= BQueue.enroute (b:=z) tendsto_const_nhds (BQueue.again D' U)
 -- convert RHS
 change BQueue (ι' r v) (fun i=> z • ((l (σ i):ℂ) • (V v).val + (-1:ℂ) • coastT P r v (σ i) (U₀ r) ((V r).val))) (z • ((b:ℂ) • (V v).val + (-1:ℂ) • stream Y H P.projection.refine r (v-r) ((V r).val))) at g₀
 simp_rw [neg_one_smul,←sub_eq_add_neg] at g₀; exact g₀
abbrev vividCard : P.Card j v (P.longtruck w f v):=⟨P.cameo j X b p u h.plan,ι' r v,(P.convoy_eight j X w h p u K').landing,P.bentC j X w h p u⟩
lemma vivid_value : P.Box j v (P.longtruck w f v) (U! v) (P.vividCard j X w h p u K') = (↑(zoomM L^(r-f)):ℂ) • ((b:ℂ) • (Ξ v) - Ξ r):=by
 let B:=P.Box j v (P.longtruck w f v) (U! v); let f':=P.deskCard j X w h; let D':= P.vividCard j X w h p u K'
 let c:= f' r; let a:= f' v
 let W':= furnished Y H r P.history j false (P.longtruck w f r) c v u
 obtain ⟨x,hx,hw'⟩:∃ x:P.Card j v (P.longtruck w f v),x.val=W'.val∧ B x=P.deskValue j X w h r:=by
    let p':=(Q) -- defeq
    let T':=refined_box Y H P.law r P.history P.projection.clipped j false (P.room j) (P.longtruck w f r) c (U! r) v u
    have hk:=P.dated_hours j X w h p u
    -- pack abstract dependent
    have liftZ (i:ℕ)(x₁:P.Card j v i)(p₂:0 < i)(e:i= £ v)(q:P.Box j v i p₂ x₁=P.deskValue j X w h r): ∃ x:P.Card j v (P.longtruck w f v), x.val=x₁.val ∧ B x=P.deskValue j X w h r:=by subst i; exact ⟨x₁,rfl,q⟩
    exact liftZ _ W' _ hk T'.symm
 -- box linear by multiples scale & neg & subtract. Need card operations explicit
 let z:ℂ:= (↑(zoomM L^(r-f)):ℂ)
 change B D'= z • ((b:ℂ) • B a - Ξ r)
 rw [←hw']; have hp:= box_linear P j v (P.longtruck w f v) (U! v)
 have ad (u v':ℂ) (F G m:P.Card j v (P.longtruck w f v))(h:m.val.val=u • F.val.val+v' • G.val.val): B m=u • B F+v' • B G:=by
    let T':= v' • G.val
    have Gt:∃ t:P.Card j v (P.longtruck w f v),t.val=T':=by
       let t:=G.property.choose; obtain ⟨t',hG⟩:=G.property.choose_spec
       exact ⟨⟨T',_,InTest.smul _ t',hG⟩,rfl⟩
    obtain ⟨t,t'⟩:=Gt
    have go:∃ u:P.Card j v (P.longtruck w f v), u.val.val=0:=by
       obtain ⟨v0,hZ,v₀⟩:=F.property
       exact ⟨⟨(0:ℂ) • F.val,v0,InTest.smul (0:ℂ) hZ,v₀⟩,(show (0:ℂ) • F.val.val=0 from zero_smul ..)⟩
    obtain ⟨u0,hu⟩:=go; have ht:t.val.val=v' • G.val.val:=by rw [t']; rfl
    have he: B u0= 0:= box_zero P j v _ (U! v) u0 hu
    refine (hp F t m u (by rw [h,ht])).trans (congrArg (u • B F+·) ((hp G u0 t v' (by rw [hu,ht,add_zero])).trans (show v' • B G+B u0=v' • B G from by rw [he,add_zero])))
 have hz:D'.val.val = z • ((b:ℂ) • a.val.val - W'.val.val):=rfl; rw [←hx] at hz
 exact (ad (z*(b:ℂ)) (-z) a x D' (by rw [hz]; module)).trans (by module)
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
