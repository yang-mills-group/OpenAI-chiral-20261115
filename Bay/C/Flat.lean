import Bay.C.Trench
import Bay.C.Buoy
import Bay.D.Regatta
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Bay.C
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Skye Scree Cadre Palot
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tulip Fock Rush Scroll Paige Vault Phase Acorn Spire
open Pastry Vow Rue
attribute [local instance] opCStarAlgebra
open Hake Jet Sault Stax Sour
attribute [local instance] Sour.loreM Sour.loreN
open Rill Branch Tenant Drapes Leaf



open Levier Urn Ione
open Peaks

set_option maxRecDepth 3500
set_option synthInstance.maxHeartbeats 160000
open Py Py.Rate Thera Dial Nacre Laic
open LocalLimit Preparation

open Lor Py.Rate.BScale Push.Uniform
open Pressure SectorNext.Remainder Nor
open Push.AbsoluteSums Trees Roots
open BPress (NPL PL lscale lscale_late lscale_one)
local notation "VΔ" => Buffered.Afterglow.Tower.VacuumSelection.Spine
open Salt SU Swell QuadClock Mew Vow.TreasuryFog
open BProof.Bide

variable {w:Berth}{a b c:ℝ}{x:Site w.side}{o:Seat w.side}{m t:ℕ}{f:w.First}

open D hiding quiver
open Carol Zephyr.Chern
lemma fuelodd (g:w.Rig a c m)(t: Sweep w.side):
 ech t (w.M 1)=swapX (detX t.s) (w.M 1):=by
 let P:=w.P.par
 have ht:1≤P.K.j:= by rw[P.kJ]; norm_num
 let f:=P.V.note.fields_one w.side (P.U.needed.trans g.deep)
 have h:Guard (1:Pane w.side) w.d:=guard0 P.dpos.le
 have hp : ech t (w.M (profile 1)) = swapX (detX t.s) (w.M (profile (flashA t 1))) := funde_f (castX t) (xtra t.charge) (spinU t.charge t.s) (spinZ t.charge t.s) 1 _ ht w.R.J.M _ f (h.shrink P.U.gem)
 rw[flash_id,profile_trivial] at hp
 exact hp

lemma nullTip(g:w.Rig a c m)(y:Site w.side):
 Matrix.trace ((w.M 1 -tickA w.side)*millQ y)=0:=by
 let s:=Signed.mirror 0
 let r:=room y s
 let t:Sweep w.side:= ⟨r.s,r.b,false⟩
 let d:=w.M 1 - tickA w.side

 have hr :detX t.s=true:=by change detX (room y s).s=true;rw[p_s];exact det_t ..
 have h0:boxA t (node y) = node y :=pole y s
 have h1:ech t d= -d:=by
    have k:=echTick t
    have j:=fuelodd g t
    unfold d
    rw [ech,singT,win_l,map_sub]
    rw [ech,singT,hr] at j k; rw[j,k]
    unfold swapX; rw [if_pos rfl,if_pos rfl]; abel
 have h2:ech t (millQ y)=millQ y:=by
    rw [millSt]
    conv_lhs=> rw[←h0]
    exact Tye.proM (boxA t) (boxA t).injective _ (γS _) (fun i j h=>Tye.birth_l i j _ _ _ h) _
 have h3:ech t (d*millQ y)= -(d*millQ y):=by
    rw [←neg_mul,ech,singT,win_m,map_mul]
    rw [ech,singT] at h1 h2
    rw [h1,h2]
 have h4:=congrArg Matrix.trace h3
 rw [ech,singT,trace_twist,win_trace, Matrix.trace_neg,
   show t.charge=false from rfl] at h4
 change Matrix.trace (d*millQ y)= -(Matrix.trace (d*millQ y)) at h4
 exact (mul_eq_zero.mp (show 2*Matrix.trace (d*millQ y)=0 by linear_combination h4)).resolve_left two_ne_zero

lemma nullTotal (g:w.Rig a c m)(x:Site w.side):
 Matrix.trace ((w.M 1 - tickA w.side) * windmill x m)=0:=by
 let H: Op (Single w.side) →+ ℂ := {
     toFun:=fun p=>Matrix.trace ((w.M 1 - tickA w.side) * p)
     map_add':=fun i j=>by rw [mul_add,Matrix.trace_add]
     map_zero':=by simp }
 let Z :Op (Single w.side) →+ ℂ :=0
 change H (squareSum millQ m _ x)=Z (squareSum millQ m (List.ofFn (id:Axis→Axis)) x)
 rw[squareMap,squareMap]
 rw[show (fun y=> H (millQ y)) =(fun y=>Z (millQ y)) from funext <| nullTip g]


lemma flatZ (g:w.Rig a c m)(h:w.Before a b m x f)
 (l:Real.exp (-a*(↑(w.p.B/10:ℕ):ℝ)) ≤ w.p.threshold^2):
 ‖glaze f.X 1‖≤ b*w.p.threshold^2:=by
 have p:1∈GateR w.side w.d:=by
    refine ⟨1,guard0 w.P.par.dpos.le,?_⟩
    rw[profile_trivial,sub_self,norm_zero];exact w.P.par.dpos

 have ht :=nullTotal g x
 rw [h.lump ⟨1,p⟩,Matrix.trace_add] at ht
 have a0:=g.pulse.hint.le
 rw [glaze,eq_neg_of_add_eq_zero_left ht, norm_neg]

 have b0:=soakCostNN h.stone.pay
 suffices hz : ‖Matrix.trace (f.endX 1)‖ ≤ w.wid a b by
    rw[mul_comm b];exact hz.trans (mul_le_mul_of_nonneg_right l b0)

 obtain ⟨F,C,q,t,r,u⟩:=h.endStone
 let i:GateR w.side w.d:=⟨1,p⟩
 rw[u i,Matrix.trace_sum]
 refine (norm_sum_le ..).trans ?_
 apply (sum_le_sum _).trans r
 intro j _
 exact ((essay_looks (q j)).2.2 i).trans (le_mul_of_one_le_left
      (show 0≤ledgerV (C j) from sum_nonneg fun y _=>sum_nonneg fun z _=> (q j).nonn y z) (rent_one a0 j))

structure Canal (w:Berth)(a D r T e:ℝ) : Prop where
 t:Twine 3 w.d D r
 p:Luster w.d T e
 hw:buoyV (w.p.B/10) w.p.threshold ≤ iceR r
 hp:w.p.threshold ≤ e
 ht:w.p.threshold ≤ 1
 gen:2*(w.p.B/10+1)<(More w.side).val
 cool:Real.exp (-a*(↑(w.p.B/10:ℕ):ℝ)) ≤ w.p.threshold^2

lemma aqueduct (P:VΔ)(a:ℝ)(p:0<a):
 ∃ D r T e,0<D∧ 0<T ∧ Dry P (fun w=>∀ c m, w.Rig a c m → Canal w a D r T e):=by
 obtain ⟨V,r,v⟩:=D.twining 3 P.par.dpos
 obtain ⟨Y,T,y⟩:=sheen P.par.dpos
 refine ⟨V,r,Y,T,v.dp,y.dp,?_⟩
 have h:=turnover P.par
 have h1:= ((PL.scale.times BPress.npl_temp).const_mul 12).drop
 filter_upwards [h.eventually (h1.eventually (ge_mem_nhds (ice_pos v.rp))),
  h.eventually (BPress.npl_temp.drop.eventually (ge_mem_nhds zero_lt_one)),
  h.eventually (BPress.npl_temp.drop.eventually (ge_mem_nhds y.rp)),
  h.eventually ((tailω P.par.R.L a 10 p (by decide)).drop.eventually (ge_mem_nhds zero_lt_one))] with s i j k t
 filter_upwards [(ageFar P s).eventually_gt_atTop (radiusB (xTop P s)/10+1)] with n z q x c m g
 let w:=takeUp P s n q
 have xp :w.p.B = radiusB w.x:=g.sizeB
 have xp':w.p.threshold=temp w.x:=g.threshold
 refine ⟨v,y,?_,xp'.symm ▸ k, xp'.symm ▸ j,?_,?_⟩
 · apply le_trans _ i
   change buoyV (w.p.B/10) w.p.threshold ≤12 * ((lscale w.x)*temp w.x)
   rw [←xp', ←mul_assoc,xp]
   refine mul_le_mul_of_nonneg_right ?_ w.p.threshold_pos.le
   unfold lscale
   gcongr;exact Nat.div_le_self ..
 · change 2*(w.p.B/10+1)<w.side.val*2
   rw[xp]; exact (Nat.mul_lt_mul_left zero_lt_two).mpr z |>.trans_eq (mul_comm ..)
 · change Real.exp _≤ w.p.threshold^2
   let C:= exponentialR a w.x
   change w.Q / (temp w.x)^2 * w.boost * C /w.Q ≤1 at t
   have hp := w.p.threshold_pos
   rw[←xp', div_mul_eq_mul_div,div_mul_eq_mul_div, show w.Q*w.boost*C=w.Q*(w.boost*C) from mul_assoc ..,mul_div_assoc,mul_div_cancel_left₀ _ g.qq.ne',div_le_one (pow_pos hp _)] at t
   change Real.exp (-a*(↑(w.p.B/10:ℕ):ℝ))≤_
   rw[xp]
   apply le_trans _ t
   exact le_mul_of_one_le_left (Real.exp_pos _).le (Real.one_le_rpow (BPress.drift_one _) (by norm_num))
