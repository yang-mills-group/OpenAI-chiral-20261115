import YM.SU5.Registration.Rise.Commerce
import YM.SU5.Registration.Rise.Serving
import YM.SU5.Registration.Rise.Handling
import SatinThinPromenade
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
open Worth Pays CF.BProof

/-! # Clock-column long estimates in this election. From phase-independent prices
on mean to ANY spectrum point including x chosen to read the thin probes. Width of
each box MUST stay common here over every tall-scale actor arm of the comparison.
ClockBooking's earned bound is applied at level v (changed coarse-phase probe),
using long banner & No cheap error estimate at volume varying with height.
-/
open SlabMark.ClockBooking
open Aria Casting MacroGrid
local notation "β"=> ruler P.par.block
local notation "β'"=> (16*P.par.block.val:ℕ)
local notation "Z" f:max v:max w:max=> ((P.par.R.L.val:ℕ)^(v-f)*w:ℕ)
variable {w:ℕ}{B:Finset Cover}
lemma ruler_sides0 : ruler P.par.block=(↑(16*P.par.block.val:ℕ):ℤ):=by unfold ruler; push_cast; rfl
lemma clock_fit (p:Plans j X f P)(e:twiceT X j≤w) : nodeC X j+ P.labW f≤(β'*w:ℕ) ∧
 ∀ v:ℕ, Between P.calibration j 0 (β*(Z f v w)) (frameOne (P.clockPlate f v X)):=by
 let b:= (16*P.par.block.val:ℕ)*w; have ht:β*w=(b:ℤ):=by unfold b; rw [P.ruler_sides0]; push_cast; rfl
 let v₀:=nodeC X j; have hh: P.labW f≤ v₀:=p.seat; have hx:0≤v₀:= (Int.natCast_nonneg _).trans hh
 have hb':2*v₀.natAbs ≤ b:=e.trans (Nat.le_mul_of_pos_left _ (by positivity))
 have hb: v₀+v₀ ≤ (b:ℤ):=by omega
 refine ⟨by change v₀+ _≤ (b:ℤ); omega, fun k i u=>⟨P.frame_rise j X p i u,?_⟩⟩
 obtain ⟨m,_,h⟩:=mem_biUnion.mp u; obtain ⟨r,hk,rfl⟩:=mem_image.mp h; have hg:(r j).natAbs≤ frameRadius j:= Finset.le_sup (f:=fun x:Cover=> (x j).natAbs) hk
 have hp:= p.test; let L':= L; let A:=(P.par.R.L.val:ℕ)^(k-f)
 have hv:0<A:= pow_pos (P.par.R.L.property) _
 rw [show β*(Z f k w)=(↑A:ℤ)*(b:ℤ) from (by rw [←ht,Nat.cast_mul]; unfold A; ring)]
 change r j+ P.clockPlate f k X j + _≤ _
 rw [clockPlate, Pi.smul_apply,nsmul_eq_mul]; change r j+(A:ℤ)*v₀+_≤ _; have hg:r j+(P.calibration.ℓ:ℕ)≤v₀:=by unfold v₀; omega
 have he:1≤(A:ℤ):=by exact_mod_cast hv
 nlinarith [mul_le_mul_of_nonneg_left hb (show 0≤(A:ℤ) by positivity)]
local notation "A'"=> ((P.par.R.L.val:ℤ)^(v-f))
lemma lands_at (p:f≤v){m:ℕ} (x:2*(β*((Z f v w):ℕ)*m) ≤ (((N v i).val:ℕ):ℤ)) (y:(((N v i).val:ℕ):ℤ) ≤ 4*(β*((Z f v w):ℕ)*m)) :
 2*(16*P.par.block.val*w)*m ≤ (N f i).val ∧ (N f i).val ≤4*(16*P.par.block.val*w)*m :=by
 let b:= 16*P.par.block.val*w; let L':ℕ:= P.par.R.L.val^(v-f)
 -- size multiplication exact
 have ht:(N v i).val=L'*(N f i).val:=by
    conv_lhs => rw [← Nat.add_sub_of_le p]
    exact refine_side ..
 rw [ht] at x y; let C:=2*b*m; let C':=4*b*m
 have he(j:ℕ): (j:ℤ)*(β*((Z f v w):ℕ)*m)=(↑(L'*(j*b*m):ℕ):ℤ):=by push_cast; rw [show (↑b:ℤ)=β*w from by unfold b; rw [P.ruler_sides0]; push_cast; rfl]; unfold L'; push_cast; ring
 have h1:= le_trans ((he 2).symm.le) (show ((↑(2:ℕ)):ℤ)*(β*↑(Z f v w) * ↑m) ≤ _ from x); have h2:= y.trans_eq (show (4:ℤ)*_= _ from he 4)
 have hL : 0<L':= pow_pos (P.par.R.L.property) _; exact ⟨Nat.le_of_mul_le_mul_left (Int.ofNat_le.mp h1) hL, Nat.le_of_mul_le_mul_left (Int.ofNat_le.mp h2) hL⟩
-- expected course sizes always on nomadic, after qualifying `v` for any displacement
abbrev ColumnBill (P:Spine)(w f:ℕ): Prop:= 14*Worth.meterC (hat P.par.R.L P.par.x f)* (↑((4*(plusAgain P.par.block (P.labW f)))^3*(2*(16*P.par.block.val*w)):ℕ):ℝ) ≤1
lemma tilt_pos (p:treasury A C P f r v) : 0<tiltBase P.par A f:=by
 obtain ⟨q,h⟩:= p.room.exists; exact mul_pos h.2.load.health.2.2.1 (Real.exp_pos _)

variable (p:Plans j X f P) (w) (hw:0<w)(c0:twiceT X j ≤ w)
local notation "U₁" s:max=> P.visitOne s (P.clockPlate f s X)
local notation "π'" s:max=> Z f s w
local notation "n₀" s:max=>frameOne (P.clockPlate f s X)
local notation "G₀" => plusAgain P.par.block (P.labW f)
def gapLeaf (P:Spine)(f r v:ℕ)(X:Cover)(b:ℝ):P.Test:= (↑(zoomM P.par.R.L^(r-f)):ℂ) • (((b:ℂ) • (P.visitOne v (P.clockPlate f v X))) - P.conveying r (v-r) (P.visitOne r (P.clockPlate f r X)))
local notation "y_G" a:max=> P.gapLeaf f r v X a
local notation "qΦ"=> 3*tiltBase P.par A f
lemma tProp (p:f ≤ r)(q:r ≤ v) : Z f v w = (L).val^(v-r)*(Z f r w):=by rw [show v-f=(v-r)+(r-f) by omega,pow_add,mul_assoc]
include c0 p
lemma bought_frame (v:ℕ) : P.InCase j v (π' v) (U₁ v):= InCase.sized P j v _ (P.clock_colors _) P.basesT ((P.clock_fit j X p c0).2 _)
lemma books_tunnel (a:f ≤ r)(g:r≤v) (b:ℝ) : P.InCase j v (π' v) (y_G b):= (InCase.scale (InCase.except ((P.bought_frame j X w p c0 v).scale _) ( (P.tProp w a g).symm ▸ (P.bought_frame j X w p c0 r).climb g)) _)
lemma width_tunnel (t0:f≤r)(q:r≤v): Between P.calibration j 0 (β* ((Z f v w):ℕ)) ((n₀ v) ∪ volumeAround Λ P.width (v-r) (n₀ r)):=by
 let u:=(clock_fit P j X p c0).2
 intro x e; refine (mem_union.mp e).elim (u v x) (fun a=> (show Between P.calibration j 0 (β*↑(Z f v w)) (volumeAround Λ P.width (v-r) (n₀ r)) from ?_) x a)
 have h:= expands_shape Y H (u r) (v-r); rw [P.tProp w t0 q]; push_cast; convert h using 1; push_cast; ring
omit c0 p
-- convergence of moving book on the same volume subsequence
variable {b:ℝ}{δ:ℕ→ℝ}{κ:ℕ→ℕ} (U:lender A C f r v δ b κ P)
lemma visits_queue(s:ℕ): BQueue (n₀ s) (fun _=> (U₁ s).val) (U₁ s).val :=by
 obtain ⟨A,p'⟩:=Journey.valuation Y H (P.basesT (s:=s) (x:=P.clockPlate f s X)); exact BQueue.stay P.basesT (add_pos_of_nonneg_of_pos (Tower.pay_nonneg p') zero_lt_one) (fun i x=> (p' i x).trans (le_add_of_nonneg_right zero_le_one))
include U
lemma lender_queue : BQueue ((n₀ v) ∪ volumeAround Λ P.width (v-r) (n₀ r))
   (fun i=> P.bookT (κ i) f r v (δ (κ i)) X) (P.gapLeaf f r v X b).val:=by
 let V(v):=P.visitOne v (P.clockPlate f v X); have hz:Tendsto (fun i=> ((δ (κ i):ℝ):ℂ)) atTop (𝓝 (b:ℂ)):=Complex.continuous_ofReal.continuousAt.tendsto.comp U.future
 let s (v:ℕ):=frameOne (P.clockPlate f v X)
 have hp:= P.visits_queue X (f:=f) v
 have he:BQueue (volumeAround P.par P.width (v-r) (s r)) (fun i=> P.coastT r v (κ i) (s r) (V r).val) (stream Y H P.refineTest r (v-r) (V r).val):= keep_queue (queue_easy Y H P.law r P.history (V r).val (s r) P.basesT (v-r)) U.earn.tendsto_atTop
 refine cue_scale (cueSub (cueMono (cue_scale hp _ _ hz) subset_union_left) (cueMono he subset_union_right)) (fun _:ℕ=> (↑(zoomM P.par.R.L^(r-f)):ℂ)) _ tendsto_const_nhds
-- Relative operator estimate. `d` of earlier book can be independent of baffle. Use tighter ruler numbers.
local notation "Eζ" i:max n:max=>Journey.sharp P.run P.large n (P.nomadic (κ i)) (P.engine (κ i))
local notation "gBook" i:max=> P.bookT (κ i) f r v (δ (κ i)) X
variable (vCap:P.ColumnBill w f)(PZ:P.NightCop)
include vCap PZ hw c0 p
lemma registered_column : Issues Y H v j (Z f v w) κ P.history (fun i=>gBook i) (3*tiltBase P.par A f):=by
 let hf:= U.treasury.price.le; let hv:= U.treasury.step; let a' := P.thresholdF f; let U₁' := tiltBase P.par A f
 have hp:Tendsto (fun i:ℕ=> ((Journey.side P.run (P.nomadic i) v).val:ℝ)) atTop atTop:= tendsto_natCast_atTop_atTop.comp (P.amount_go v)
 obtain ⟨D,a₁,Xt,Xu⟩:= (P.lender_queue X U).bdd; let Zβ:= U.earn.tendsto_atTop
 filter_upwards [Zβ.eventually (P.history.finance v),Zβ.eventually U.pays,Zβ.eventually (U.treasury.room),Zβ.eventually ((P.amount_go f).eventually_ge_atTop G₀),Zβ.eventually (hp.eventually_ge_atTop (D*(16/U₁'))),Zβ.eventually (PZ v),Xu,Zβ.eventually (P.touring_fee X hf hv)] with i hT e m' cΩ hA bΩ u b₂ n a t V Hf
 let s:= κ i; let k:=P.engine s; let l':=P.nomadic s; let Z₁:=RootBook Y l' k f
 obtain ⟨X₁,X₂⟩:= P.clock_fit j X p c0
 have hz:f ≤ P.run.uv k:= (hf.trans hv).trans hT.enters
 have H₁: (Z₁).p.B=a':=congrArg BudgetPoint.B (Papal.prices_plot P.run f l' k hz).1
 obtain ⟨α₁,z',eV,x,y,hx⟩:=e.2
 let M':= gapMark Y l' k α₁ z' hf hv
 let W₀:=gBook i
 have he:Tower.distribute Y H v l' W₀=M' (wrap (Journey.side Y l' f) X):=by
    unfold W₀; rw [hx]; exact b₂ ..
 have hW:repeatD Λ P.width Z₁.p.B = P.labW f:= by rw [H₁]; -- abbrev
 obtain ⟨y',t'⟩:= P.lands_at (hf.trans hv) (v:=v) (i:=l') (m:=n) V Hf
 have hh:= long_line_issues (P.run) l' k j H hT (hf.trans hv) m'.2 (f:=f) (w:=w) (A:=A) (by -- budget
       rw [hW]; exact vCap)
    (by rw [hW]; exact cΩ) M' bΩ (D:=D) hA (fun l=> oval Y l' k hf hv l hT)
    (graceful_clock Y l' k hf hv H hT Z₁.p.B)
    (fun l v=> gap_ticket Y l' k hf hv l m'.2 y v) X (by rw [hW]; exact p.seat) (by rw [hW]; exact X₁) W₀ (aux_test ((P.lender_queue X U).whereTo i)) he u t hw y' t' a
 change ‖ (Eζ i v) (SlabMark.banner j (Z f v w:ℕ) ((Z f v w:ℕ)*a) n W₀)‖ ≤_
 rw [show ((↑(Z f v w)):ℤ)= ((L).val:ℤ)^(v-f)*w from by push_cast; rfl, mul_assoc]; exact hh

omit U hw c0 p PZ vCap in
lemma calendarZ (v f w:ℕ)(hw:0<w): 0 < P.par.R.L.val^(v-f)*w:= mul_pos (pow_pos P.par.R.L.property _) hw -- remove include prior
-- mean THEN single. Give hF explicitly to rewrite width. Card valuation here, all consumers would still have to shift their own cap.
lemma mean_span (a:f≤r)(h:r≤v): ‖P.Box j v (Z f v w) (P.calendarZ v f w hw) (P.books_tunnel j X w p c0 a h b).card‖ ≤ 2*(3*tiltBase P.par A f):=
   let t':= P.books_tunnel j X w p c0 a h b
   ClockBooking.earned Y H P.law v P.history P.projection.clipped j (Z f v w) ((n₀ v) ∪ volumeAround Λ P.width (v-r) (n₀ r)) (P.lender_queue X U) (P.width_tunnel j X w p c0 a h) κ U.earn.tendsto_atTop (P.calendarZ _ _ _ hw) (mul_pos (by norm_num) (P.tilt_pos U.treasury)) (P.registered_column j X w p hw c0 U vCap PZ) (f₀:=t'.card) (congrArg Subtype.val t'.entry) (P.room j)

lemma passage_clock (a:f≤r)(h:r≤v)(x:P.Spectrum0 j): ‖(b:ℂ) • (P.bought_frame j X w p c0 v).charges x (P.calendarZ v f w hw)-(P.bought_frame j X w p c0 r).charges x (P.calendarZ r f w hw)‖ ≤ 6*tiltBase P.par A f/(zoomM P.par.R.L ^(r-f)):=by
 let V:=P.books_tunnel j X w p c0 a h b; let f₀:= P.bought_frame j X w p c0 v
 let D:= P.bought_frame j X w p c0 r; let E:= V.charges x (P.calendarZ v f w hw); let μ':ℝ:= zoomM P.par.R.L^(r-f); let U':= D.charges x (P.calendarZ r f w hw)
 have he:0<μ':= pow_pos (zoomM_p _) _
 let s₁: P.InCase j v (Z f v w) (P.conveying r (v-r) (P.visitOne r (P.clockPlate f r X))):= (P.tProp w a h).symm ▸ D.climb h
 let v₀:= P.calendarZ v f w hw
 change ‖(b:ℂ) • f₀.charges x v₀-U'‖ ≤ 6*tiltBase P.par A f/μ'
 have hE:E= (μ':ℂ) • ((b:ℂ) • f₀.charges x v₀-U'):=by
    have e: s₁.charges x v₀=U':=(s₁.charges_eq x (D.climb h) rfl (P.tProp w a h) rfl v₀).trans (D.charges_climb x h (P.calendarZ r f w hw))
    change (((f₀.scale (b:ℂ)).except s₁).scale (μ':ℂ)).charges x v₀=_; rw [((f₀.scale (b:ℂ)).except s₁).charges_scale x (μ':ℂ) v₀,(f₀.scale (b:ℂ)).charges_except x s₁, f₀.charges_scale x (b:ℂ) v₀, e] -- implicit issue
 apply (le_div_iff₀ he).mpr; rw [mul_comm]; have hx : ‖E‖≤ 2*(3*tiltBase P.par A f):= (V.cap x v₀).trans (P.mean_span j X w p hw c0 U vCap PZ a h)
 rw [hE, norm_smul,Complex.norm_real,Real.norm_of_nonneg he.le] at hx; linarith only [hx]
omit U hw c0 p PZ vCap
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms Spine.bought_frame
#print axioms Spine.books_tunnel
#print axioms Spine.passage_clock
#print axioms Spine.registered_column
