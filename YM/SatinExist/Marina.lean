import YM.SatinExist.Elm
import YM.SatinExist.Carnet
import YM.SatinExist.Dovecote
/-! # Literal field engine. Mixed stencils of the actual A.Converge, not just twin. Still no relativistic Poin standing, registration CP27 open. -/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxHeartbeats 420000
set_option linter.unusedSectionVars false
set_option maxRecDepth 4500
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common CF.Pannier.Chancel Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal InnerProductSpace Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open Lamour.Bridge.Celeste.Morn CF.Py.Rate.LocalLimit.Papal
open CF.Lamour.Bridge.Celeste
namespace Spine
open MacroGrid
open CF.Lamour.Bridge
open Aria Casting Six OS.Semigroup.Balloon
variable (P:Spine)(x:P.Spectrum0 3)(c r:ℕ→ℕ)(Z:Lead.Clan)
local notation "M"=>timeMesh P.par
local notation "X"=>P.ColorHil 3 (P.advocate 3 x 3)
local notation "Y"=>P.ManyF 3 (P.advocate 3 x 3)
local notation "ℰ" => P.physicalEnergy 3 (P.advocate 3 x 3)
local notation "R"=>P.seasons 3 (P.advocate 3 x 3)
local notation "ℓ"=>P.calibration.ℓ
local notation "Λ"=>P.kiosk 3 (P.advocate 3 x 3)
local notation "E"=> (ℰ).E
local notation "U"=> (R).E
local notation "V"=>P.advocate 3 x 3
local notation "E!" s:max i:max=> whenly (timeMesh P.par) s i
local notation "q'" n:max=> P.probeClock n 3
local notation "Q" i:max=> E! (c i) (q' (r i))
variable (A:ℕ→P.Apron)(n:ℕ→ℕ)
local notation "B" Z:max i:max=> P.stitchApron Z (A i) (c (n i)) (r (n i))
abbrev sentK (Z:Lead.Clan) (i:ℕ) := E (P.zt (B Z i))* (A i).engine P 3 (P.advocate 3 x 3)* (demerit Z • E (P.zt (A i) + P.zt (A i) + Q (n i)))
structure Snapdragon :Prop where
 allow : P.HandleWith x c r A n
 fund (Z:Lead.Clan)(i:ℕ): ‖(B Z i).engine P 3 (P.advocate 3 x 3)- P.sentK x c r A n Z i‖≤ P.macroStep i
private lemma choosePh {W:ℕ→ℕ→Prop} (p:∀ i,∀ᶠ j:ℕ in atTop,W i j):∃ n:ℕ→ℕ,StrictMono n ∧ ∀ i,W i (n i):=by
 choose h u using fun i=> eventually_atTop.1 (p i)
 let g:ℕ→ℕ := Nat.rec (h 0) (fun i v=>max (h (i+1)) (v+1))
 exact ⟨g,strictMono_nat_of_lt_succ fun i=> (Nat.lt_succ_self _).trans_le (le_max_right (h (i+1)) (g i+1)),fun i=> u i (g i) (by cases i; exact le_refl _; exact le_max_left ..)⟩
lemma hovered (G:P.LargeM c r){K:P.Register}{J:P.Ellis 3 x}(V':P.Experiment K c r x J):∃ n,Snapdragon P x c r A n:=by
 let F i Z (j:ℕ):=(P.stitchApron Z (A i) (c j) (r j)).engine P 3 V-P.sentK x c r A (fun _=>j) Z i
 let A0 (i j:ℕ)(k:Lead.Clan): X:=(A i).engine P 3 V (E (((A i).realWidth P 3).toNNReal) (P.shard x k (c j) (r j)))
 let T' (i:ℕ)(k:Lead.Clan): X:= demerit k • (A i).engine P 3 V (P.colorZero 3 V)
 have h(i):∀ᶠ j in atTop,∀ Z, ‖F i Z j‖ ≤ P.macroStep i ∧ ‖A0 i j Z-T' i Z‖ ≤ P.macroStep i:=by
    apply eventually_all.mpr; intro k
    let v:=((A i).realWidth P 3).toNNReal; have hv:0<v:= Real.toNNReal_pos.mpr ((A i).real_width_pos P 3)
    let t:=(A i).engine P 3 V; have he: Tendsto (fun j:ℕ=> A0 i j k) atTop (𝓝 (T' i k)):=by
       have he:Tendsto (fun j:ℕ=> A0 i j k) atTop (𝓝 (t (demerit k • P.colorZero 3 V))):= (t.continuous.tendsto _).comp (thin_front_shard_tendsto k V' (fun _=>v) (thin_compare_dew V' hv _ (Eventually.of_forall fun _=>le_refl v)))
       rw [map_smul] at he; exact he
    have t':Tendsto (fun j=>‖F i k j‖) atTop (𝓝 0):= tendsto_zero_iff_norm_tendsto_zero.mp (P.sword_moves x c r k (A i) G V'.launch.smaller); exact (t'.eventually (ge_mem_nhds (P.macroStep_pos i))).and ((tendsto_iff_norm_sub_tendsto_zero.1 he).eventually (ge_mem_nhds (P.macroStep_pos i)))
 obtain ⟨n,g,q⟩:= choosePh (fun i=> (V'.launch.smaller.tendsto_atTop.eventually (eventually_ge_atTop (A i).s)).and ((V'.launch.eager.tendsto_atTop.eventually (eventually_gt_atTop P.calibration.ℓ)).and (h i)))
 exact ⟨n,⟨g,fun i=> (q i).1, fun i=>(q i).2.1, fun i Z=> ((q i).2.2 Z).2⟩,fun Z i=> ((q i).2.2 Z).1⟩
section bar
-- projection to ManyF. Real prices kiosk nonmultiplicative; only Calendars payment on it.
lemma projectionLingo (F:(X).Op)(u v:ℝ≥0): Λ (E u * F* E v)= U u * Λ F * U v:=by
 rw [mul_assoc,mul_assoc]; exact P.kiosk_heat 3 V u v F
lemma bookRig (L:P.Apron): (P.zt L:ℝ)= L.realWidth P 3:= (natural_time ..).symm
lemma stampPoint (L:P.Apron) (a b:ℝ≥0)(p:P.zt L≤a)(q:P.zt L≤b) : P.pillar 3 V L (-(a:ℝ)) (b:ℝ) 0= U (a-P.zt L)*Λ (L.engine P 3 V)* U (b-P.zt L):=by
 let v:= P.zt L; let A: (X).Op:= L.engine P 3 V
 unfold pillar Apron.time_panel Apron.time_edge; rw [Pi.zero_apply, zero_add, ← P.bookRig]
 have hp(x:ℝ≥0)(h:v≤x): x-v=((x:ℝ)-v).toNNReal:=by rw [← NNReal.coe_sub h, Real.toNNReal_coe]
 rw [show (0:ℝ)- ↑v - -(a:ℝ)= (a:ℝ)-v by abel, ← hp a p, ←hp b q,show P.tableau 3 V 0 _ =Λ A from ?_,mul_assoc]; rfl
 unfold kiosk tableau
 rw [neg_zero,P.cart_zero]; rfl
end bar
variable {f:ℝ → (P.ManyF 3 (P.advocate 3 x 3)).Op}
variable (G:P.LargeM c r)(S:Snapdragon P x c r A n)
open SatinTails
local notation "V'" L:max a:max t:max => P.pillar 3 V L (- (a:ℝ)) (t:ℝ) 0
include S G
variable (D:P.ActualScarab x A 3 [] f)
include D
private lemma dstar : Tendsto (fun i=>P.zt (A i)) atTop (𝓝 0):= by
 apply NNReal.tendsto_coe.mp; change Tendsto (fun i:ℕ=>(P.zt (A i):ℝ)) atTop (𝓝 0)
 simp_rw [P.bookRig]; exact D.prices.thin
lemma dragon_stamps : Tendsto (fun i=> P.zt (B Z i)) atTop (𝓝 0):=by
 apply NNReal.tendsto_coe.mp; change Tendsto (fun i:ℕ=>(P.zt (B Z i):ℝ)) atTop (𝓝 0)
 have h:= D.prices.thin
 have hu:= (P.edelweiss 3 c r G Z).comp S.allow.fast.tendsto_atTop; have hu:Tendsto (fun i=>(Q (n i):ℝ)) atTop (𝓝 ((0:ℝ≥0):ℝ)):= NNReal.tendsto_coe.mpr hu -- coe direction!
 have hv:= (h.add (h.const_mul 3)).add hu; rw [NNReal.coe_zero] at hv; rw [mul_zero,zero_add,zero_add] at hv
 refine hv.congr fun i=>?_; rw [P.bookRig,P.stitch_width 3 Z _ (S.allow.already _)]; symm;
 change _ + _ + _= (((A i).realWidth P 3 + _) + ((Q (n i)):ℝ))
 rw [show P.probeWidth _ _ _=((Q (n i)):ℝ) from natural_time ..]; rfl
omit D S G
private lemma Brakes_together {X':Hilbert}{A L:ℕ→X'.Op}{a b:X'.Op}(p:Brakes A a)(q:Brakes L b): Brakes (fun i=> A i + L i) (a+b):=by
 obtain ⟨r,h⟩:=p.costs; obtain ⟨s,t⟩:=q.costs
 refine ⟨⟨r+s,(h.and t).mono fun i u=> (norm_add_le ..).trans (add_le_add u.1 u.2)⟩,fun y=> (p.brakes y).add (q.brakes y),fun y=>?_⟩
 simp_rw [star_add]; exact (p.heels y).add (q.heels y)
include S G D
lemma snapBrakes(t:ℝ≥0)(p:0<t): Brakes (fun i=> V' (B Z i) t t) (demerit Z • f t):=by
 let C':=P.kiosk 3 V; obtain ⟨U0,hU⟩:=P.kioskL 3 V
 have h1(X':(X).Op): U0 X'=C' X':=hU X'
 let W(i):= P.zt (B Z i); have hW:Tendsto W atTop (𝓝 0):= P.dragon_stamps x c r Z A n G S D -- order
 let Z'(i):= P.zt (A i); have hZ:Tendsto Z' atTop (𝓝 0):=P.dstar x c r A n G S D -- may C R via includes
 let R'(i):=(A i).engine P 3 V; let L'(i):=(B Z i).engine P 3 V
 let C₁(i):=P.sentK x c r A n Z i
 have hy:Tendsto (fun i=> L' i-C₁ i) atTop (𝓝 0):=by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr; exact squeeze_zero (fun i=> norm_nonneg _) (fun i=> S.fund Z i) P.macroStep_zero
 let Q₀(i:ℕ):= U0 (L' i-C₁ i); have hp0: Tendsto Q₀ atTop (𝓝 0):= by
    have hh:= U0.continuous.continuousAt.tendsto.comp hy; rw [map_zero] at hh; exact hh
 let f₀(i:ℕ):=t-W i; have hu:Tendsto f₀ atTop (𝓝 t):=by simpa only [tsub_zero] using ((tendsto_const_nhds (x:=t)).sub hW)
 let v(i):= U (f₀ i); let Y'(i):= v i * Q₀ i * v i
 have hv: Brakes v (U t):=Brakes.heatT _ hu
 have hx:Brakes Y' 0:= ((hv.weave (Brakes.by_budget hp0)).weave hv).sameC (Eventually.of_forall fun i=>rfl) (by simp)
 -- competition: C1 onto Y stamps at smaller R = t/2. require pad sufficient. right slack U(2Z+q) added
 let P₁:=t/2; have hp₁:0<P₁:=half_pos p; have ht₁:P₁+P₁=t:= add_halves _
 let V₀(i):=(V' (A i) P₁ P₁); let B':=f ↑P₁
 have hb:Brakes V₀ B':=by
    have h:= D.prices.paid P₁ hp₁; simp_rw [one_smul] at h; exact h
 let q(i):=Z' i+Z' i + Q (n i)
 have hq:Tendsto q atTop (𝓝 0):=by have h:=((hZ.add hZ).add ((P.edelweiss 3 c r G Z).comp S.allow.fast.tendsto_atTop)); rw [zero_add,zero_add] at h; exact h
 let l(i):=P₁-Z' i; have hl:Tendsto l atTop (𝓝 P₁):=by simpa only [tsub_zero] using ((tendsto_const_nhds (x:=P₁)).sub hZ)
 let u'(i):=f₀ i+ W i; let w'(i):= q i+f₀ i; have heY:Tendsto u' atTop (𝓝 t):=by simpa only [add_zero] using hu.add hW
 have heZ:Tendsto w' atTop (𝓝 t):= by simpa only [zero_add] using hq.add hu
 let L₀(i):= U (u' i-l i); let L₁(i):= U (w' i-l i); let Lℰ:= U (t-P₁); let F₀(i):= demerit Z • (L₀ i * V₀ i*L₁ i); let B₁:= f ↑t
 have hx0:P₁ ≤ t:= by simpa only [ht₁] using (le_self_add : P₁ ≤ P₁+P₁)
 have h0 : B₁=Lℰ*B'*Lℰ:=by
    have h:= Mosaic.tariff _ _ _ _ _ D.prices (t:ℝ) (P₁:ℝ) hp₁ hx0
    rw [← NNReal.coe_sub hx0,Real.toNNReal_coe] at h; exact h
 have hFix: Brakes (fun i=> F₀ i) (demerit Z • f (t:ℝ)) := (( (Brakes.heatT (R) (heY.sub hl)).weave hb).weave (Brakes.heatT (R) (heZ.sub hl))).pump (demerit Z)|>.sameC (Eventually.of_forall fun i=>rfl) (congrArg (fun p:(Y).Op=> demerit Z • p) h0.symm)
 apply (Brakes_together hx hFix).sameC _ (zero_add ..)
 filter_upwards [hZ.eventually (ge_mem_nhds hp₁), hW.eventually (ge_mem_nhds p), heY.eventually (le_mem_nhds (half_lt_self p)), heZ.eventually (le_mem_nhds (half_lt_self p))] with i hg he vj hj
 have X₁:v i * C' (L' i) * v i=V' (B Z i) t t:= (P.stampPoint x (B Z i) t t he he).symm
 have hq(v l):U v* U l= U (v+l):= ((R).time v l).symm
 have hw0:l i ≤ P₁:=tsub_le_self
 have hM: L₀ i * U (l i)=v i * U (W i):=by
    unfold L₀ v; rw [hq,hq, tsub_add_cancel_of_le (hw0.trans vj)]
 have hN: U (l i)*L₁ i=U (q i)*v i:=by
    unfold L₁ v; rw [hq,hq,add_tsub_cancel_of_le (hw0.trans hj)]
 have hr: F₀ i = v i * C' (C₁ i) * v i := by
    have hx :C₁ i=demerit Z •( E (W i)* R' i* E (q i)):= Algebra.mul_smul_comm ..
    unfold F₀
    rw [hx]
    unfold C'
    rw [P.kiosk_scale,P.projectionLingo, Algebra.mul_smul_comm,Algebra.smul_mul_assoc]
    apply congrArg (fun p:(Y).Op=> demerit Z • p)
    unfold V₀
    rw [stampPoint P x _ _ _ hg hg]; change L₀ i * (U (l i)* C' (R' i)* U (l i))*L₁ i=v i* _* v i
    calc
       _=(L₀ i*U (l i))* C' (R' i)*(U (l i)*L₁ i):= by simp only [mul_assoc]
       _=_:= by rw [hM,hN]; simp only [mul_assoc]; rfl
 change Y' i + F₀ i=_; unfold Y' Q₀; rw [hr, map_sub, h1 (L' i), h1 (C₁ i),mul_sub,_root_.sub_mul,sub_add_cancel,X₁]
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
