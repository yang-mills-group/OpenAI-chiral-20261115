import Anomaly.PinLocal
import YM.CF.Chaff.Temp
import YM.CF.Sour.Breeze
/-!
In a full **constant-width** angle chart, retain the support prices
BEFORE masking & Loom. (Kernel provisions VII, XIX/XXI.) Also
Lor verification of offsets later can pay uniformly in support
extent.

Credit jet scaffolds Breeze,Temp etc. of project for part of the proofs.
-/
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Swell
open Function NormedSpace Filter Metric Finset Lattice MeasureTheory RG
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Classical Kronecker
open Cube Lat Tenant Tulip Spire Scroll Scree Jet Skye Pastry Dial Fock Branch Drapes Rill
section
open scoped Matrix.Norms.Frobenius
private lemma Sonar.termsHis {n:ℕ}{b c:ℝ}{X:Type}[NormedAddCommGroup X][NormedSpace ℝ X]{x:X}{F T:X→SU.group.El}(h:Tender F x b n)(w:b≤c)(g: F=ᶠ[𝓝 x] T):Tender T x c n:= (h.bag w).same (g.mono fun i hi=>congrArg SU.group.mat hi) -- tune
end
open scoped Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
namespace Sonar
variable {n:Side}{d α : ℝ}
local notation "G" => SU.group
local notation "Φ" => tangD n
abbrev fenceP (n:Side) (d:ℝ) := {U:Pane n|Guard U d}
theorem insideQ (v:fenceP n d) (h:0<d) : (profile v.val)∈Openc (More n) d:= ⟨v.val,v.property,by simpa using h⟩
-- angular budget, on real scans WHICH use Openc. offset allowed.
abbrev mintQ (σ K:ℝ) (d:ℝ) (l:ℕ):Prop:= 0<σ ∧ σ ≤ 1 ∧ 0<K ∧
   (∀ {n:Side}(x:tangD n), ‖x‖ < σ → Guard (increment 1 x) d) ∧
   ∀ {n:Side}(F:Raw (Openc (More n) d) (Single n)) {S:Seal (Seat n)} (W:Toll (Single n)), Suite (badge _) (bail n d) (bail n d) S W F →
   ∀ (U:Pane n → Op (Single n)), (∀ (i:fenceP n d)(q:0<d), U i.val=F ⟨profile i.val,insideQ i q⟩) → ∀ x:tangD n, ‖x‖ < σ → ∀ i j, Allows l (fun y=> U (increment 1 y) i j) x (K*W i j)

lemma answer (h:0<d)(n:ℕ):∃ σ K:ℝ, mintQ σ K d n:=by
 obtain ⟨b,hb,V⟩ := opus_b n h
 obtain ⟨C,hC,H⟩ := Rill.funding n
 have hv:0<C:=zero_lt_one.trans_le hC
 obtain ⟨σ,s,u,Q⟩ := Chaff.toll_y h
 let a:=min 1 (b/C); have hx:0<a:=lt_min zero_lt_one (div_pos hb hv); let ε := min a σ
 have hp:0<ε:=lt_min hx s
 have he:ε≤a ∧ ε ≤ σ:=⟨min_le_left ..,min_le_right ..⟩
 refine ⟨ε,max 1 (ε⁻¹ ^ n),hp,he.2.trans u,zero_lt_one.trans_le (le_max_left ..),fun x t=> Q _ _ (guard0 le_rfl) x (t.trans_le he.2),?_⟩
 intro N F S W k U p x t i j
 let L:=ε • ContinuousLinearMap.id ℝ (tangD N)
 let D:=ε⁻¹ • ContinuousLinearMap.id ℝ (tangD N)
 have hg(y:tangD N):L (D y)=y:=smul_inv_smul₀ hp.ne' y
 let f(y:tangD N):Pane N:=increment 1 (L y); let Y(y:tangD N):fenceP N d:= if e:‖L y‖<σ then ⟨f y,Q _ _ (guard0 le_rfl) _ e⟩ else ⟨1,guard0 h.le⟩
 let x':= D x
 have hs:‖L x'‖<σ:=by unfold x'; rw [hg]; exact t.trans_le he.2
 have hj:∀ᶠ y in 𝓝 x',‖L y‖<σ:= L.continuous.continuousAt.norm.tendsto.eventually (gt_mem_nhds hs)
 have hm: Y x'=⟨f x',Q _ _ (guard0 le_rfl) _ hs⟩:=dif_pos hs
 have he'(i:Edge (Site (More N))) : Tender (fun y=> (Y y).val i) x' b n:=by
    let T:tangD N→L[ℝ]SU.group.Color:= ContinuousLinearMap.proj i ∘L L
    have hw: ‖L‖≤ε := Newt.pole0 _ (tangD N) (tangD N) hp.le
    have ht:Allows n T x' ε:= allows_linear (ContinuousLinearMap.opNorm_le_bound T hp.le (fun q=> (norm_le_pi_norm (L q) i).trans ((L.le_opNorm q).trans (mul_le_mul_of_nonneg_right hw (norm_nonneg _))))) ((norm_le_pi_norm (L x') i).trans (by unfold x'; rw [hg]; exact t.le))
    refine termsHis (H T x' ε ht (he.2.trans u)) (by rw [mul_comm]; exact (le_div_iff₀ hv).1 (he.1.trans (min_le_right ..))) ?_
    filter_upwards [hj] with y hy; change SU.group.lieExp (T y)=(Y y).val i; unfold Y; rw [dif_pos hy]; exact (mul_one _).symm
 have hA := V F W k (tangD N) (fun y=> ⟨_,insideQ (Y y) h⟩) x' (fun y=> (Y y).val) (fun y=>rfl) (Y x').property (fun y _=> he' y) i j
 have hz: Allows n (fun y=> U (f y) i j) x' (W i j):=by
    apply hA.germ; filter_upwards [hj] with y hy
    exact (congrArg (fun x:Op (Single N)=> x i j) (p _ h)).symm.trans (by unfold Y; rw [dif_pos hy]) -- p infer
 let g(y:tangD N):=U (f y) i j
 have ha : Allows n (g ∘ D) x ((W i j) * (ε⁻¹ ^ n)):=by
    constructor; exact hz.smooth.comp x D.contDiff.contDiffAt
    intro k hk; rw [Push.Uniform.iter_lin_at (hz.smooth.of_le (by exact_mod_cast hk))]; apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le ..).trans; simp only [prod_const,card_univ,Fintype.card_fin]
    apply mul_le_mul (hz.norm_le k hk) _ (by positivity) hz.nonneg
    refine (pow_le_pow_left₀ (norm_nonneg _) (Newt.pole0 _ (tangD N) (tangD N) (inv_nonneg.mpr hp.le)) _).trans (pow_le_pow_right₀ ((one_le_inv₀ hp).mpr (he.2.trans u)) hk)
 exact (ha.mono (by rw [mul_comm]; exact mul_le_mul_of_nonneg_right (le_max_right ..) hz.nonneg)).germ (Eventually.of_forall fun y=> by dsimp only [Function.comp_apply,g,f]; rw [hg]) -- direction of germ
variable {S:Sa n}{W:Toll (Single n)}{F:Raw (Openc (More n) d) (Single n)}
-- totalize on Guard. agrees locally whenever both in Guard.
noncomputable def lens (p:0<d)(F:Raw (Openc (More n) d) (Single n)) (u:Pane n) := if h:Guard u d then F ⟨profile u,insideQ ⟨u,h⟩ p⟩ else 0
abbrev soloQ (p:0<d)(F:Raw (Openc (More n) d) (Single n))(v:Pane n):= Matrix.trace (lens p F v)
variable (p:0<d) (h:Suite (badge _) (bail n d) (bail n d) S W F)
include h

lemma coinLocal {u v: fenceP n d} (t: Agrees S u.val v.val) : lens p F u.val=lens p F v.val:=by
 rw [lens,lens,dif_pos (show Guard _ _ from u.property),dif_pos (show Guard _ _ from v.property)]; ext i j
 let x: Openc (More n) d := ⟨_,insideQ u p⟩; let y: Openc (More n) d:=⟨_,insideQ v p⟩
 have hx: (forum n d).eval S x y=0:=by
    change fare S _ _/ _=0; rw [show fare S x.val y.val=0 from ?_,zero_div]; refine sum_eq_zero fun i hi=>?_
    have hp:= (mem_filter.mp hi).2; have hh:x.val i=y.val i:=by change profile u.val i=profile v.val i; funext b; unfold profile; rw [t i hp.1 hp.2]
    simp only [hh,sub_self,norm_zero] -- tune
 have he:= (h.expo i j).variation x y; rw [hx,mul_zero,norm_le_zero_iff] at he; exact sub_eq_zero.mp he

lemma taxLocal (u :fenceP n d) (f:Seat n→SU.group.El) : soloQ p F (gauge f u.val)=soloQ p F u.val := by
 let x: Openc (More n) d:=⟨_,insideQ u p⟩; let y:=(forum n d).drive f x
 have hv := (h.toTicket.frame.frame f x) -- which frame signature
 unfold soloQ lens; rw [dif_pos (show Guard _ d from (show Guard u.val d from u.property).cov f),dif_pos (show Guard _ _ from u.property)]
 have he : y.val = profile (gauge f u.val):=by rw [profile_g]; rfl
 rw [←show y=⟨profile (gauge f u.val),_⟩ from Subtype.ext he]
 change Matrix.trace (F y)=Matrix.trace (F x); -- intertwiners
 -- tune
 rw [show F y= _ from hv,Matrix.trace_mul_cycle,((bail n d).run f).property.1,one_mul]
lemma penchant {σ K:ℝ}{m:ℕ} (a: mintQ σ K d m){x:Φ}(q:‖x‖<σ): Allows m (fun y=> soloQ p F (RG.increment 1 y)) x (K*ledgerV W):=by
 let J:= lens p F
 have hu(i:fenceP n d)(q:0<d): J i.val=F ⟨_,insideQ i q⟩:=dif_pos i.property
 have ht:= a.2.2.2.2 F W h J hu x q
 refine (allows_sum (f:=fun i:Single n=> fun w:Φ=> J (increment 1 w) i i) (s:=univ) (fun i _=>ht i i)).mono ?_
 unfold ledgerV; rw [←mul_sum]; exact mul_le_mul_of_nonneg_left (sum_le_sum fun i _=> single_le_sum (fun j (_:j∈(univ:Finset (Single n)))=>h.nonn i j) (mem_univ i)) a.2.2.1.le -- tune
lemma zeroD (P: DifferentiableAt ℝ (fun x:Φ=> soloQ p F (increment 1 x)) 0) {σ K:ℝ}{l:ℕ}(t:mintQ σ K d l):fderiv ℝ (fun y:Φ=>soloQ p F (increment 1 y)) 0=0 := by
 apply ContinuousLinearMap.ext; apply Stationary.slot_fixed Thera.yet_one
 intro u x; let A: Φ→L[ℝ] Φ:= ContinuousLinearMap.pi (fun i=> (SU.group.adjoint u).toContinuousLinearMap ∘L ContinuousLinearMap.proj i); apply Stationary.chain_fixed A _ P x
 filter_upwards [ball_mem_nhds 0 t.1] with z hz
 let f:Seat n→SU.group.El:=fun _=>u; let V:fenceP n d:=⟨increment 1 z,t.2.2.2.1 _ (mem_ball_zero_iff.mp hz)⟩
 rw [Function.comp_apply,show increment (1:Pane n) (A z)=gauge f V.val from ?_]; exact taxLocal p h V f
 funext i; change SU.group.lieExp (SU.group.adjoint u (z i))*1= u* (SU.group.lieExp (z i)*1)*_; rw [mul_one,mul_one]; exact Next.SectorChange.exp_adjoint ..
end Sonar
end YM.CF.Swell
