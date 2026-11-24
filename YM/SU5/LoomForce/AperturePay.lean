import YM.SU5.LitCurrent.Source
import YM.SU5.LitCurrent.Light
import YM.CF.Chaff.Sky
import YM.CF.Sour.Fro
import YM.Next.RANK.LineBox
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 2000
set_option maxHeartbeats 500000
noncomputable section
namespace YM.CF.LitCurrent.Surplus
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour
open Stax Skye Jet Scroll Finset Palot Cadre Vow RG Rive Nor Hake MeasureTheory
open Metric Drapes Tulip Lat Branch Cube Tenant
section
open scoped Topology Matrix.Norms.Frobenius Classical
open Rill
private lemma tGerm {N:Type} [NormedAddCommGroup N][NormedSpace ℝ N] {A B : N→ SU.group.El}{b:ℝ}{x:N}{k:ℕ}
    (e:Rill.Tender A x b k)(p:A =ᶠ[𝓝 x] B): Rill.Tender B x b k:=
  e.same (p.mono fun _ e'=> congrArg SU.group.mat e')
end
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical ContDiff
attribute [local instance] opCStarAlgebra
open Rush SU Prism Nacre Laic Tap Levier Thera Moto Oath Font Haro Spire Dial Rill
open Kennel Swell StressExchange
variable {N:Side}{P T:SOp N}{a b d v g t u:ℝ}{r k:ℕ}
variable (B:StageTree N d (4*a) v)
abbrev untouched (k:ℕ) (U:Pane N) := (beforePing B k (profile U)).trace
local notation "A" => tangD N
open Next.Rank.Spindle (progress upon)
-- even on whole regulator p. first trace cutoff k any size
variable {o:Seat N} (m:moored o B)(ha:0<a)(hd:0<d)
include hd m ha
lemma holdsTrace {V:Pane N} (Q:HopeT d b g 3) (hV:Guard V (d/2)) :
  Allows 3 (fun x:A=> untouched B k (increment V (g • x))) 0 (expiry (4*a) v) := by
  let F(x:A):=increment V (g • x); let f:=untouched B k
  obtain ⟨s,e,-,c⟩:= Chaff.toll_y (half_lt_self hd)
  let L(x:A):= if ‖g • x‖<s then F x else F 0
  have h:∀ x,Guard (L x) d:=by intro x; unfold L; split; exact c N V hV _ (by assumption); exact c N V hV _ (by simpa using e)
  let H(x:A): Openc (More N) d:=⟨profile (L x),⟨_,h x,(show ‖profile (L x)-profile (L x)‖<d by simpa using hd)⟩⟩
  have ht: F =ᶠ[𝓝 0] L:= by
    have he: ∀ᶠ x:A in 𝓝 0, ‖g • x‖ < s:= ((show Continuous (fun x:A=>‖g • x‖) by fun_prop).tendsto 0).eventually (gt_mem_nhds (by simpa using e))
    exact he.mono fun _ g=> (if_pos g).symm
  have hs(S:Sa N)(i j: Single N): Allows 3 (fun x:A=> B.F S () (H x) i j) 0 (B.W S i j):= by
    refine Q.warm (F:= B.F S ()) (B.W S) ((B.coat S).1 ()) _ H 0 L (fun _=> rfl) (h _) ?_ i j
    intro x _; let K:= (ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _ :Edge (Site (More N))=> group.Color) x); have hp: ‖g • K‖≤g:= by rw [norm_smul,Real.norm_eq_abs,abs_of_pos Q.peta]; exact mul_le_of_le_one_right Q.peta.le (ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun y=> (norm_le_pi_norm y x).trans_eq (one_mul _).symm))
    have he:Tender (fun y:A=> F y x) 0 b 3:= Q.until' A (g • K) (V x) hp
    exact tGerm he (ht.mono fun i (v:_ = _) => congrFun v x)
  let Dk:= (univ:Finset (Sa N)).filter (fun i=>i.card<k)
  let L'(x:A):= ∑ i∈Dk,∑ j:Single N,B.F i () (H x) j j
  let y:= expiry (4*a) v
  have hu:L' = fun (x:A) => f (L x):=by
    funext x; unfold L' f untouched; rw [show profile (L x)=(H x).val from rfl,beforePing, dif_pos (H x).property,retain,←Finset.sum_filter,Matrix.trace_sum]; rfl
  have hy:Allows 3 L' 0 (∑ i∈ Dk,∑ j:Single N,B.W i j j):=allows_sum fun i _=> allows_sum fun j _=> hs i j j
  rw [hu] at hy
  apply Allows.mono (C:=(∑ i∈ Dk,∑ j:Single N,B.W i j j)) (Allows.germ hy (ht.mono fun x e=> congrArg f (Eq.symm e)))
  apply le_trans _ (saw_line B m (by positivity : 0< 4*a))
  have hx(i:Sa N)(j k:Single N):0 ≤ B.W i j k:=(B.coat i|>.1 ()).nonn j k
  unfold tallyC; refine le_trans (sum_le_sum_of_subset_of_nonneg (subset_univ Dk) (fun i _ _=>sum_nonneg fun j _=>hx i j j)) (sum_le_sum fun i _=>?_)
  refine le_trans (sum_le_sum (s:= (univ:Finset (Single N))) (fun j _=>Finset.single_le_sum (f:=B.W i j) (fun k _=>hx i j k) (mem_univ j))) (show ledgerV (B.W i) ≤ _ from ?_)
  apply le_mul_of_one_le_left (sum_nonneg (fun j _=> sum_nonneg (fun k _=>hx i j k)))
  unfold Branch.rent; apply Real.one_le_exp; positivity

local notation "ℓq"=> untouched B
abbrev occupancy (a v x:ℝ):ℝ:= composeCost 3 (expiry (4*a) v) x⁻¹
lemma occupied {V:Pane N} (Q:HopeT d b g 3) (hV:Guard V (d/2)) :
    Allows 3 (ℓq k ∘ increment V) (0:A) (occupancy a v g):=by
  let L: A→L[ℝ] A:=g⁻¹ • ContinuousLinearMap.id ℝ A
  let F:= fun x:A=> untouched B k (increment V (g • x))
  have he: F ∘ L = untouched B k ∘ increment V:= by
    funext x
    simp only [Function.comp,F,L,_root_.smul_apply,ContinuousLinearMap.id_apply,smul_inv_smul₀ Q.peta.ne']
  have hp: ‖L‖ ≤ g⁻¹:= by
    unfold L; rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr Q.peta.le)]
    exact mul_le_of_le_one_right (inv_nonneg.mpr Q.peta.le) (ContinuousLinearMap.norm_id_le (E:=A))
  rw [← he]; exact Allows.comp (f:=L) (show Allows 3 F (L 0) _ from by rw [map_zero]; exact holdsTrace B m ha hd Q hV) (allows_linear hp (by rw [map_zero,norm_zero]; exact (norm_nonneg _).trans hp))

omit hd m ha
-- Taylor on true link-profile readings; no regularity beyond the stated ray/roll costs.
-- Real and complex conventions; mapPoly cost otherwise.
def dollH (F : Pane N→ℂ) (X : A) : ℂ := (2:ℝ)⁻¹ • fderiv ℝ (fderiv ℝ (F∘increment 1)) 0 X X

variable (F : Pane N→ℂ) {C ρ : ℝ}
lemma uniform_roll (ρ:ℝ)(hρ:0< ρ)(h:∀ x:A, ‖x‖ ≤ ρ→ Allows 3 (F∘increment (increment 1 x)) 0 C) (L:fderiv ℝ (F∘increment 1) 0=0) (X:A)(p:‖X‖≤ρ): ‖F (increment 1 X)-F 1-dollH F X‖ ≤ C*‖X‖^3:= by
  rcases eq_or_ne X 0 with q|q
  · rw [q]; simp [dollH]
  let v:=‖X‖; have hv:0<v:= norm_pos_iff.mpr q; let Y:=v⁻¹ • X
  have hz: v • Y=X:= smul_inv_smul₀ hv.ne' _
  have hy: ‖Y‖=1:=by unfold Y; rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hv),inv_mul_cancel₀ hv.ne']
  let I:=Set.Icc (0:ℝ) ρ; let g(x:A):= F (increment 1 x); let f(t:ℝ):=g (t • Y)
  have h0:Allows 3 g 0 C:= by have ht:=h 0 (by rw [norm_zero]; exact hρ.le); simp only [Work.G07.at_zero_increment] at ht; exact ht
  have hm (t)(ht:t∈I): ContDiffAt ℝ (↑(3:ℕ)) f t ∧ ‖iteratedDeriv 3 f t‖≤ C:= by
    let G := F∘increment (increment 1 (t • Y))
    have he: Allows 3 G (0:A) C:= h _ (by rw [norm_smul,Real.norm_eq_abs, abs_of_nonneg ht.1,hy,mul_one]; exact ht.2)
    have hf (i:ℝ): f (t+i)=G (i • Y):=congrArg F (progress 1 Y t i)
    refine ⟨?_,?_⟩
    · rw [show f=(fun u:ℝ=> G ((u-t) • Y)) from funext (fun u=> by rw [←hf, add_sub_cancel])] 
      exact ContDiffAt.comp t (show ContDiffAt ℝ (↑(3:ℕ)) G _ from by simpa only [sub_self, zero_smul] using he.smooth) (f:=fun u=> (u-t) • Y) (by fun_prop)
    rw [show iteratedDeriv 3 f t=iteratedDeriv 3 (fun z=>f (t+z)) 0 from (by rw [iteratedDeriv_comp_const_add]; simp),funext hf,upon Y _ 3 he.smooth]; let g:=(iteratedFDeriv ℝ 3 G (0:A)); simpa only [hy,prod_const_one,mul_one] using (g.le_opNorm (fun _=> Y)).trans (mul_le_mul_of_nonneg_right (he.norm_le _ (by decide)) (prod_nonneg (fun i _=>norm_nonneg _)))
  have hv':v∈I:=⟨hv.le,p⟩
  have hb(t:ℝ)(i:ℕ)(p:i≤3)(ht:t∈I): iteratedDerivWithin i f I t = iteratedDeriv i f t:= iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hρ) ((hm t ht).1.of_le (by exact_mod_cast p)) ht
  have hw:‖f v - taylorWithinEval f 2 I 0 v‖ ≤ C*(v-0)^(2+1)/(2:ℕ).factorial:=taylor_mean_remainder_bound hρ.le (fun t u=> (show ContDiffWithinAt ℝ (↑(2+1:ℕ)) f I t from (hm t u).1.contDiffWithinAt)) hv' (fun t e=> by rw [hb _ _ (by decide) e]; exact (hm t e).2)
  have hl: iteratedDeriv 1 f 0=0:= by rw [show f=_ from (show f=(fun t:ℝ=>g (t • Y)) from rfl),upon Y _ 1 (h0.smooth.of_le (by norm_cast)),iteratedFDeriv_one_apply]; exact by rw [show fderiv ℝ g 0=0 from L]; rfl
  have he: taylorWithinEval f 2 I 0 v= F 1+dollH F X:= by
    rw [taylor_within_apply]; simp only [sub_zero];
    simp_rw [Finset.sum_range_succ]; rw [hb 0 0 (by decide) ⟨le_rfl,hρ.le⟩,hb 0 (0+1) (by decide) ⟨le_rfl,hρ.le⟩]
    rw [hb 0 2 (by decide) ⟨le_rfl,hρ.le⟩]; norm_num [Nat.factorial,hl]
    rw [show f 0= F 1 from by simp [f,g],show iteratedDeriv 2 f 0=_ from upon Y g 2 (h0.smooth.of_le (by norm_num)),iteratedFDeriv_two_apply]
    rw [← hz]; unfold dollH; simp_rw [map_smul,_root_.smul_apply]; unfold g; norm_num [Function.comp_def, Complex.real_smul]; ring
  change _ ≤ C*v^3; rw [sub_sub,←he, show F (increment 1 X)=f v from congrArg g hz.symm]
  exact hw.trans (by simp only [sub_zero]; apply div_le_self; exact mul_nonneg h0.nonneg (pow_nonneg hv.le _); norm_num [Nat.factorial])
#print axioms occupied
#print axioms uniform_roll
end YM.CF.LitCurrent.Surplus
