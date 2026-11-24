import Anomaly.Ward.Reach
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace YM.CF.Swell.Sonar
open Function NormedSpace Filter Metric Finset Lattice MeasureTheory RG
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Classical Kronecker
open Cube Lat Tenant Tulip Spire Scroll Scree Jet Skye Pastry Dial Fock Branch Drapes Rill
open Nacre Next.Rank.Spindle LampP Exterior Precision Wilson
open scoped Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
set_option synthInstance.maxSize 24000
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E]{f:E→ℂ}
variable {n:Side}{m:ℕ}{α C:ℝ}
-- Taylor.Left.Carry cube in x norm. need coefficient convention not raw derivative size.
lemma gaugeTaylor (r:‖(0:E)‖<α)(p:∀ x:E, ‖x‖<α→ Allows 3 f x C)(a: f 0=0)(h:fderiv ℝ f 0=0){x:E}(q:‖x‖<α):
 ‖f x-trim 2 f x‖ ≤ C*‖x‖^3:=by
 let U:= (ContinuousLinearMap.id ℝ ℝ).smulRight x; let L := f ∘ (U:ℝ→E)
 let W:=Set.Icc (0:ℝ) 1
 have hu : ContDiffAt ℝ (3:ℕ) f 0 :=(p _ r).1
 have he: ‖U‖ ≤ ‖x‖:= ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) (fun y=> by change ‖y • x‖ ≤ _; rw [norm_smul,mul_comm])
 have hk (t:ℝ)(hp:t∈W) : ‖U t‖<α:=by rw [← show t • x=U t from rfl,norm_smul,Real.norm_of_nonneg hp.1]; exact (mul_le_of_le_one_left (norm_nonneg x) hp.2).trans_lt q
 have hv(t:ℝ)(hp:t∈W): Allows 3 f (U t) C:=p _ (hk _ hp); have ht(t:ℝ)(hp:t∈W):ContDiffAt ℝ (3:ℕ) L t:=(hv _ hp).smooth.comp t U.contDiff.contDiffAt
 have ho: (0:ℝ)∈W:=Set.left_mem_Icc.mpr zero_le_one; have hb: (1:ℝ)∈W:= Set.right_mem_Icc.mpr zero_le_one
 have hh:=taylor_mean_remainder_bound (n:=2) (f:=L) zero_le_one (fun t h=> ((ht _ h).contDiffWithinAt.of_le (by norm_num))) hb (C:=C*‖x‖^3) ?_
 swap; · intro t h; have hf:= hv t h
         rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc zero_lt_one) (ht t h) h]
         change ‖iteratedFDeriv ℝ 3 (f ∘ U) t _‖ ≤ _; rw [Push.Uniform.iter_lin_at hf.smooth]
         change ‖iteratedFDeriv ℝ 3 f (U t) (fun _=> (1:ℝ) • x)‖ ≤ _; apply ((iteratedFDeriv ℝ 3 f (U t)).le_opNorm _).trans; change _* (∏ i:Fin 3, ‖(1:ℝ) • x‖) ≤ _; simp only [one_smul, prod_const,card_univ,Fintype.card_fin]; exact mul_le_mul_of_nonneg_right (hf.2 3 le_rfl) (pow_nonneg (norm_nonneg _) _)
 have hU: L 1=f x:=by change f ((1:ℝ) • x)=_; rw [one_smul]
 have H(k:ℕ)(h:k ≤ 3) : iteratedDerivWithin k L W 0=iteratedFDeriv ℝ k f 0 (fun _=>x):=(iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc zero_lt_one) ((ht _ ho).of_le (by exact_mod_cast h)) ho).trans (upon x f k (hu.of_le (by exact_mod_cast h))) -- missing args
 have hx:taylorWithinEval L 2 W 0 1=trim 2 f x:=by
    rw [taylor_within_apply,sum_range_succ,H 2 (by omega),sum_range_succ,H 1 (by omega),sum_range_one,H 0 (by omega),iteratedFDeriv_one_apply,h]
    simp only [ContinuousLinearMap.zero_apply,smul_zero,add_zero,zero_smul, iteratedFDeriv_zero_apply,a, zero_add,sub_zero,one_pow,mul_one]; rfl
 rw [hx,hU] at hh
 have ht:= (p _ r).nonneg; apply hh.trans; rw [sub_zero,one_pow,mul_one]; exact div_le_self (by positivity) (by norm_num [Nat.factorial])
variable {b k:ℕ}{S:Sa n}{d:ℝ}{W:Toll (Single n)}{F:Raw (Openc (More n) d) (Single n)} (u:Seat n)

local notation "Πp" => tangD n
local notation "Y" => fieldDir SU.group (More n) 1
variable (p:0<d) (h:Suite (badge _) (bail n d) (bail n d) S W F) (K:mintQ α C d m)
include K h
lemma feeLens (u:tangD n)(t:‖u‖<α): Allows m (fluxJet p F) u (2*C*ledgerV W):=by
 have hw:= (penchant p h K (show ‖(0:Πp)‖<α from norm_zero.trans_lt K.1)).value
 have hf : increment 1 (0:Πp)=(1:Pane n):=by funext i; simp [increment]
 exact (Newt.subtract_p (penchant p h K t) (allows_const _ (hf ▸ hw))).mono (by ring_nf; rfl) -- tune
lemma flatCut (q:2 ≤ m) :
 fderiv ℝ (fluxJet p F) 0=0 ∧ fluxJet p F 0=0 ∧ ‖cake 2 (fluxJet p F)‖ ≤ 2*C*ledgerV W:=by
 let A:=(penchant p h K (show ‖(0:Πp)‖<α from norm_zero.trans_lt K.1)).order q
 refine ⟨?_,?_,?_⟩
 · unfold fluxJet; rw [fderiv_sub_const]; exact zeroD p h (A.smooth.differentiableAt (by norm_num)) K
 · unfold fluxJet; simp [show increment 1 (0:Πp)=(1:Pane n) from (by funext i; simp [increment])]
 unfold cake; rw [norm_smul]; apply le_trans (mul_le_of_le_one_left (norm_nonneg _) (by norm_num [Nat.factorial])) ((feeLens p h K _ (norm_zero.trans_lt K.1)).norm_le _ q)

-- probe family independent version for Poker.Real.Index. String.
omit K h
abbrev TrackKey (G:Gauge)(n:Side):= Face (Per n) × G.ColorIndex -- Cell namespace path
abbrev ChainKey (G:Gauge)(n:Side):= Fin 2→ TrackKey G n
abbrev columnQ (G:Gauge)(n:Side) := TrackKey G n→ℝ
abbrev tableQ (G:Gauge)(n:Side)(E:Type):=ChainKey G n→E
def tariff {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E]{G:Gauge} {n:Side}(X:tableQ G n E)(f:columnQ G n): E:=∑ i,(∏ j,f (i j)) • X i
abbrev costs {G:Gauge}{n:Side}{E:Type}[NormedAddCommGroup E](T:tableQ G n E):ℝ:=∑ i,‖T i‖
abbrev receipt {G:Gauge} {n:Side} (u:fieldDir G n 1)(k:TrackKey G n):= (Work.F03.faceCurl k.1 u) k.2
abbrev Regional {G:Gauge}{n:Side}{E:Type}[NormedAddCommGroup E](o:Site n)(k:ℕ)(P:tableQ G n E):Prop:=∀ i, P i≠0 → ∀ j: Fin 2,(i j).1.1∈ halo k {o}
variable (q: 2 ≤ m)
abbrev expDice (b:ℕ)(κ D :ℝ):= ((b+b+1:ℕ)^4* Fintype.card PlaqAxes * Fintype.card SU.group.ColorIndex:ℝ)^2 * (2*κ* D * (4*b)^2)
include K q h
lemma party (t:S⊆halo b {u})(w:2*(b+1)<(More n).val):
 ∃ X: tableQ SU.group (More n) ℂ,costs X ≤ expDice b C (ledgerV W) ∧ Regional u b X∧∀ i:Y,trim 2 (fluxJet p F) (collect SU.group i)=tariff X (receipt i):=by
 obtain ⟨ht,v,r⟩:= flatCut p h K q
 let T:= cake 2 (fluxJet p F); let D:= (T.compContinuousLinearMap (fun _=> rowLine u (G:=SU.group) w))
 let J:= Turn b × SU.group.ColorIndex; let P:= Fin 2 → J
 let valQ(i:J): Turn b→ SU.group.Color:= Pi.single i.1 (EuclideanSpace.single i.2 1)
 let A(j:P):=D (fun i=> valQ (j i))
 let B(k:J): TrackKey SU.group (More n):=(LampP.column u k.1,k.2)
 let H(k:P): ChainKey SU.group (More n):= B ∘ k
 let X(i:ChainKey SU.group (More n)):=∑ j:P, if H j=i then A j else 0
 have ho: 0 ≤ ledgerV W:=by unfold ledgerV; exact sum_nonneg fun i _=>sum_nonneg fun j _=>h.nonn i j
 have hi:‖D‖ ≤ 2*C * ledgerV W * (4*b)^2:=by apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le ..).trans; rw [prod_const,card_univ,Fintype.card_fin]; apply mul_le_mul r (pow_le_pow_left₀ (norm_nonneg _) (row_fee u w) _) (by positivity) ((norm_nonneg _).trans r)
 have hv (k:J): ‖valQ k‖ ≤ 1:=by unfold valQ; apply (pi_norm_le_iff_of_nonneg zero_le_one).2; intro i; by_cases h:i=k.1<;>simp [Pi.single_apply,h]
 have hh(j:P): ‖A j‖ ≤ 2*C*ledgerV W*(4*b)^2:=by refine ((D.le_opNorm _).trans (mul_le_of_le_one_right (norm_nonneg _) (prod_le_one ?_ (fun i _=> hv _)))).trans hi; exact fun i _=> norm_nonneg _
 have hc: (Fintype.card P:ℝ) ≤ ((b+b+1:ℕ)^4* Fintype.card PlaqAxes * Fintype.card SU.group.ColorIndex:ℝ)^2:=by unfold P J; rw [Fintype.card_fun,Fintype.card_prod,Fintype.card_fin 2]; exact_mod_cast pow_le_pow_left₀ (Nat.zero_le _) (Nat.mul_le_mul_right (Fintype.card SU.group.ColorIndex) (halo_souls b)) 2
 refine ⟨X,?_,?_,?_⟩
 · apply le_trans (sum_le_sum (fun (i:ChainKey SU.group (More n)) (_: i∈univ)=> norm_sum_le univ (fun j:P=> if H j=i then A j else 0))); rw [sum_comm]; simp only [apply_ite (‖·‖),norm_zero,sum_ite_eq,mem_univ,ite_true]; refine (sum_le_sum (fun i _=> hh i)).trans ?_; rw [sum_const,card_univ,nsmul_eq_mul]; exact mul_le_mul_of_nonneg_right hc ((norm_nonneg _).trans hi)
 · intro i p j
   obtain ⟨k,_,B'⟩:=exists_ne_zero_of_sum_ne_zero p; split at B'; rename_i v; subst i; exact village_le _ (faceOrigin (k j).1); exact (B' rfl).elim
 intro U; let Z:=rayFace u U (b:=b)
 have hm: Z= ∑ i:J, receipt U (B i) • valQ i:=by rw [Fintype.sum_prod_type]; funext i; ext j; simp [valQ,Pi.single_apply,Z,B]; rfl -- tune
 rw [riseN u p h K q U t w]; change D (fun _=>Z)=_
 calc
 D (fun _=> Z)=∑ i:P, (∏ j, receipt U (H i j)) • A i:=by
    rw [hm,D.map_sum (fun _ i=> receipt U (B i) • valQ i)]
    exact sum_congr rfl (fun k _=> D.map_smul_univ _ _)
 _=tariff X (receipt U):=by unfold tariff X; simp_rw [smul_sum]; rw [sum_comm]; simp only [smul_ite,smul_zero,sum_ite_eq,mem_univ,ite_true]
end YM.CF.Swell.Sonar
