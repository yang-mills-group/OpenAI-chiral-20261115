import YM.CF.Cloak.Wing
import YM.Further.ROOTED_INTERACTING_REMAINDER.Vault
import YM.CF.Cloak.Wear
import YM.CF.Cloak.Mint
import YM.CF.Rill.Oboe
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.CF.Cloak
open Siete
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG PhysicalNext.JointLoad Heir Next.Foundations AnalyticBridge.SectorAffine AnalyticBridge.SectorAffine.Offset Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree Esti
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
open AnalyticBridge.Annulus1AD
open Ac
variable {c f:Side}(S:StepData c f){r v:ℕ}
open CF.Jet
local notation "G"=> SU.group
variable {S}{n:ℕ}{θ a b m x t w K C d:ℝ}
variable {K': Teller G}{A B:Stores S}{T:Tube G S}{V:Config G c}{U:Config G f}{k:S.Choices}{q:Chi}{E:Type}[NormedAddCommGroup E][NormedSpace ℝ E][Nonempty E]{x':E}
open AnalyticBridge.Annulus1AD Push.SectorMeasure.Oriented Pressure.Tube
variable {O:Stores S}{F: Forest S.ratio}{Y:LinkArray G (Frozen A x F)}{z:LogArray G (Active A x F)}{β Q γ D L M s:ℝ}{J:ChartRatio G}{P:Patch}
open Forge Reine Rill
open Vol Pressure.Tube
open Vol Cay Slate
variable {l:ℕ}{M:Monk G S}{s':ℝ}
open Further.RootedInteractingRemainder Precision Next.SectorChange
-- normative d-independent W. before width & threshold. Uniform for small Z, afterwards local clamp.
lemma orn(K:Teller G)(P:Patch)(p:P.Branches K.bind G)(n l:ℕ)(hp:2 ≤ n)(hl:l ≤18)(q:Chi)(W:Push.Uniform.Before G K.top.width K.top.paths K.j K.bind (n+2)) :∃ D d:ℝ,0<D∧0<d∧∀ A:ℝ,0<A→∃ r:ℝ,0<r∧∀ᶠ x in atTop,∀{c f:Side}(S:StepData c f)(T:Tube G S),Cert P K S T x→∀ (M:Monk G S)(m:ℝ), sizedP G P K S T M.park→ M.key.flags=RG.flags (temp x) M.V→∀ β∈Set.Icc (y G P.L x/2) (2*y G P.L x), let t:= fiery G x P.L;‖M.z‖ ≤ r*Scales.p G P.L x → MossX n l x M.key M.park T M.V M.k A m t q →
 (∀ i: Bond c,i.1∉ M.key.dome ((l+70)*radiusB x) → Pressure.wire (S.prediction (M.sent x T q m l β) M.k) M.V i ≤ D*t) ∧ (∀ i:Active M.key x M.park,S.ratio.parent i.val.val.1 ∉ M.key.dome ((l+62)*radiusB x)→ ‖M.rich x T q m l β i‖ ≤ d*t):=by
 obtain ⟨A,h,H⟩:= turnsX n l 1 zero_lt_one K P p hp hl W q
 obtain ⟨C,v,hC,hv,T⟩:= chord_chart_cost G; let g:=Push.Uniform.shade G; let d:=g*(A+1); have hg:0<g:=Push.Uniform.shade_pos _; have hd:0<d:=by unfold d; positivity
 let w:= (16:ℝ)*(2*((predReach P+1:ℕ):ℝ)+1)^5*Fintype.card PlaqAxes
 let b:= Vault.farePrice P K.bind; let L:=max 1 (2*w+|b| *(4*(C*d+2*w))); have hw:0≤w:=by unfold w; positivity
 refine ⟨L,d,zero_lt_one.trans_le (le_max_left ..),hd,fun Q hQ=>?_⟩; let r:ℝ:= (2*(2^n*Q))⁻¹; have hr:0<r:=by unfold r; positivity
 refine ⟨r,hr,?_⟩; filter_upwards [H,monitors G P.L,(year G P.L).eventually (eventually_gt_atTop 0),expM P (hp:=div_pos hv hd),Work.E01.radiusB_tendsto.eventually_ge_atTop (2*predReach P+1000)] with x hp hx hv' hr' hP c f S T' ht M m hu hV β hβ t hz hf
 have he:= ht.size; have hO:= hp S T' ht M.key M.park M.V hu hV M.k; rw [ht.got] at hO; let s':=r*Scales.p G P.L x; have hC':0<β:= (half_pos hv').trans_le hβ.1; have ht':0<t:=by unfold t; rw [Scales.fi]; exact mul_pos (Scales.gauge G _ hv') (Scales.pos ..)
 have hL:coupling β*(2^n*Q*s')≤t:=by
    refine (mul_le_mul_of_nonneg_right (compare_v G P.L x hβ hv').1 (by unfold s'; have hp:= Scales.pos G P.L x; positivity)).trans (Eq.le ?_) -- tune
    unfold t; rw [Scales.fi]; unfold s' r; field_simp
 have hM(i:Active M.key x M.park)(u:S.ratio.parent i.val.val.1∉_): ‖M.rich x T' q m l β i‖ ≤ d*t:=((wedge_h i n (show 0<s' from mul_pos hr (Scales.pos ..)) hz hQ.le hf hC' (show MossX n l x M.key M.park T' M.V M.k A (1*t) t q from hO) (by omega) u).trans ((mul_le_mul_of_nonneg_left (add_le_add le_rfl hL) hg.le).trans_eq (by unfold d g; ring))) -- orientation
 refine ⟨fun i p=>?_ ,hM⟩; let U:=M.sent x T' q m l β; let a:=C*(d*t); have hb: predReach S.patch+1 ≤ radiusB x:= by rw [ht.got]; omega
 have hh(j:Bond f)(z:separation i.1 (S.ratio.parent j.1)≤ predReach S.patch):∃ u:SU.group.El,U j=u*replica S.ratio M.V j∧ SU.group.chord u ≤ a:=by
    have hy:=afar_s _ _ _ (show i.1 ∉ halo ((l+70)*radiusB x) _ from p) (show (l+62)*radiusB x + separation (S.ratio.parent j.1) i.1 ≤ (l+70)*radiusB x from by rw [separation_comm]; simp_rw [Nat.add_mul]; omega); apply fieldP T' M j (d*t) a (by positivity) (by positivity) hC' hy (by omega); · intro u p; exact (T u (p.trans ((mul_comm d t).le.trans ((le_div_iff₀ hd).mp hr')))).trans (mul_le_mul_of_nonneg_left p hC.le)
    intro i' z; apply hM; rw [z]; exact hy
 have hz := sail_g S ((l+70)*radiusB x) i (temp x) a U M.V M.key hV p hx.1.le (funds_branch ht.funds.1) hh (by unfold a; positivity) (by omega) (by simp_rw [Nat.add_mul]; omega) M.k
 dsimp only at hz; rw [ht.got,ht.funds.1.knobs] at hz
 have hr: w*temp x ≤ (w*2)*t:= (mul_le_mul_of_nonneg_left hx.2.2 hw).trans (mul_assoc ..).symm.le; apply hz.trans; unfold L; apply le_trans _ (mul_le_mul_of_nonneg_right (le_max_right ..) ht'.le); change w*temp x + b*_≤_; apply le_trans (add_le_add hr (mul_le_mul (le_abs_self b) (mul_le_mul_of_nonneg_left (add_le_add (le_refl a) hr) (by norm_num)) (show 0 ≤ 4*(a+w*temp x) from by have hv:=hx.1; unfold a; positivity) (abs_nonneg _))); unfold a; apply Eq.le; ring
end YM.CF.Cloak
