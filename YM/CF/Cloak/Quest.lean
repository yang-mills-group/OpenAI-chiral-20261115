import YM.CF.Cloak.Probe
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
open Atala
local notation "Cᵢ"=> max 1 SU.group.colorScale
structure Gest (q:Chi) (n l:ℕ) (w s a L M K:ℝ) (F N P:ℝ→ℝ) :Prop where
 fit : Lento F∧Lento N∧Lento P
-- reserve for signed.V tags.Mask.
lemma gradeN (T:Teller G)(n l:ℕ)(q: Chi)(J:Patch)(D A B a b m w:ℝ)(p:0<A)(h:0<B)(hp:0<a)(hm:0 ≤ m) : ∃ F N P:ℝ→ℝ, Gest q n l w a b D B Cᵢ F N P ∧∀ᶠ x in atTop,∀{c f:Side}(S: StepData c f)(T':Tube G S), Cert J T S T' x→Volo S n a b Cᵢ m→∀(M: Monk G S), ‖M.z‖≤ B*Scales.p G J.L x → let t:=fiery G x S.patch.L; let d:=D*t;∀ β∈Set.Icc (y G J.L x/2) (2*y G J.L x), MossX n l x M.key M.park T' M.V M.k A d t q →
 let Q(v):=M.atop v x; let Y(v):= (Q v).sent x T' q d l β
 (∀ i:Cell f,Probe (fun u:Directions G c=>tokenF M.key q x (Y u) i) 0 (F x) n)∧ (∀ i:Bond c,Probe (fun u: Directions G c => tidal M.key x w a q (Y u) (Vmove x M.V u) M.k i) 0 (N x) n) ∧ ∀ i:Active M.key x M.park,Probe (fun v:Directions G c=> broad q d ((Q v).rich x T' q d l β (show Active (Q v).key x (Q v).park from i))) 0 (P x) n:=by
 obtain ⟨L,hL,H⟩:= hullD n l J q A B p h; obtain ⟨u,hu,hz⟩:=currencyT q n; let v:=Cᵢ; let TT (x):=fiery G x J.L; let F(x:ℝ):=dam G n (TT x /4) u v; let P':=Push.Uniform.shade G; have hs:0<P':= Push.Uniform.shade_pos G; let d:= A+2^n*A*(2*B); let r:=P'*d; have hd:0<d:=by unfold d; positivity
 let N(x:ℝ):=trout J x w a v u m n; let P (x):= Jet.composeCost n u ((2/(D*TT x)^2)*(2^n*r*r)); have hL':0<L:= zero_lt_one.trans_le hL
 refine ⟨F,N,P,⟨?_⟩,?_ ⟩
 · have hr:Lento fun x=>(TT x/4)⁻¹:=by refine Lento.mono (Lento.ledge J.L (1/4)) ?_; filter_upwards with x; unfold TT; ring_nf; rfl
   exact ⟨Lento.piece ((Lento.sco hr).times (Lento.sun _)) _ _,Lento.piece ((Lento.sco (Lento.ledge J.L w)).times (Lento.sun _)) _ _,Lento.piece ((Lento.sco (Lento.ledge J.L D)).times (Lento.sun _)) _ _⟩
 let U:=hL -- tune
 filter_upwards [H,expM J (hp:=lt_min (one_div_pos.mpr hL') zero_lt_one), Work.E01.radiusB_tendsto.eventually_ge_atTop (shovel J+10),(year G J.L).eventually (eventually_gt_atTop 0)] with x hv ht hr hx c f S H₁ p' hk M hq t y β hμ hJ Q Y
 have he:t=TT x:=by unfold TT t; rw [p'.got]
 have ha:=hv S H₁ M p'.got y hJ (by rw [p'.got]; exact hq) _ (by rw [p'.got]; exact hμ)
 have hh(I: Bond _):grantB n (fun w=> Y w I) 0 v:=((ha.2 I).paid (d:=SU.group.colorScale) (le_of_eq (show ‖SU.group.mat _‖=_ from Gauge.unitary_frob (SU.group.mat_mul_star _)))).mono (max_le_max (by rw [mul_comm]; exact (le_div_iff₀ hL').mp (ht.trans (min_le_left ..))) le_rfl)
 have hU: FuelG _ (Vmove x M.V) 0 n v:=fun i=> ((ha.1 i).paid (d:=SU.group.colorScale) (le_of_eq (Gauge.unitary_frob (SU.group.mat_mul_star _)))).mono (max_le_max (by rw [mul_comm]; exact (le_div_iff₀ hL').mp (ht.trans (min_le_left ..))) le_rfl)
 have hf: Dane G n q u:=by intro E _ _ f x C d i h; exact hz d i h
 have hF:Frolic M.key x Y 0:= pileD (F:=M.park) (V':=Vmove x M.V) (fE:=fun i=> (Q i).fuel x H₁ q y l β) (Y:=M.bush x) (by rw [p'.got]; exact hr)
 refine ⟨fun i=>?_,fun i=>?_,fun i=>?_⟩
 · have hp:=probF (A:=M.key) (x:=x) hh hf i; convert hp using 1; unfold F TT; rw [p'.got]
 · have hp:= probI (w:=w) (k:=M.k) i hh hU hf hF (funds_branch p'.funds.1) hk ‹0<a› hu hm (le_max_left ..); convert hp using 1; unfold N; rw [p'.got]
 let Z:=B*Scales.p G J.L x; have hP:= Scales.pos G J.L x; have he' := (shelJ (ready_heat (β:=β) (M.bush x) (M.bell x) _ hJ Z ((pi_norm_le_iff_of_nonneg (mul_pos h hP).le).mpr (fun i=> (norm_le_pi_norm M.z i.val.val).trans hq)) p.le).2 i); -- tune
 let W(u):= (Q u).rich x H₁ q y l β (show Active _ _ _ from i); have hg: Allows n W 0 r := he'.mono (mul_le_mul_of_nonneg_left ?_ hs.le); · have hp:= probR y hg hf; convert hp using 1; unfold P y; rw [he] -- tune y
 have hp:0<β:=(half_pos hx).trans_le hμ.1; rw [he,abs_of_pos (coupling_pos hp)]
 apply le_trans (add_le_add le_rfl (mul_le_mul_of_nonneg_right (compare_v G J.L x hμ hx).1 (by change 0≤2^n*A*Z; positivity)))
 apply le_trans (b:=d*TT x) ?_ (mul_le_of_le_one_right hd.le (ht.trans (min_le_right ..)))
 unfold TT Z d; rw [Scales.fi]; apply Eq.le; ring
end YM.CF.Cloak
