import YM.CF.Cloak.Wave
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
open Rill
local notation "m₀"=> SU.group.colorScale
lemma windUp{d b:ℝ}{p:SU.E→SU.E→SU.E}(h: Wind d p n C)(hv:C ≤ b):Wind d p n b:=⟨h.pos.trans hv,fun a y z=> (h.duty a y z).bag (mul_le_mul_of_nonneg_right hv y.price)⟩
lemma coze(n l:ℕ)(Q:Patch)(g A B:ℝ)(p:0<g)(hA:0<A)(hB:0<B) :∃ a:ℝ,0<a∧∀ᶠ x in atTop,∀ β∈Set.Icc (y G Q.L x/2) (2*y G Q.L x),∀ L:ℝ,0<L→ L≤ B*Scales.p G Q.L x→ 0<β∧coupling β*L/a ≤1 ∧∀ {c f:Side}(S:StepData c f)(T:Tube G S), S.patch=Q→∀ (M: Monk G S) u s d, ‖M.z‖ ≤ L→MossX n l x M.key M.park T M.V M.k A d (fiery G x Q.L) s → |u|≤1 → Trow (repine T x M d l s a L) (0,u) g n ∧ Trow (Vmove x M.V) 0 g n ∧ (∀ i, Allows n (fun p=> tape (bent T x M d l s a L p) i) (0,u) g) :=by -- remove extraneous
 let r:=firstRadius G; obtain ⟨e,K,p',hK,H,-⟩:=sailors n Chi.canonical (div_pos (first_pos G) (by norm_num : (0:ℝ)<3)) (show 2*(r/3)< r by have ht:=first_pos G; unfold r; linarith); obtain ⟨C,hC,h⟩:=funding n; obtain ⟨A₀,v,h₁,hv,P⟩:= moveC n
 let D:= max K C; have he:1≤D:=hK.trans (le_max_left ..); have hD:0<D:=zero_lt_one.trans_le he; let R:=min (min 1 (e/D)) (g/D^2); have ht:0<R:=lt_min (lt_min zero_lt_one (div_pos p' hD)) (by positivity)
 let z:=2^n*(2^n*A); let l':=Push.Uniform.shade G; have hl':0<l':= Push.Uniform.shade_pos _; have hz:0<z:=by unfold z; positivity
 let a:=R/(2*l'*z); have ha:0<a:=by unfold a; positivity
 have hu:A₀>0:=zero_lt_one.trans_le h₁
 refine ⟨a,ha,?_⟩; filter_upwards [expM Q (hp:=lt_min (div_pos ht (mul_pos (mul_pos (by norm_num : (0:ℝ)<2) hl') hA)) (div_pos ha (mul_pos (by norm_num:(0:ℝ)<2) hB))),Work.E05.ultimately_cool (min v (D*R/A₀)) (lt_min hv (div_pos (mul_pos hD ht) hu)),(year G Q.L).eventually (eventually_gt_atTop 0),eventually_gt_atTop (0:ℝ)] with x hx hp hg hO β h₀ L hL hL'
 let t:=fiery G x Q.L
 have hP:0<β:= (half_pos hg).trans_le h₀.1
 have hj:coupling β*L ≤ a:=by
    have hh:=mul_le_mul ((compare_v G Q.L x h₀ hg).1) hL' hL.le (show 0≤2*Scales.g G Q.L x from by have hp:=Scales.gauge G Q.L hg; positivity); have ht:= (le_div_iff₀ (show (0:ℝ)<2*B by positivity)).mp (hx.trans (min_le_right ..)); refine hh.trans ?_; rw [Scales.fi] at ht; apply le_trans (le_of_eq ?_) ht; ring
 refine ⟨hP,(div_le_one ha).mpr hj,@fun c f S T hs M u s d hx' Ht hμ=>?_⟩
 let a':=A*t+2^n*(a*(2^n*A)); have hx:= boa Ht hx' hL ha.le hμ hA.le
 have hp' : Trow (Vmove x M.V) 0 (D*R) n:= fun i=> ((P M.V x (Work.E09.temp_pos hO) (hp.2.trans (min_le_left ..))) i).bag ((mul_comm ..).le.trans ((le_div_iff₀ hu).mp (hp.2.trans (min_le_right ..))))
 have hN:D*(D*R) ≤ g:=by have hq:= (le_div_iff₀ (pow_pos hD 2)).mp (min_le_right (min 1 (e/D)) (g/D^2)); apply le_trans (Eq.le ?_) hq; change _=R*D^2; ring
 have hb:D*R ≤ g:=(le_mul_of_one_le_left (mul_nonneg hD.le ht.le) he).trans hN
 have hℓ:l'*a' ≤ R:=by
    rw [show a'=A*t+a*z from ?_]; swap; · unfold a' z; ring
    have hQ:t ≤ R/(2*l'*A):= by exact LE.le.trans ‹fiery _ _ _≤ min _ _› (min_le_left ..)
    apply le_trans (mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_left hQ hA.le) (le_refl (a*z))) hl'.le); apply le_of_eq; unfold a; field_simp; ring
 have he' :D*R ≤ e:=(mul_comm ..).le.trans ((le_div_iff₀ hD).mp ((min_le_left ..).trans (min_le_right ..)))
 have ht' : R ≤ 1:=(min_le_left ..).trans (min_le_left ..)
 have hp :=pulse_b (M:=M) n e R D ht.le he (windUp H (le_max_left ..)) he' ht' (@fun E _ _ f u hf=>(h _ u _ hf ht').bag (mul_le_mul_of_nonneg_right (le_max_right ..) ht.le)) hp' hx hℓ
 exact ⟨fun i=> (hp i).bag hN, fun i=> (hp' i).bag hb,fun i=> (shelJ hx i).mono (hℓ.trans ((le_mul_of_one_le_left ht.le he).trans hb))⟩
end YM.CF.Cloak
