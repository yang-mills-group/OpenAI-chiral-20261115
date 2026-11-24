import YM.CF.Cloak.Wall
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
lemma moveC(n:ℕ):∃ C v:ℝ,1 ≤ C∧0<v ∧∀{c:Side}(V:Config G c),∀x:ℝ,0<temp x → temp x≤v → Trow (Vmove x V) 0 (C*temp x) n:=by
 -- directly
 let a:= firstRadius G; obtain ⟨e,K,p,hK,H,-⟩:= sailors n Chi.canonical (div_pos (first_pos G) (by norm_num:(0:ℝ)<3)) (show 2*(firstRadius G/3)<firstRadius G from by have ht:=first_pos G; linarith); obtain ⟨C,hc,h⟩:=funding n; let v:=C*K; refine ⟨v,min 1 (e/C),one_le_mul_of_one_le_of_one_le hc hK,lt_min zero_lt_one (div_pos p (zero_lt_one.trans_le hc)),fun V x g l i=>?_⟩
 let t:=temp x; let Y(z:Directions G _):= temp x • z i; let L:=ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _ : Bond _=>SU.group.Color) i; have hL:‖L‖≤ 1:= ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v=>by rw [one_mul]; exact norm_le_pi_norm v i
 have he: Allows n Y 0 t:= ((allows_linear hL (x:=0) (by simp)).smul t).mono (by rw [abs_of_nonneg g.le,mul_one])
 have hz:= h Y 0 t he (l.trans (min_le_left ..)); change Tender _ _ (v*temp x) _; rw [show v*temp x= K*(C*t) from by unfold v t; ring]; exact H.duty ((mul_comm C t).le.trans ((le_div_iff₀ (zero_lt_one.trans_le hc)).mp (l.trans (min_le_right ..)))) hz ((Shake.holds (SU.group.mat (V i))).bag hz.price)
lemma vistZ(n:ℕ)(v σ:ℝ)(hp:1 ≤ v)(hv:m₀ ≤ v)(hσ:0<σ)(q:Chi): ∃ C:ℝ,1 ≤ C∧∀ {f:Side}{E:Type}[NormedAddCommGroup E][NormedSpace ℝ E](u:ℝ)(U:E→ Config G f)(X:E)(F:Finset (Cell f)), 0<u → u ≤ 1 → HeldT U F X→ Trow U X (v*u) n→(∀ i,Tender (fun y=>faceValue (U y) i) X (v*u) n) → Vista U X u 1 σ F n q C 0:=by
 choose M h H using fun i:Fin 5=>crown_h v σ hp n (i:ℕ) hσ hv q; let C:=1+∑ i,M i; refine ⟨C,le_add_of_nonneg_right (sum_nonneg (fun i _=> h i)),@fun f E _ _ u U X F p ht hv g k=>?_⟩
 constructor; intro n hn A i; let j:Fin 5:= ⟨n,by omega⟩; have hL:M j ≤ C:= (single_le_sum (f:=M) (fun i _=>h i) (mem_univ j)).trans (le_add_of_nonneg_left zero_le_one); obtain ⟨hz,h,u'⟩:= H j U X u F p ht g k hv A i; have hp:0 ≤ A.budget σ:=by unfold RG.Atom.budget RG.Atom.magnitude; positivity
 have hP:M j*u^n*A.budget σ ≤ C*u^n*A.budget σ:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hL (by positivity)) hp
 exact ⟨hz.mono hP, fun i=>(h i).mono hP,fun p=> (u' p).mono (mul_le_mul_of_nonneg_right hL hp)⟩
def Inherits (n:ℕ)(q:Chi)(P:Patch)(σ σ' a b K K' t Y:ℝ)(p:Monk G S)(T:Tube G S)(l:ℕ)(β x d:ℝ):Prop:=∀{E:Type}[NormedAddCommGroup E][NormedSpace ℝ E](i:E→L[ℝ] Directions G c),(∀ y, axl p.key.flags (temp x•i y)=temp x•i y)→ ‖i‖ ≤ 1 →∀ s:Signed,
 (let X:=traceZ (turnStore s p.key).flags;let V:= pull s 0 ∘ Vmove x p.V ∘ i; Vista V (0:E) (temp x) 1 σ' X n q K' 0∧∀ z∉ X,Pressure.toll (V 0) z ≤ temp x)∧let U(y):=(p.atop (i y) x).sent x T q d l β; Vista (pull s 0 ∘ U) (0:E) t 1 σ (turnStore s p.key).costs n q K 0
lemma bloomP (n l:ℕ)(q:Chi)(P:Patch)(σ σ' a b:ℝ)(ha:0<a)(hb:0<b)(hσ:0<σ)(hσ':0<σ'): ∃ K K':ℝ,1 ≤ K ∧1 ≤ K' ∧∀ᶠ x in atTop,∀ {c f:Side}(S:StepData c f)(T:Tube G S),S.patch=P→∀ (M:Monk G S),M.key.flags= RG.flags (temp x) M.V → let t:=fiery G x P.L; let Y:=b*Scales.p G P.L x;‖M.z‖ ≤ Y →∀ d β:ℝ,MossX n l x M.key M.park T M.V M.k a d t q → β∈Set.Icc (y G P.L x/2) (2*y G P.L x)→ Inherits n q P σ σ' a b K K' t Y M T l β x d:=by
 obtain ⟨C,hC,H⟩:= hullD n l P q a b ha hb; obtain ⟨D,v,hD,hv,H'⟩:= moveC n; obtain ⟨A,e,hA,hs,hP,T⟩:= pong n C hC; obtain ⟨B,v',hB,hs',hV,T'⟩:= pong n D hD; obtain ⟨K,hK,J⟩:=vistZ n A σ hA hs hσ q; obtain ⟨K',hK',J'⟩:=vistZ n B σ' hB hs' hσ' q
 refine ⟨K,K',hK,hK',?_⟩; filter_upwards [H, expM P (hp:=lt_min hP zero_lt_one), Work.E05.ultimately_cool (min v (min v' 1)) (lt_min hv (lt_min hV zero_lt_one)), monitors G P.L, (year G P.L).eventually (eventually_gt_atTop (0:ℝ))] with x Ht hz hy hx hZ c f S T₂ p M h t Y hu d β hU hg E _ _ i he hp s; have g:=hx.1; have hg':0<t:=by unfold t; rw [Scales.fi]; exact mul_pos (Scales.gauge G P.L hZ) (Scales.pos ..)
 let W:=Vmove x M.V; let Q(z):= (M.atop z x).sent x T₂ q d l β; have hf(j:Bond f): Tender (fun u=> Q (i u) j) (0:E) (C*t) n:= by
    have ht:= Ht S T₂ M p d (by rw [p]; exact hU) (by rw [p]; exact hu) β (by rw [p]; exact hg)
    exact (Shake.dil
      i _ (ht.2 j) hp (le_refl _)).bag (by rw [one_pow,mul_one]); -- tune
 have ht':=T (Q ∘ i) 0 t hg'.le (hz.trans (min_le_left ..)) hf s; let t':=temp x; let A:=Vmove x M.V∘ i; have ht'' (j:Bond c):Tender (fun y=> A y j) 0 (D*t') n:= (Shake.dil i _ ((H' _ _ g (hy.2.trans (min_le_left ..))) j) hp le_rfl).bag (by rw [one_pow,mul_one]) -- tune
 have hp':=hy.2.trans (min_le_right ..); have hP':= T' A 0 (temp x) g.le (hp'.trans (min_le_left ..)) ht'' s;
 refine ⟨⟨J' _ _ _ _ g (hp'.trans (min_le_right ..)) (face_h (curtainP (x':=(0:E)) he) s) hP'.1 hP'.2,?_ ⟩,J _ _ _ _ hg' (hz.trans (min_le_right ..)) ?_ ht'.1 ht'.2⟩ -- orientation
 · intro i v; suffices hs:Vmove x M.V (‹E→L[ℝ] Directions G c› 0)=M.V by
     dsimp only [comp_apply]; rw [hs]; by_contra! k; have he:= (RG.flags_spec ..).2 ⟨i,Work.E01.base_touched _,k⟩; exact v (mem_filter.mpr ⟨mem_univ _,(flag_turn ..).2 (h.symm ▸ (exact_turn ..).1 he)⟩)
   simp [Vmove]
 -- U.Held
 exact tide_d (F:=M.park) (fE:=fun y:E=> (M.atop (i y) x).fuel x T₂ q d l β) (Y:=M.bush x) (V':=A) s
end YM.CF.Cloak
