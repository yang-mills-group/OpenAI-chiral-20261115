import YM.CF.Prism.Hoy
import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Folio.Wind
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.CF.Prism
open Siete
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG PhysicalNext.JointLoad Heir Next.Foundations AnalyticBridge.SectorAffine AnalyticBridge.SectorAffine.Offset Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
variable {n l:ℕ}{K C Q R v ε d r η t x:ℝ}{c f: Side}
local notation "G"=> SU.group
open Cube (More)
open Tree
variable {S: StepData (More c) (More f)}{F:Forest S.ratio}{T:Tube G S}{V:Pane c}
variable {B P:BudgetPoint}{o:Seat c}
lemma cent(k:ℕ)(p:1 ≤ k):∃ C:ℝ,1 ≤ C ∧∀ {c f:Side}(Θ:tangD c→Seat f→ SU.group.Color)(B:BudgetPoint)(o:Seat c)(ε:ℝ),B.order=k → Guide _ (B.dirBound o) 0 Θ k ε → ε ≤ 1 →∀ (a:Seat f)(b:Bool)(i j:SU.Slot),Signs B o (fun w=> aull b i j (-Θ w a)-aull b i j 0) (C*ε):=by
 let O:=Bool× SU.Slot×SU.Slot; choose k' hk hK using fun i:O=> stopF i.1 i.2.1 i.2.2 k p
 let H:=1+∑ i:O,k' i; have hx:1 ≤ H:=le_add_of_nonneg_right (sum_nonneg fun i _=>zero_le_one.trans (hk i)); refine ⟨H,hx,@fun c f X B o ε h hz p a b i l=>?_⟩; have hp:k' (b,i,l) ≤ H:=le_trans (single_le_sum (f:=k') (fun i _=>zero_le_one.trans (hk i)) (mem_univ _)) (le_add_of_nonneg_left zero_le_one); exact high (hK (b,i,l) a X B o ε h hz p) (mul_le_mul_of_nonneg_right hp ((norm_nonneg _).trans hz.size))
lemma bonus (Θ:tangD c→ℂ)(B:BudgetPoint)(o:Seat c)(A:ℝ)(X:ℂ)(h:Signs B o (fun w=>Θ w-X) A)(k:‖X‖ ≤ ε): Signs B o Θ (A+ε):=mint (tack h (Prism.hail k)) (Eventually.of_forall fun i=>sub_add_cancel (Θ i) X)
def carrot(n:ℕ)(K C:ℝ):ℝ:=let M:=pepper n; M*(M*(K+1)*C)*(K+1)+M*(M*(K+1))*K+ M*(M*K) -- choose Δ(E(V)) path using expU−, trans Ecost X ; expression decay shape
-- exact nonflat variation compared to 1 in SAME coarse gauge
variable {X:Hub f}{Z:Support (More c)}{U:Pane c→Pane f}{a b c':ℝ}
local notation "Y"=>X.val.2
local notation "Ω"=>S.ratio.parent X.val.1
abbrev TariffZ (N:ℕ)(C:ℝ):Prop:=∀ (c f:Side)(Θ:tangD c→Seat f→ SU.group.Color)(B:BudgetPoint)(o:Seat c)(ε:ℝ),B.order=N → Guide _ (B.dirBound o) 0 Θ N ε → ε ≤ 1 →∀ (a:Seat f)(b:Bool)(i j:SU.Slot),Signs B o (fun w=> aull b i j (-Θ w a)-aull b i j 0) (C*ε)
section hue
variable (hp: 2 ≤ n)(hK: 1 ≤ K)(hC:1 ≤ C)(hQ: TariffZ n K) 
variable {F':InkD f}
variable (W:tangD c→ tangD f) (Θ:tangD c→Seat f→SU.group.Color)(g:Seat c→SU.E)(β:PressB P X F' a b) (L: Guide _ (B.dirBound (S.ratio.parent X.val.1)) 0 Θ n ε)(hg:∀ᶠ w in 𝓝 (0:tangD c),Agrees (inspected X.val.2) (increment 1 (W w)) (Lattice.gauge (fun i=> SU.group.lieExp (Θ w i)) (Lattice.gauge (g ∘ S.ratio.parent) (U (increment V w)))))
local notation "L_"=>fun v=> Lattice.gauge (g ∘ S.ratio.parent) (U (increment V v))
variable (x y:Rock f)(h:ℝ)(he:ε ≤ r^2)(hr:0 ≤ r)(h1:r≤1)(k:B.order=n)
include hK hC hQ L hg β he hr h1 k
lemma wept (hx:∀ i j:SU.Slot, Signs B (S.ratio.parent X.val.1) (fun v=> crib F' x y i j (increment 1 (W v))-crib F' x y i j 1) (C*r^2*h))(hk:∀ i j, ‖crib F' x y i j 1‖ ≤ h)(i j:SU.Slot): Signs B (S.ratio.parent X.val.1) (fun w=>crib F' x y i j (Lattice.gauge (g ∘ S.ratio.parent) (U (increment V w)))-crib F' x y i j 1) ((Fintype.card SU.Slot:ℝ)*((Fintype.card SU.Slot:ℝ)*(carrot n K C*r^2*h))):=by
 let a(b:Bool)(z:Rock f)(i j:SU.Slot)(w):=aull b i j (-Θ w (Cube.node z.1)); let c(b:Bool)(i j:SU.Slot):= aull b i j 0; let E:=crib F' x y; let u:= fun i j w=> E i j (increment 1 (W w))
 have hy : r^2 ≤ 1:=pow_le_one₀ hr h1
 have heq:(fun w=> crib F' x y i j ((L_) w)-crib F' x y i j 1)=ᶠ[𝓝 0] (fun w=>∑ l:SU.Slot,∑ k:SU.Slot,(a true x i k w*u k l w*a false y j l w - c true i k*E k l 1*c false j l)):=by
    filter_upwards [hg] with w hw; simp_rw [sum_sub_distrib]; congr 1 -- tune subtract
    · unfold crib; let g'(i:Seat f):= SU.group.lieExp (-Θ w i)
      let G': Pane f:=(L_) w; have hv(i:Seat f): (fun i=> SU.group.lieExp (Θ w i)) i *g' i=1:=by unfold g'; have h:=Cascade.roll_inv (Θ w i) 1; rw [inv_eq_iff_mul_eq_one] at h; simpa [Cascade.rollH] using h -- tune
      have hh:Agrees Y G' (Lattice.gauge g' (increment 1 (W w))):=by
           intro i he hp
           unfold Lattice.gauge; rw [hw i (mem_union_left _ he) (mem_union_left _ hp)]; unfold Lattice.gauge; -- tune group
           simp_rw [← inv_eq_of_mul_eq_one_right (hv i.1),← inv_eq_of_mul_eq_one_right (hv (i.1+step i.2))]; change Lattice.gauge (g ∘ S.ratio.parent) (U (increment V w)) i=_; unfold Lattice.gauge; group <;> simp
      rw [β.term _ _ hh,forge β,Matrix.mul_apply]; simp_rw [Matrix.mul_apply,Finset.sum_mul]; rfl
    have hh(b:Bool): Matrix.of (fun i j=> c b i j)=(1:Op SU.Slot):=by ext i j; cases b<;>simp [c,aull,gemT,- SU.matter_matrix,cc] -- tune namespace
    have ht (b) : ∀ i j:SU.Slot,c b i j=(1:Op _) i j:=Matrix.ext_iff.mpr (hh b); simp_rw [ht]; simp [ite_mul, mul_ite, Matrix.one_apply,E]

 let H:=carrot n K C*r^2*h; have hk'(b:Bool)(z:Rock f)(i j:SU.Slot): Signs B Ω (fun w=> a b z i j w - c b i j) (K*r^2):= high (hQ _ _ Θ B Ω ε k L (he.trans hy) _ _ _ _) (mul_le_mul_of_nonneg_left he (zero_le_one.trans hK))
 have he'(b:Bool)(z:Rock f)(i j:SU.Slot): Signs B Ω (a b z i j) (K+1):=high (bonus _ B Ω _ (c b i j) (hk' b z i j) (hus ..)) (add_le_add_left (mul_le_of_le_one_right (zero_le_one.trans hK) hy) _)
 let f(k l:SU.Slot)(w):=a true x i k w*u k l w*a false y j l w - c true i k*E k l 1*c false j l
 have ht (l k':SU.Slot):Signs B Ω (f k' l) H:=by
    have hE:=Prism.hail (B:=B) (o:=Ω) (hk k' l)
    refine mint (high (tack (tack (patch (patch (he' true x i k') (hx k' l)) (he' false y j l)) (patch (patch (he' true x i k') hE) (hk' false y j l))) (patch (patch (hk' true x i k') hE) (Prism.hail (hus false j l)))) ?_) ?_
    · unfold H carrot; rw [k]; dsimp only; exact le_of_eq (by ring)
    apply Eventually.of_forall; intro w; change _+_= f k' l w; unfold f c a E u at *; ring -- tune
 refine mint ?_ heq.symm
 apply high (haloI (fun l _=> haloI (fun k' _=>ht l k'))); simp [H] -- tune metavars
end hue
end YM.CF.Prism
