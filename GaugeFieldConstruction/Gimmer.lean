import YM.CF.Prism.Pang
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
-- exact nonflat variation compared to 1 in SAME coarse gauge
variable {X:Hub f}{Z:Support (More c)}{U:Pane c→Pane f}{a b c':ℝ}
local notation "Y"=>X.val.2
local notation "Ω"=>S.ratio.parent X.val.1
section hue
variable (hp: 2 ≤ n)(hK: 1 ≤ K)(hC:1 ≤ C)(hQ: TariffZ n K) 
variable {F':InkD f}
variable (W:tangD c→ tangD f) (Θ:tangD c→Seat f→SU.group.Color)(g:Seat c→SU.E)(β:PressB P X F' a b) (L: Guide _ (B.dirBound (S.ratio.parent X.val.1)) 0 Θ n ε)(hg:∀ᶠ w in 𝓝 (0:tangD c),Agrees (inspected X.val.2) (increment 1 (W w)) (Lattice.gauge (fun i=> SU.group.lieExp (Θ w i)) (Lattice.gauge (g ∘ S.ratio.parent) (U (increment V w)))))
local notation "L_"=>fun v=> Lattice.gauge (g ∘ S.ratio.parent) (U (increment V v))
variable (x y:Rock f)(h:ℝ)(hh:0 ≤ ε)(hgε:ε ≤ 1)(k:B.order=n)
include hp hK hQ L hg β hh hgε k
abbrev sparkleC(n:ℕ)(K:ℝ):= let M:=pepper n; ((Fintype.card SU.Slot:ℝ))*((Fintype.card SU.Slot:ℝ)*(M^2*K*(K+2)))
lemma goss(hx:∀ i j:SU.Slot,Signs B Ω (fun w=>crib F' x y i j (increment 1 (W w))) h)(i j:SU.Slot): Signs B Ω (fun w=> crib F' x y i j ((L_) w)-crib F' x y i j (increment 1 (W w))) (sparkleC n K*h*ε):=by
 let a(b:Bool)(z:Rock f)(i j:SU.Slot)(w):=aull b i j (-Θ w (Cube.node z.1)); let c(b:Bool)(i j:SU.Slot):= aull b i j 0; let E:=crib F' x y; let u:= fun i j w=> E i j (increment 1 (W w));
 have heq:(fun w=> crib F' x y i j ((L_) w)-E i j (increment 1 (W w)))=ᶠ[𝓝 0] (fun w=>∑ l:SU.Slot,∑ k:SU.Slot,(a true x i k w*u k l w*a false y j l w - c true i k*E k l (increment 1 (W w))*c false j l)):=by
    filter_upwards [hg] with w hw; simp_rw [sum_sub_distrib]; congr 1 -- tune subtract
    · unfold crib; let g'(i:Seat f):= SU.group.lieExp (-Θ w i)
      let G': Pane f:=(L_) w; have hv(i:Seat f): (fun i=> SU.group.lieExp (Θ w i)) i *g' i=1:=by unfold g'; have h:=Cascade.roll_inv (Θ w i) 1; rw [inv_eq_iff_mul_eq_one] at h; simpa [Cascade.rollH] using h -- tune
      have hh:Agrees Y G' (Lattice.gauge g' (increment 1 (W w))):=by
           intro i he hp
           unfold Lattice.gauge; rw [hw i (mem_union_left _ he) (mem_union_left _ hp)]; unfold Lattice.gauge; -- tune group
           simp_rw [← inv_eq_of_mul_eq_one_right (hv i.1),← inv_eq_of_mul_eq_one_right (hv (i.1+step i.2))]; change Lattice.gauge (g ∘ S.ratio.parent) (U (increment V w)) i=_; unfold Lattice.gauge; group <;> simp
      rw [β.term _ _ hh,forge β,Matrix.mul_apply]; simp_rw [Matrix.mul_apply,Finset.sum_mul]; rfl
    have hh(b:Bool): Matrix.of (fun i j=> c b i j)=(1:Op SU.Slot):=by ext i j; cases b<;>simp [c,aull,gemT,- SU.matter_matrix,cc] -- tune namespace
    have ht (b) : ∀ i j:SU.Slot,c b i j=(1:Op _) i j:=Matrix.ext_iff.mpr (hh b); simp_rw [ht]; simp [ite_mul, mul_ite, Matrix.one_apply]


 have hk'(b:Bool)(z:Rock f)(i j:SU.Slot): Signs B Ω (fun w=> a b z i j w - c b i j) (K*ε):= hQ _ _ Θ B Ω ε k L hgε _ _ _ _
 have he'(b:Bool)(z:Rock f)(i j:SU.Slot): Signs B Ω (a b z i j) (K+1):=high (bonus _ B Ω _ (c b i j) (hk' b z i j) (hus ..)) (add_le_add_left (mul_le_of_le_one_right (zero_le_one.trans hK) hgε) _)
 let f(k l:SU.Slot)(w):=a true x i k w*u k l w*a false y j l w - c true i k*u k l w*c false j l
 let H:=(pepper n)^2*K*(K+2)*h*ε
 have ht (l k':SU.Slot):Signs B Ω (f k' l) H:=by
    refine mint (high (tack (patch (patch (he' true x i k') (hx k' l)) (hk' false y j l)) (patch (patch (hk' true x i k') (hx k' l)) (Prism.hail (hus false j l)))) ?_) ?_
    · unfold H; rw [k]; exact le_of_eq (by ring)
    apply Eventually.of_forall; intro w; let x':= a true x i k'; let y':= a false y j l; let F:= u k' l; change x' w*F w*(y' w-c false j l)+(x' w-c true i k')* F w*c false j l=x' w * F w * y' w - c true i k' * F w*c false j l; ring
 refine mint ?_ heq.symm
 apply high (haloI (fun l _=> haloI (fun k' _=>ht l k'))); unfold sparkleC H; simp; exact le_of_eq (by ring) -- tune
end hue
end YM.CF.Prism
end
