import YM.CF.Cloak.Kern
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
section bound
variable {E X:Type}[NormedAddCommGroup E][NormedSpace ℝ E]{x₀:E}{U:E→ Config G f}{u v C D:ℝ}{T:E→X}[NormedAddCommGroup X][NormedSpace ℝ X]
local notation "m"=> SU.group.colorScale
open scoped Classical
variable {X₂:Support f}{U₀:Config G f}{A:Finset (Cell f)}{F:Forest S.ratio}{s:ℝ}
open Atala
section
variable {a k:ℕ}{D':ℝ}
variable (S':RG.Atom G a)(i:Site f)(hp:0 ≤ D)(h:∀ x:Fin a, Allows n (fun y=> (S'.leg x).atSite (U y) i) x₀ (D*Real.exp (C*(S'.leg x).length)))
include h
lemma potsY (P:Fin a→ SU.group.ColorIndex)(X': Finset (Fin a)):Allows n (fun y=>∏ j∈X', ((S'.leg j).atSite (U y) i) (P j)) x₀ ((zest n*D)^X'.card*Real.exp (C* (∑ j∈X',(S'.leg j).length:ℕ))) :=by
 induction X' using Finset.induction_on with
 | empty=> simp only [Finset.prod_empty,card_empty,pow_zero,sum_empty,Nat.cast_zero,mul_zero,Real.exp_zero,mul_one]; exact allows_const _ (by simp)
 | insert t V hv ih=>
    let VVV(x):=(S'.leg t).atSite (U x) i; let B:=EuclideanSpace.proj (𝕜:=ℝ) (P t); have hp:‖B‖ ≤ 1:= ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun i=> (PiLp.norm_apply_le i (P t)).trans_eq (one_mul _).symm
    have ht:Allows n (fun x=> (VVV x) (P t)) x₀ _:= (h t).linear B hp
    simp_rw [prod_insert hv,card_insert_of_notMem hv,sum_insert hv]; refine (allot ht ih).mono ?_; apply Eq.le; rw [pow_succ']; push_cast; rw [mul_add,Real.exp_add]; ring
lemma cupXT : Allows n (fun y=> S'.unmasked (U y) i) x₀ ((zest n * D)^a * (S'.budget C)) :=by
 have hp(r):= potsY S' i h r univ; unfold RG.Atom.unmasked RG.Atom.poly; refine Allows.mono (allows_sum (s:=univ) fun j p=> (hp j).smul (S'.coeff j)) ?_ -- tune hp(r) unused estimator 
 simp only [card_univ,Fintype.card_fin, ←sum_mul,RG.Atom.budget,RG.Atom.magnitude,RG.Atom.length]; exact le_of_eq (by ring)
omit h
lemma mature(a n:ℕ)(F:ℝ)(h:m ≤ F)(σ:ℝ)(hs:0<σ): ∃ C:ℝ,0 ≤ C ∧∀ {f:Side}{E:Type}[NormedAddCommGroup E][NormedSpace ℝ E](t:ℝ)(A:RG.Atom G a)(i:Site f)(U:E→ Config G f)(x:E), 0<t → t≤1→ Trow U x (F*t) n→(∀ j:Cell f,Tender (fun y=>faceValue (U y) j) x (F*t) n) →Healthy t (A.footprint i) (U x) → Allows n (fun y=> A.unmasked (U y) i) x (C* t^a * A.budget σ):=by -- tune cannot autoParam p
 obtain ⟨D,hD,H⟩:=ink n F σ hs h
 have ht:=zpos n; refine ⟨(zest n*D)^a,by positivity,@fun f E _ _ t A i U x v k u hk hp=>?_⟩
 have ha : (zest n*D)^a*t^a=(zest n*(D*t))^a :=by ring
 rw [ha]
 apply cupXT; intro j; exact (H U x t v k u hk (A.leg j) i (loc_k _ hp _ (tintB ..))).mono (Eq.le (by ring))
-- maskM exact & stream.Price pay.Multiplicative.
def lush_k(q:Chi)(V:RG.Atom G a)(X:Finset (Cell f))(t:ℝ)(i:Site f)(U:Config G f):ℝ:= east q (V.footprint i) X t U* V.unmasked U i
def peer_k (V:RG.Atom G a)(X:Finset (Cell f))(t:ℝ)(i:Site f)(U:Config G f):ℝ:= if polP t U (V.footprint i) X then V.unmasked U i else 0
lemma sonK (V:RG.Atom G a)(U:Config G f)(X:Finset (Cell f))(q:Chi)(p:BudgetPoint)(t:=p.threshold)(i:Site f)(he:t=p.threshold)(ht:0<t)(h:∀ l∈ costA (V.footprint i)\ X, Pressure.toll U l ≤ t/2): lush_k q V X t i U=V.placed p U i:=by
 subst t; rw [lush_k,east_k _ _ _ _ ht h]; split
 next u=> rw [one_mul]; exact (masked_eq _ _ (fun v=>V.unmasked v i) _ u).symm
 next u=> rw [zero_mul]; exact (masked_ne _ _ (fun v=>V.unmasked v i) _ u).symm
lemma sunK (V:RG.Atom G a)(U:Config G f)(X:Finset (Cell f))(p:BudgetPoint)(i:Site f)(h:∀ l∈ costA (V.footprint i)\ X, Pressure.toll U l ≤ p.threshold): peer_k V X p.threshold i U= V.placed p U i:=by
 unfold peer_k; rw [← (propext (pol_g p.threshold U X _ h))]; split
 next u=> exact (masked_eq _ _ (fun v=>V.unmasked v i) _ u).symm
 next u=> exact (masked_ne _ _ (fun v=>V.unmasked v i) _ u).symm
end
end bound
end YM.CF.Cloak
