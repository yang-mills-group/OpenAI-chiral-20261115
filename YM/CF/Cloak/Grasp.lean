import YM.CF.Cloak.Flux
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
abbrev costA(X:Support f):= univ.filter fun i:Cell f=> ¬Disjoint X (touched i)
def polP (t:ℝ)(U: Config G f)(X:Support f)(A:Finset (Cell f)): Prop:=∀ i∈A∩costA X,Pressure.toll U i≤t
lemma green_k(t:ℝ)(U:Config G f)(X:Support f):Healthy t X U↔ polP t U X univ:=by
 constructor; intro p i h; obtain ⟨y,h,z⟩:=Finset.not_disjoint_iff.mp ((mem_filter.mp (mem_inter.mp h).2).2); exact le_of_not_gt fun g=> disjoint_left.mp p h ((flags_spec ..).2 ⟨i,z,g⟩)
 intro p; apply Finset.disjoint_left.mpr; intro j a v; obtain ⟨i,t,h⟩:= (flags_spec ..).1 v; exact h.not_ge (p _ (mem_inter.mpr ⟨mem_univ _,mem_filter.mpr ⟨mem_univ _,fun v=>Finset.disjoint_left.mp v a t⟩⟩))
def nose(q:Chi)(t:ℝ)(A:Finset (Cell f))(X:Support f) : Config G f→ ℝ:=wrapM q t (costA X \ A)
lemma pol_g(t:ℝ)(U:Config G f)(F: Finset (Cell f))(Y:Support f)(h:∀ i∈ costA Y\ F,Pressure.toll U i≤t):Healthy t Y U↔ polP t U Y F:=by
 rw [green_k]; constructor
 · intro p i v; exact p i (mem_inter.mpr ⟨mem_univ _,(mem_inter.mp v).2⟩)
 intro p i v; by_cases l:i∈F; · exact p i (mem_inter.mpr ⟨l,(mem_inter.mp v).2⟩)
 exact h _ (mem_sdiff.mpr ⟨(mem_inter.mp v).2,l⟩)
lemma coat (h:x₀∈tsupport (nose q t A X₂ ∘ U))(p:polP t (U x₀) X₂ A)(hp:0<t)(u:∀ i∈costA X₂,Tender (fun y=>faceValue (U y) i) x₀ v n): Healthy t X₂ (U x₀):= (pol_g t (U x₀) A X₂ fun i t'=> aboard q _ hp _ h i t' (u i (mem_sdiff.mp t').1)).mpr p
def east (q:Chi)(X:Support f)(F:Finset (Cell f))(t:ℝ) : Config G f→ℝ:=fun V=> if polP t V X F then nose q t F X V else 0
lemma east_k(q:Chi)(X:Support f)(F: Finset (Cell f))(s:ℝ)(h:0<s)(p:∀ i∈ costA X \ F,Pressure.toll U₀ i ≤ s/2): east q X F s U₀= if Healthy s X U₀ then 1 else 0 :=by -- tune U₀
 unfold east; by_cases g:Healthy s X U₀; · rw [if_pos g,if_pos ((pol_g _ _ F X fun i t=>(p _ t).trans (half_le_self h.le)).mp g)]; exact pure_w q _ _ h p
 rw [if_neg g,if_neg (mt ((pol_g _ _ F X fun i t=>(p _ t).trans (half_le_self h.le)).mpr) g)]
lemma nose_h (p:x₀∈tsupport (east q X₂ A t ∘ U)):x₀∈tsupport (nose q t A X₂ ∘ U):=closure_mono (s:=Function.support (east q X₂ A t ∘ U)) (t:=Function.support (nose q t A X₂ ∘ U)) (fun i h l=> h (by unfold Function.comp east; split; exact l; rfl)) p -- tune elabor
lemma form_h (q:Chi)(p: HeldT U A x₀):∀ᶠ i in 𝓝 x₀,east q X₂ A t (U i)=(if polP t (U x₀) X₂ A then nose q t A X₂ (U i) else 0):=by
 refine p.mono fun i u=>?_ ; have he:polP t (U i) X₂ A ↔ polP t (U x₀) X₂ A:=forall_congr' fun j=>imp_congr_right fun t=> by rw [Pressure.toll, u _ (mem_inter.mp t).1]; rfl
 unfold east; rw [show _=_ from propext he] -- tune motive dep
lemma bright_k(q:Chi)(n:ℕ)(D:ℝ)(p:m ≤ D): ∃ v:ℝ,0≤v ∧ ∀ {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E]{f:Side}(t:ℝ)(U:E→ Config G f)(X:Support f)(F:Finset (Cell f))(x:E),0<t → HeldT U F x → (∀ i∈costA X,Tender (fun y=>faceValue (U y) i) x (D*t) n) → Allows n (east q X F t ∘ U) x (priceK n (costA X).card v) ∧ (x∈tsupport (east q X F t ∘ U) → Healthy t X (U x)):=by
 obtain ⟨K,h,H⟩:=starchy q D n p; refine ⟨K,h,@fun E _ _ f t U X F x p u g=>?_⟩; have ht:=form_h (X₂:=X) (t:=t) q u
 by_cases v:polP t (U x) X F
 · refine ⟨((H t p (costA X \ F) U x fun i p =>g i (mem_sdiff.mp p).1).mono ?_).germ (ht.mono fun s hp=>by simpa [v,nose] using! hp.symm),fun y=>coat (nose_h y) v p g⟩
   unfold priceK; gcongr; exact sdiff_subset
 have he:east q X F t ∘ U=ᶠ[𝓝 x] (fun _=>0):= by simpa only [v,↓reduceIte] using! ht
 exact ⟨(allows_const _ (v:=(0:ℝ)) (by rw [norm_zero]; unfold priceK; positivity)).germ he.symm, fun h=>False.elim ((notMem_tsupport_iff_eventuallyEq.mpr he) h)⟩
end bound
end YM.CF.Cloak
