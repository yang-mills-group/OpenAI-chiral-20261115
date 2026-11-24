import YM.SU5.FiniteGaugeData.Tapestry.Awnings
import YM.SU5.FiniteGaugeData.Tapestry.Junction
set_option autoImplicit false
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tapestry
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder ENNReal Classical
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock
open Satin
attribute [local instance] opCStarAlgebra

/-! # The other side of menu compactness (upper argument of the actual push) -/
section move
variable {I:Type*}(N: I→ Side)(P: I→ Side)(L:Side)(p:∀i, (P i).val = (N i).val*L.val)
    (F:(i:I)→Forest (ratio (bead N L P p i)))(S:Finset Cover)(q:Chi)(d:ℝ)
    (v:0<d)(u:2*d<firstRadius SU.group)(V:(i:I)→ Pane (N i))(z:(i:I)→ Edge (Seat (P i)))
local notation "G"=> bead N L P p
private lemma foldsDeal (a:(i:I)→ Seat (P i)) : Deal (I:=I) (T:=fun _=>SU.E) (fun i (x:PairsC)=> (F i).foldAt (graft S (P i) x.2) (a i)):=by
  refine Shelf.slight ?_ (fun i=> ((F i).folds _).measurable.comp ((graft_b ..).comp measurable_snd))
  refine (travelShelf P _ (fun e=> graftShelf S P Prod.snd e) a (fun i=> (F i).hike (a i)) (4*L.val) ?_).thenDo (fun f x=> (f x)⁻¹)
  intro i; exact ((F i).hike_lower _).trans ((F i).bound _)
include v u
lemma foldedDeal : Deal (X:=PairsC) (I:=I) (T:=fun _=>SU.E) (fun i x=> seine (G i) (F i) q d (graft S (P i) x.2) (V i) (z i)):=by
  let A(i:I)(x:PairsC): Seat (P i) → SU.E:= (F i).foldAt (graft S (P i) x.2)
  let a(i:I):= (z i).1; let b(i:I):=(z i).1+step (z i).2
  let X(i:I)(x:PairsC):Pane (P i):= graft S (P i) x.2
  let Y:=fun i x=> X i x (z i); let Y'(i:I)(x:PairsC):= Precision.replica (ratio (G i)) (show Config SU.group _ from V i) (z i)
  let W(i:I)(x:PairsC):= gauge (A i x) (X i x) (z i)
  have h₀ : Deal (I:=I) (T:=fun _=>SU.E) Y:= Shelf.slight (graftShelf S P Prod.snd z) (fun i=> (measurable_pi_apply _).comp ((graft_b ..).comp measurable_snd))
  have he := foldsDeal N P L p F S a
  have ht := foldsDeal N P L p F S b
  have hv: Deal W:= (((he.prod h₀).post (continuous_fst.mul continuous_snd)).prod ht).post (continuous_fst.mul continuous_snd.inv)
  have hw : Continuous (fun x:SU.E×SU.E=> knit q d x.1 x.2):= (SU.group.lieExp_cont.comp ((patched_continuous q v u).comp (continuous_fst.mul continuous_snd.inv))).mul continuous_snd
  have h:Deal (T:=fun _:I=>SU.E) (fun i x=>knit q d (W i x) (Y' i x)):= (hv.prod (show Deal Y' from Deal.pure _)).post hw
  exact (((he.prod h).post (continuous_fst.inv.mul continuous_snd)).prod ht).post (continuous_fst.mul continuous_snd.inv.inv)

omit v u
variable (j D:ℕ)(vA:LaurentRadius j L D)(ho:Odd L.val)
variable (M:I→ Male)(Q: I→Op SU.Slot){γ:ℝ}(w:∀i,‖Q i‖ ≤ γ)
variable (V':(i:I)→Fields (N i))
local notation "run" i:max=>gathered (G i) j (Q i) (M i) ho q d
include v u vA w
lemma upperSewn (h:Chorus): Menu (T:=fun i=>FC (Single (P i)))
   (fun (i:I)(x:PairsC)=> (run i) (wholeZ (N i) h) (replant S (P i) x) (V' i)):=by
  let J(i:I):= Forest (ratio (G i))
  refine circle (J:=J) ?_
  apply wool (fun a:Σ i,J i=> N a.1) L (fun a=>P a.1) (fun a=> p a.1) j D vA ho (fun a=> M a.1) (fun a=> Q a.1) (fun a=>w a.1)
     (fun a x=> middle (G a.1) q d a.2 (replant S (P a.1) x) (V' a.1)) _ h
  intro a; exact foldedDeal _ _ _ (fun a: Σ i,J i=> p a.1) (fun a=> a.2) S q d v u (fun a=>(V' a.1).2) _ -- missing arg a?
end move

section transfer
variable {I X:Type*}[MeasurableSpace X]{P:I→Type*}{T:I→Type*}[∀i,MeasurableSpace (T i)][∀i,NormedAddCommGroup (P i)][∀i,NormedSpace ℝ (P i)][∀i,CompleteSpace (P i)]
variable (μ:(i:I)→ Measure (T i)) [∀i,IsProbabilityMeasure (μ i)](D:(i:I)→ X→ T i→ℝ)(A:(i:I) → X→ T i→ P i)
    (h:Menu (T:=fun a:Σ i,T i=> P a.1) (fun (a:Σ i,T i) x=> A a.1 x a.2))
    (pos:∀ i x y,0≤D i x y)(tot:∀ i x, ∫ a, D i x a ∂μ i=1)
    (den:∀ i x,Integrable (D i x) (μ i))(int:∀ i x x', Integrable (fun y=> D i x y • A i x' y) (μ i))
include h pos tot den int
theorem honored (p:∀ δ:ℝ,0<δ→ ∃ P:Deck X, P.dark ∧ ∀ x y, P.withZ x y→ ∀ i u, |D i x u-D i y u| ≤ δ*D i y u):
    Menu (T:=P) (fun i x=> ∫ t, D i x t • A i x t∂μ i):=by
  obtain ⟨C,c,u⟩:= h.budget
  have hv (i x x') : ‖∫ a, D i x a • A i x' a∂μ i‖ ≤ C:=by
    nth_rw 1 [show C= (∫ a, D i x a∂μ i)*C from (by rw [tot,one_mul]),←integral_mul_const]
    refine norm_integral_le_of_norm_le ((den i x).mul_const C) (Filter.Eventually.of_forall fun a=>?_)
    rw [norm_smul, Real.norm_of_nonneg (pos i x a)]; exact mul_le_mul_of_nonneg_left (u ⟨i,a⟩ x') (pos ..)
  refine ⟨?_,C,c,fun i x=>hv i x x⟩
  intro ε e; let d:= ε/(2*(1+C)); have hd:0<d:=by unfold d; positivity
  obtain ⟨B,b,v⟩:=p d hd; obtain ⟨F,f,w⟩:= h.deal d hd
  refine ⟨(B:Finset _)∪ F,B.join F b f,fun x y h i=>?_⟩
  refine lt_of_le_of_lt (dist_triangle _ (∫ a, D i x a • A i y a ∂μ i) _) ?_
  have hf:x=x:=rfl -- tune remove
  rw [dist_eq_norm,dist_eq_norm]; refine add_le_add ?_ ?_ |>.trans_lt (show d+d*C< ε from (by have he:d*(2*(1+C))=ε:= div_mul_cancel₀ _ (by positivity); linarith))
  · rw [←integral_sub (int i x x) (int i x y)]
    have hp(u:T i): ‖D i x u • A i x u-D i x u • A i y u‖ ≤ D i x u *d:=by
      rw [←smul_sub,norm_smul,Real.norm_of_nonneg (pos ..),←dist_eq_norm]; exact mul_le_mul_of_nonneg_left (w x y (Deck.grow subset_union_right _ _ h) ⟨i,u⟩).le (pos ..)
    refine (norm_integral_le_of_norm_le ((den i x).mul_const d) (Filter.Eventually.of_forall hp)).trans_eq ?_; rw [integral_mul_const,tot,one_mul]
  rw [←integral_sub (int i x y) (int i y y)]
  have hp(t:T i): ‖D i x t • A i y t-D i y t • A i y t‖ ≤ (d*D i y t)*C:=by
    rw [←sub_smul, norm_smul]; exact mul_le_mul (v x y (Deck.grow subset_union_left _ _ h) i t) (u ⟨i,t⟩ y) (norm_nonneg _) (mul_nonneg hd.le (pos ..))
  refine (norm_integral_le_of_norm_le (((den i y).const_mul d).mul_const C) (Filter.Eventually.of_forall hp)).trans_eq ?_; rw [integral_mul_const, integral_const_mul,tot,mul_one]
end transfer
end YM.CF.Buffered.Afterglow.Tapestry
#print axioms YM.CF.Buffered.Afterglow.Tapestry.honored
