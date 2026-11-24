import YM.CF.BPress.Envelope
/-! Draw full dummy copies but use only the variables named (at templated charged links). This lets each use of these links pay only the new independent noise occurrences. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress.Law
open Function MeasureTheory RG Wilson Lattice Push.SectorMeasure Env
open scoped Topology ENNReal NNReal BigOperators Classical
variable {X Z : Type*} {G : Gauge} {I : Type*}[Fintype I] [MeasurableSpace X][MeasurableSpace Z][NormedAddCommGroup Z][NormedSpace ℝ Z][CompleteSpace Z][BorelSpace Z][SecondCountableTopology Z]
variable (S:Finset I) (μ:Measure X) [IsProbabilityMeasure μ]
def brief (f : I→X)(i:↥S):= f i.val
def chartIn (f: ↥S→X)(x:I→X) (i:I):= if p:i∈S then f ⟨i,p⟩ else x i
lemma chartIn_cli (x:I→X) : Measurable (fun f=> chartIn S f x):=by apply measurable_pi_lambda; intro i; unfold chartIn; split <;> fun_prop
lemma rep_in {x y:I→ X}: rep S x y=chartIn S (brief S x) y:=by funext i; unfold rep chartIn; split <;> simp_all [brief]
lemma chart_mem {f: ↥S → X}{y:I→X}{i:I}(p:i∈ S): chartIn S f y i=f ⟨i,p⟩:=dif_pos p
lemma sect_mem : MeasurePreserving (brief S (X:=X)) (chain μ I) (chain μ S) := by apply keys (f:=fun i:↥S=>i.val) μ; exact Subtype.val_injective
-- use when s given. Composing by deleting coordinates only. Law.keep select any.
lemma restore_at (f:(I→X)→ Z)(h:Envelope f)(v:I→X) :
    (∫ u, f (rep S u v)∂chain μ I)=(∫ u,f (chartIn S u v) ∂chain μ S):=by simp_rw [rep_in S]; exact (restore _ _ _ (sect_mem S μ) (fun u=> f (chartIn S u v)) (integrableX (Env.along h (chartIn_cli S v)) _)).symm
variable (f:(I→G.El)→Z) (h:Envelope f) (v:I→ G.El)
include h
lemma choice_at (r : ℝ)(w : I→ G.El)[IsProbabilityMeasure (noise G r)]:
   (∫ x, f (rep S (v*x) w) ∂chain (noise G r) I)=(∫ x, (∏ i∈S,chord.ballDensity r (v i) (x i)) • f (rep S x w)∂chain G.probHaar I):=by
 let g:= fun x:↥S→ G.El=> f (chartIn S x w); let U:=brief S (X:=G.El); let b:=U v; let V(x:↥S→ G.El):=(∏ i:↥S, chord.ballDensity r (b i) (x i)) • g x
 have hx : Envelope g:=Env.along h (chartIn_cli S w); have hv:Envelope V:=Env.scale (vl_cost ..) hx
 rw [show (∫ x, f _ ∂chain _ _)=(∫ x,g (b*U x)∂chain (noise G r) I) from (integral_congr_ae (Filter.Eventually.of_forall fun x=>?_))]; swap; · dsimp only; rw [rep_in (X:=G.El)]; rfl -- tune
 rw [← restore _ _ _ (sect_mem S (noise G r)) (fun x=>g (b*x)) (integrableX (Env.along hx (g:=fun x=>b*x) (by fun_prop)) _), translate_at _ _ hx b, restore _ _ _ (sect_mem S G.probHaar) V (integrableX hv _)] -- tune
 apply integral_congr_ae; apply Filter.Eventually.of_forall; intro x; unfold V g; dsimp only; rw [rep_in S, ← Finset.prod_attach S]; rfl -- tune attach
end YM.CF.BPress.Law
