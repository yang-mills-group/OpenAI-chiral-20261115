import YM.CF.DPress.Chess.Flow.Robe
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace YM.CF.DPress.Chess.Transit.Robe
open Function Filter Lattice RG Wilson MeasureTheory ProbabilityTheory Push.GridApprox FD Skye Tree Precision Rush Spire Scree
open Cube (More assembly)
open scoped Topology BigOperators Pointwise Classical ENNReal NNReal
variable {n:Side}{P:Loom n} {u d:ℝ}{r:ℕ}
-- use same read requirements for all μ_F with R_F bigger than purchased; sharp equality irrespective of chosen Φ.
variable (X:Firm P u r)
local notation "Ξ_" => Ties SU.group
open Star OrderF
private lemma lou_t{n:Side} (S:Support n){a b:ℕ}(p:a ≤ b) : halo a S⊆ halo b S:=fun _ t=> by obtain ⟨i,g,h⟩:= halo_spec.mp t; exact halo_spec.mpr ⟨i,g,h.trans p⟩
include X
lemma twinP (S T: Support (More n))(x:Pane n)(h: Far r (halo r S) (halo r T)): Pairm (τ P x) (Ξ_ S) (Ξ_ T):=by
 obtain ⟨k,u,a,I,o,U,H⟩:= X; letI:MeasurableSpace I:=⊤; letI:MeasurableSingletonClass I:=⟨fun _=>trivial⟩; let V:= BasicIid.orb (fun _:Seat n=>SU.group.probHaar); let E:= (Coral n).prod U.V.c.PM; let Z:=uncurry (fairly U x); have ht:k≤ r:=by omega
 have hx(Y:Support (More n)): Respects (joins (V.see (halo k Y)) (U.V.set (halo k Y))) (Ξ_ Y) Z:= fun x y w=> worth U Y w.2 (fun _ _ _=> rfl) (BasicIid.key.mp w.1)
 let ℓ:=halo k S; let t:=halo k T; have he: Far k ℓ t:= h.down ht (lou_t _ ht) (lou_t _ ht); have hv:= Pairm.ofOrd (OrderF.extend U.V) he
 let v: FD.Meeting (BasicIid.P2 _) ℓ t:=BasicIid.P2U.mpr (Finset.disjoint_left.mpr (fun i l y=> (by simpa using he i l i y))); exact ((Pairm.ofOrd V v).joint hv).map ⟨fair_m U x, (H x).symm⟩ (hx _) (hx _)
lemma pair_map {A:Support (More n)}{x y:Pane n}{H:Type*}[MeasurableSpace H](f:Pane n→H)(v:Measurable f)(h:Uses f (Ξ_ A))(t:Agrees (halo r A) x y): (τ P x).map f= (τ P y).map f :=by
 obtain ⟨k,u,a,I,o,U,p⟩:= X; letI:MeasurableSpace I:=⊤; letI:MeasurableSingletonClass I:=⟨fun _=>trivial⟩; unfold τ; rw [p x,p y,Measure.map_map v (show Measurable (uncurry (fairly U x)) from fair_m ..),Measure.map_map v (show Measurable (uncurry (fairly U y)) from fair_m ..)]; exact congrArg (fun a:(View n × I)→ H=>Measure.map a ((Coral _).prod U.V.c.PM)) (funext fun i: View n × I=>h _ _ (worth U A ((U.V.set (halo k A)).iseqv.refl i.2) (agrees_mono t (Finset.coe_subset.mpr (lou_t _ (by omega)))) (fun _ _=> rfl))) -- tune Omega
lemma samePrice {A:Support (More n)}{x y:Pane n}{H:Type*}[NormedAddCommGroup H][NormedSpace ℝ H][SecondCountableTopology H][MeasurableSpace H][BorelSpace H](f:Pane n→ H)(m:Measurable f) (v:Uses f (Ξ_ A))(t:Agrees (halo r A) x y): (∫ i,f i∂τ P x)=(∫ i,f i∂τ P y):=by
 have e(x:Pane n): (∫ i,f i∂τ P x)=(∫ i,id i∂(τ P x).map f):=expect f ⟨m,rfl⟩ id measurable_id; rw [e x,e y,pair_map X f m v t]
end YM.CF.DPress.Chess.Transit.Robe
