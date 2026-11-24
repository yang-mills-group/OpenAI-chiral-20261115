import YM.SU5.FiniteGaugeData.Cirrus.Sastrer
set_option autoImplicit false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.Seld.Poin.Cirrus
open Complex Filter Function Set MeasureTheory MeasureTheory.Measure Boundary OS OS.Semigroup Probe Maison Flute
open Mink Mink.General Vp.Folio
open scoped Topology NNReal InnerProductSpace
local notation "a"=>timeAxis
variable {H:Axis→Hilbert}(S:∀ i:Axis, OS.Semigroup (H i) i)
variable (Ω:(i:Axis)→(H i).space)(Ω':Bench (S a))(ht:Ω'.val=Ω a) (hΩ:∀ (i:Axis)(p:E4),M (S i) p (Ω i)=Ω i)
variable {ι:Type}(G:Canopy (H a) ι)(J K:Set ι)
open Gem Celeritas Land
variable (V:Gem.Tribe G){r:Axis→ℝ≥0}
variable (X:Action (H a))(L:Gem.Life S G Ω Ω' V X) (i:Axis)(B:Bag G r)
local notation "M'"=> G.ornate (S a) Ω'
abbrev νκ(B:Bag G r) := (B.map (fun x=> x.1 * G.ornate (S a) Ω' x.2.points x.2.chips)).sum
include L hΩ
lemma val_L (A:Cartouche G r) : inner ℂ (Ω i) (traceB S G V r i A (Ω i))=M' A.points A.chips:=by
 let X':= Ω i; let R:=traceB S G V r i A; let u:=ink G i A; let d:= -(r i:ℝ); let S₀:= S i; let f:= receiptI G V i
 have v:(billBefore S₀ G.grade d 0 u).adjoint X'= X':= ?_; swap; ·
    have hx:LaneE i d u:=(readyFw G i A).1; generalize he:u=w at hx ⊢; cases w with
    | nil=> rw [billBefore]; rw [show (1:(H i).Op).adjoint= 1 from star_one _]; rfl
    | cons j w=> rw [budgetFoot, show ContinuousLinearMap.adjoint _ =_ from warm_a S₀ _ (sub_pos.mpr (hx.2 _ List.mem_cons_self))]; exact earnO _ _ (hΩ i) _ (sub_pos.mpr (hx.2 _ List.mem_cons_self))
 rw [(realPlay S G V i Ω (hΩ i) A).1, L.votes _ _ _ _ _ (A.perm i) (PricesRoll G r i A),utop]; change inner ℂ X' ((billBefore S₀ G.grade d 0 u) _) = _; rw [← ContinuousLinearMap.adjoint_inner_left (billBefore S₀ G.grade d 0 u),v]; apply congrArg (fun A : (H i).Op=>inner ℂ X' (A X')) (Eq.symm (mappingF ..)) -- likely need rfl
 all_goals intros; rfl
lemma valediction: inner ℂ (Ω i) (oars S G V r i B (Ω i))=νκ S Ω' G B:=by
 induction B with | nil=> exact inner_zero_right .. | cons A B ih=> let x:= Ω i; change inner ℂ x (A.1 • traceB S G V r i A.2 x+ _)= _+_; rw [inner_add_right,inner_smul_right,val_L S Ω Ω' hΩ G V X L i A.2]; exact congrArg (fun t:ℂ=> A.1*M' A.2.points A.2.chips+t) ih
lemma stipendA (Z:(H i).Op)(B:ℕ→ Bag G r)(v:Wot (fun t=> oars S G V r i (B t)) Z): Tendsto (fun t=>νκ S Ω' G (B t)) atTop (𝓝 (inner ℂ (Ω i) (Z (Ω i)))):= (v.funds (Ω i) (Ω i)).congr fun t=> valediction S Ω Ω' hΩ G V X L i (B t)
#print axioms stipendA
end YM.CF.Buffered.Afterglow.Hierarchy.Seld.Poin.Cirrus
