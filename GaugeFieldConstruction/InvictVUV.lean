import GaugeFieldConstruction.EldStarVUV
/-!
 # Boundary two mark price energy identity with implicit vacuum subtraction
 -/
set_option autoImplicit false
noncomputable section
namespace YM.NSF.Boundary
open YM.Boundary
open MeasureTheory Set Filter Function Mink Spectral Complex
open scoped Topology BigOperators InnerProductSpace Matrix
variable {G:Gauge} {D:Register G} {S:Table D} {W:Surface S} (R: Wightman S) {s:S.RealSpin}{K:S.Rotation} (h:R.Realizes (W:=W) K s)
local notation "Ω" => R.operators.vacuum
local notation "π" => R.operators
variable (x y: S.Union)(f g: Test4)
abbrev ArrΛVU := ElanΛVU R (R.operators.vector [(x,f)])
abbrev RetΛVU:= ArrΛVU R (R.J x) (Probe.bar f)
include h
-- adj: x appears as star vector. expect no invol demand on all.
lemma payEmitVU (a:R.operators.domain):inner ℂ (R.operators.vector [(R.J x,Probe.bar f)]) a.val=inner ℂ Ω ((π).field x f a).val:=by
 rw [← inner_conj_symm _ a.val,← inner_conj_symm _ ((π).field x f a).val]; exact congrArg (starRingEnd ℂ) (h.adj x f a (π).omega).symm
lemma payReadVU: W.expect [(x,f),(y,g)]-W.expect [(x,f)] * W.expect [(y,g)] = inner ℂ (RetΛVU R x f) (ArrΛVU R y g):=by
 let A:=R.operators.vector [(R.J x,Probe.bar f)]; let B:=R.operators.vector [(y,g)]
 have p: W.expect [(x,f),(y,g)]= inner ℂ A B:= (h.meets _).symm.trans (payEmitVU R h x f ((π).evaluates [(y,g)])).symm
 have q:W.expect [(x,f)]=inner ℂ A Ω:= (h.meets _).symm.trans (payEmitVU R h x f (π).omega).symm
 rw [p,q,show W.expect [(y,g)]=inner ℂ Ω B from (h.meets _).symm]; change _= inner ℂ (A-_ • Ω) (B-_ • Ω)
 rw[inner_sub_left,inner_sub_right,inner_sub_right,inner_smul_right,inner_smul_right,inner_smul_left,inner_smul_left, inner_self_eq_norm_sq_to_K,h.total.norm, inner_conj_symm]; simp; ring -- tune
lemma MintMarketVU: W.W 2 (![x,y]) (Joint.materialize 2 (![f,g]))-W.W 1 (![x]) (Joint.materialize 1 (![f])) * W.W 1 (![y]) (Joint.materialize 1 (![g])) = inner ℂ (RetΛVU R x f) (ArrΛVU R y g):=by
 rw [←payReadVU R h]
 -- three expectations. awkward casts via utility
 have h0(c:S.Union)(k:Test4):W.W 1 (![c]) (Joint.materialize 1 (![k]))=W.expect [(c,k)]:=by
     let p:Fin 1→Letter S:= ![(c,k)]
     have hp:=Work.C29.expectOfFn W p; rw [show Prod.fst∘p=![c] from (by funext i; fin_cases i; rfl), show Prod.snd ∘ p=![k] from (by funext i; fin_cases i; rfl), show List.ofFn p=[(c,k)] from ?_] at hp; exact hp.symm; simp [p, List.ofFn_succ]
 rw[h0,h0]; congr 1
 let q:Fin 2→Letter S:= ![(x,f),(y,g)]
 have he:= Work.C29.expectOfFn W q; rw [show Prod.fst∘q=![x,y] from (by funext i; fin_cases i <;> rfl), show Prod.snd ∘ q=![f,g] from (by funext i; fin_cases i <;> rfl), show List.ofFn q=[(x,f),(y,g)] from ?_] at he; exact he.symm; simp [q, List.ofFn_succ]
#print axioms payReadVU
#print axioms MintMarketVU
end YM.NSF.Boundary
end
