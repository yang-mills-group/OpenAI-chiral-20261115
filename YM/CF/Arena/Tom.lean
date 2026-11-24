import YM.CF.Arena.Pearl
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.CF.Arena
open Function Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch MeasureTheory NormedSpace Nacre Braid Font
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace Matrix Kronecker
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Push.Uniform (curve Slope tint partSpace meetVar)
open AnalyticBridge.Annulus1AD AnalyticBridge.SectorAffine Oriented Esti Vol Bloch Exterior Jet
open RG Forge Cay Slate Rel
local notation "G"=> SU.group
variable {c f:Side}{S:StepData c f}{T:Tube SU.group S}{F:Forest S.ratio}{q:Chi}{s:Signed}{l n:ℕ}{x d β C D σ m:ℝ}{P:Tab S}{V:Config SU.group c}
section
variable (x:ℝ)(j r:ℕ)(Φ:Tab S→FileM c G)(A:Tab S→DirP c) {Z:Tab S}{a:Stores S}{i y:Site c}{p m L:ℕ}{M A' D' e u:ℝ}{k:ℕ}
lemma payW(a:Stores S)(V:Config G c)(P:Tab S)(h:Woven Φ A L k n σ C D)(p:C≥0)(hp:D≥0)(he:e≥0)(t:ℝ)(hu:0≤t) (H:∀ i:Site c, i ∉ a.dome (r*radiusB x)→∀ f,CakeF f i L n σ C → cFoot 2 (satX f)→ (∀ j, 2 ≤ j→ j ≤ k→‖cake j (satX f)‖ ≤ D)→ Allows n (f ∘ Vmove x V) 0 e)(Q:∀ i:Site c,i ∉ a.dome (j*radiusB x)→ Allows n (Φ P i ∘ Vmove x V) 0 t) (i:Site c): Allows n (issued x j r Φ A a P i ∘ Vmove x V) 0 (t+(plot L*e+ plot L*e)):=by -- fix binder
 let Y:= cClip x r A a P; let Z:= a.dome (r*radiusB x); let X:=a.dome (j*radiusB x)
 let p' := pavilion L i; let U:= Vmove x V; have hU(z y):Allows n (Y z y ∘ U) 0 e:=by
    unfold Y cClip; split
    next p=> exact H _ p.1 _ (h.crew P z y).1 (h.crew P z y).2.1 (h.crew P z y).2.2
    next p=> exact Jet.allows_const _ ((norm_zero).le.trans he)
 have he(i y:Site c)(hv:L < separation i y): Y i y=0:=by unfold Y cClip; split; exact not_not.mp fun u=> hv.not_ge (h.dawn _ i y u); rfl
 have hZ : dict Y i=(∑ y∈p', Y y i) -(∑ y∈ p', Y i y):=by unfold dict; apply congrArg₂ (·-·); symm; apply sum_subset (subset_univ _); intro y _ hh; apply he; rw [separation_comm]; exact not_le.mp (mt (theatre ..).mpr hh); symm; exact Finset.sum_subset (subset_univ _) fun y _ hu=> he i y (not_le.mp (mt (theatre ..).mpr hu))
 let P'(V):ℂ:= if i∈X then 0 else Φ P i V
 have hp': Allows n (P' ∘ U) 0 t:=by
    by_cases h:i∈X; unfold P' Function.comp; simp only [if_pos h]; exact Jet.allows_const _ ((norm_zero).le.trans (by assumption)); unfold P' Function.comp; simp only [if_neg h]; exact Q _ h
 have hW:P' ∘ U + ((fun v=>∑ y∈p', (Y y i ∘ U) v)-(fun v=>∑ y∈p',(Y i y ∘ U) v))= issued x j r Φ A a P i ∘ Vmove x V:=by
    unfold issued; funext v; rw [Function.comp_apply, show cClip x r A a P=Y from rfl,hZ]; simp only [Pi.add_apply,Pi.sub_apply,Function.comp_apply,Finset.sum_apply, P', X,U]; split <;> rfl
 have hx: #(p')*e ≤ (plot L:ℝ)*e:= mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (pay_v _)) (by assumption)
 rw [← hW]; exact hp'.add (Newt.subtract_p ((summed (V:=fun y=> Y y i ∘ U) _ (fun y _=> hU y i)).mono hx) ((summed (V:=fun y=>Y i y ∘ U) _ (fun y _=>hU i y)).mono hx))
end
end YM.CF.Arena
