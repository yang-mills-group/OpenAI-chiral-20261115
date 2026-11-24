import YM.CF.Skye.Pine
set_option autoImplicit false
noncomputable section
namespace YM.CF.Skye
open Function Filter Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory Mesa ProbabilityTheory
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
theorem roofs_small (b d:ℝ)(h:0<b)(t:0<d) :∃ N:ℕ,∀ B:Side,N≤B.val → ∃ k u,0<u∧u ≤ b ∧∀ m:Side,2≤m.val→ ∃ P,Roof (CSide m B) u d k P:=by
 obtain ⟨g,c,H⟩:=taxon t; obtain ⟨N,J⟩:= trench c; refine ⟨N,fun B v=>?_⟩
 obtain ⟨u,p,K⟩:= J _ v; let T:=min b u; refine ⟨2*B.val,T,lt_min h p,min_le_left ..,fun m r=>?_⟩; obtain ⟨F,g'⟩:= K m r; have hh: Prequel m B g T F:= ⟨g'.1,g'.2.1,fun a=> ⟨fun U hv=> (g'.2.2 a).1 U (fun x p i=> (hv _ p i).trans (min_le_right ..)), (g'.2.2 a).2⟩⟩; have ht:= repairB F hh
 refine ⟨sun F _ _,⟨fun x=>H _ _ ?_,sunM _ _ _ ht.meas,fun V X s=>sun_g _ _ _ _ _ _,fun V X i h=> sun_v _ _ _ _ _ h _,fun V X i=>sun_here _ _ _ _ _ _,sunW F ht⟩ ⟩
 rw [sun,RG.gauge_flags]; exact lightLegal ht _
end YM.CF.Skye
