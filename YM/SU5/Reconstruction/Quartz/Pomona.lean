import YM.SU5.Reconstruction.Quartz.Vapor
/-! # Equality invoices once Tilt cyclic in both (cyclic price easier here) -/
set_option autoImplicit false
noncomputable section
namespace YM.Quartz.Ship
open Function Set Filter MeasureTheory Spectral Analysis Metric ContinuousLinearMap Picket CrossedFrame Clasp BridgeClub Anvil Waltz Submodule
open scoped BigOperators Topology InnerProductSpace ComplexOrder NNReal ENNReal Complex
variable {H D K:Hilbert} (C:Clasp K H D)(F:H≃ₗᵢ[ℂ] D)
local notation "ϒ"=> F.conjStarAlgEquiv
variable (M:Net H)(N: Net D)
local notation "u"=> Pull F N
lemma both (A:H.Op): A∈ M ↔ ϒ A∈ Pull F.symm M:=by rw[pulling F.symm,run_base]
lemma awayRel(Ω:H)(h:owns_it M Ω): owns_it (Pull F.symm M) (F Ω):=by
 intro x; obtain ⟨x,rfl⟩:=F.surjective x
 let L:= parish M Ω; let G:=(parish (Pull F.symm M) (F Ω)); let T:= G.comap F.toLinearMap
 change x∈ T; suffices L≤T from this (h x)
 let t:IsClosed (T:Set H):= (Submodule.isClosed_topologicalClosure _).preimage F.continuous
 apply Submodule.topologicalClosure_minimal _ _ t; refine Submodule.span_le.mpr ?_; rintro _ ⟨x,k,rfl⟩; change F (x Ω)∈ G; exact le_topologicalClosure _ (subset_span (show F (x Ω)∈ (fun A:D.Op=> A (F Ω)) '' (Pull F.symm M:Set D.Op) from ⟨ϒ x,(both F M x).1 k,by simp [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply]⟩))
lemma reverseRel{M} (p:Pull F N=M) : Pull F N.commutant=M.commutant:=by
 apply VonNeumannAlgebra.ext; intro x; subst M; rw[pulling, VonNeumannAlgebra.mem_commutant_iff, VonNeumannAlgebra.mem_commutant_iff];
 refine ⟨fun p y h=> ?_, fun p y h=> ?_⟩
 · apply F.conjStarAlgEquiv.injective; change ϒ (y*x)=ϒ (x*y); rw[map_mul,map_mul]; exact p _ ((pulling ..).1 h)
 obtain ⟨i,r⟩:= F.conjStarAlgEquiv.surjective y; change ϒ i=y at r; subst y; rw[← map_mul,← map_mul,p i ((pulling ..).2 h)]
-- version to use for opposite-in-study
lemma rearWave (A:H.Op)(t:ℝ): (C.look.conjStarAlgEquiv (ascend t C A))=ascend (-t) C.Back (C.look.conjStarAlgEquiv A):= by rw [← go C C.look t A]; unfold ascend; rw [turnaside]
end YM.Quartz.Ship
