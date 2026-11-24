import YM.SU5.Reconstruction.Crease.BackLight
/-!
# Transport net by both linear & anti movers: bicommutant checks only.
-/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.BridgeClub
open Function Set Filter MeasureTheory Spectral Analysis Metric
open scoped BigOperators Topology InnerProductSpace ComplexOrder Pointwise
variable {H:Hilbert}
abbrev Net (H:Hilbert) := VonNeumannAlgebra H.space
def Auditorium (S:Set H.Op) : Net H where
 toStarSubalgebra:= StarSubalgebra.centralizer ℂ ↑(StarSubalgebra.centralizer ℂ S)
 centralizer_centralizer':= by
    change Set.centralizer (Set.centralizer (↑(StarSubalgebra.centralizer ℂ (↑(StarSubalgebra.centralizer ℂ S):Set H.Op)):Set H.Op))= (↑(StarSubalgebra.centralizer ℂ (↑(StarSubalgebra.centralizer ℂ S):Set H.Op)):Set H.Op)
    simp only [StarSubalgebra.coe_centralizer_centralizer]
    rw [Set.centralizer_centralizer_centralizer]
lemma lobby (S:Set H.Op)(p:∀ x∈S, star x∈S) : (Auditorium S:Set H.Op)=Set.centralizer (Set.centralizer S):=by
 change (↑(StarSubalgebra.centralizer ℂ (↑(StarSubalgebra.centralizer ℂ S):Set H.Op)):Set H.Op)=_
 rw [StarSubalgebra.coe_centralizer_centralizer,Set.union_eq_left.mpr (show star S⊆ S from ?_)]
 rw [← Set.image_star]; rintro y ⟨z,p',rfl⟩; exact p _ p'
lemma audition (S:Set H.Op) {x:H.Op} (q:x∈S): x∈ Auditorium S:= by
 change x∈ ((↑(StarSubalgebra.centralizer ℂ (↑(StarSubalgebra.centralizer ℂ S):Set H.Op)):Set H.Op):Set H.Op); rw [StarSubalgebra.coe_centralizer_centralizer]; exact Set.subset_centralizer_centralizer (Set.mem_union_left _ q)
lemma houseGrow {S T:Set H.Op}(p:S⊆T): Auditorium S ≤ Auditorium T:=StarSubalgebra.centralizer_le _ _ _ (StarSubalgebra.centralizer_le _ _ _ p) -- tune
lemma houseFire {S T:Set H.Op}(p:∀ x ∈ S,star x∈ S)(q:∀ y ∈ T,star y∈ T)(h:∀ x∈S,∀ y∈T, Commute x y): Auditorium S ≤ (Auditorium T).commutant:=by
 have t:T ⊆ Set.centralizer S:= fun z b y u=> h _ u _ b
 have v:= Set.centralizer_subset t
 intro x e; rw [VonNeumannAlgebra.mem_commutant_iff]; -- WANT commute auditorium T with S double via centralizer triple and H other orientation.V wrong direction?
 rw [← SetLike.mem_coe, lobby S p] at e
 -- t implies centralizer(centralizer S) ⊆ centralizer T. Good.Then T'' comm
 intro g r; rw [← SetLike.mem_coe, lobby T q] at r; exact (r x (v e)).symm
lemma rehouse {S T:Set H.Op}(p:∀ x ∈ S,star x∈ S)(q:∀ y ∈ T,star y∈ T){V W:H.Op→H.Op}(h:∀ x∈ S, V x∈ T) (u:LeftInverse W V)(z:RightInverse W V)(g:∀ x y,V (x*y)=V x*V y) (x:H.Op)(b:x∈ Auditorium S): V x∈ Auditorium T:=by
 rw [←SetLike.mem_coe,lobby T q]; rw [←SetLike.mem_coe,lobby S p] at b
 intro t v; have hy : W t∈Set.centralizer S:= by
   intro r p; apply u.injective; rw [g,g,z t]; exact v (V r) (h r p)
 have hh:= congrArg V (b _ hy); rwa [g,g,z t] at hh
end YM.BridgeClub
