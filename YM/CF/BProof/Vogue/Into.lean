import YM.CF.BProof.Vogue.Throng
/-! Sampling backup and reindexing board. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Vogue
open Function Filter MeasureTheory ProbabilityTheory Skye Spire Lattice Wilson Mesh Shore Finset Equiv
open scoped Topology BigOperators NNReal ENNReal Classical
variable {K: Type}{n:Side}{d u:ℝ}{k r L:ℕ}(P:Spice n K d u k L)(M:Finset (Seat n))
abbrev BoardB (M:Support (Cube.More n))(r:ℕ)(K:Type) := (Fleets M r→ K) × (Fleets M r→ Sweep n)
local notation "Ψ" => BoardB M r K
def seed_at (X:Pane n)(Z:BoardB M r K): Pane n:= fun i=> if h:Bubb M r i then mend (P.P (Z.1 (point M i h))) (Z.2 (point M i h)) X i else X i
lemma seed_meas(V:BoardB M r K): Measurable (fun X=> seed_at P M X V):=by
 apply measurable_pi_lambda; intro i; unfold seed_at; split; rename_i q; exact (measurable_pi_apply i).comp (mine (P.ok _) _).meas; exact measurable_pi_apply _
-- pullover
lemma guardMP(s:Sweep n):∃ E:Equiv.Perm K, ∀ t, mend (P.P (E t)) s=P.P t:=by
 obtain ⟨E,h⟩:=P.ride s.s ((Cube.assembly n).embed s.b) s.charge; refine ⟨E,fun t=>funext (fun i=>?_)⟩; unfold mend; rw [show P.P (E t) (flashA s i)= flashA s (P.P t i) from by rw [Skye.revoke,Skye.revoke]; exact h t i, revB]
private def knitB {A B:Type*}(U:B→Equiv.Perm A): Equiv.Perm (A×B) where
 toFun x:= (U x.2 x.1,x.2)
 invFun x:=((U x.2).symm x.1,x.2)
 left_inv x:=by simp
 right_inv x:=by simp

lemma shuffle (p:k≤ r)(h:k+1+(k+1)+L≤2*r+20):∃ E₁ E₂: Equiv.Perm (K × BoardB M r K),∀ U:Pane n, M=RG.flags u U→∀ i, seed_at P M U (E₁ i).2=P.P (E₂ i).1 U:=by
 obtain ⟨V,hv⟩:= epoch P M p h; choose E hE using guardMP P; let i(X:Fleets M r→Sweep n):=(Equiv.piCongrRight fun l=> E (X l))
 let P₁:Perm (K × BoardB M r K):= prodCongr (Equiv.refl K) (knitB i); let P₂:= prodCongr V (Equiv.refl (Fleets M r→ Sweep n)); let j:= prodAssoc K (Fleets M r→ K) (Fleets M r→ Sweep n); let P₂': Perm (K × BoardB M r K):= j.symm.trans (P₂.trans j)
 refine ⟨P₁,P₂',fun U hU i=> ?_⟩; funext e; unfold seed_at; split
 · rename_i H; let k:=point M e H; change mend (P.P (E (i.2.2 k) (i.2.1 k))) (i.2.2 k) U e=_; rw [hE]; exact (hv U hU (i.1,i.2.1) e H).symm
 next v=> exact ((P.ok _).covers _ _ (hU ▸ not_not.mp fun g=>v (bubble_s p ((pieV ..).2 g)))).symm -- syntax

variable [Fintype K][Nonempty K]
def skill (K:Type)[Fintype K][Nonempty K](t:Ids n):BoardB M r K:= (fun i=>brush K t i.val,fun i=> timb i.val t)
lemma skills {M:Finset (Seat n)}(X:Ids n)(A:Pane n)(e: M=RG.flags u A): seed_at (r:=r) P M A (skill M K X)=burn P r (A,X):=by
 subst M; funext i; unfold burn; dsimp only; unfold seed_at; split <;> rfl

variable [MeasurableSpace K] [MeasurableSingletonClass K]
lemma rawmp : MeasurePreserving (fun t:Ids n=> (show BoardB M r K×Root n from (skill M K t,frameP t))) (depot n) ((paperMeas (BoardB M r K)).prod (rootM n)):=by
 rw [parcelPair]; rw [parcelPi K,parcelPi (Sweep n)]
 exact value_p (fun i:Fleets M r=> i.val) (cashS M r) (separates M r)
end YM.CF.BProof.Vogue
