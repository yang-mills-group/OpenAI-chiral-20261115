import YM.CF.BProof.Bias.Relate
/-! Existence of local pressure payment, with uniform branch A constant
and a separately-bought Π at p. Kernel read on actual Loft and priced gauges,
but only tested here with (U=1,...). -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Bias
open Function Filter Fock Finset Branch Tenant Cube SU Tulip Lat Lattice Dial Spin Fig Align Stint Wick Hearth
open Fir Laurent Rush Bloch Next.Free BZ Real Tape
open scoped Topology BigOperators Matrix MatrixOrder InnerProductSpace Kronecker Matrix.Norms.L2Operator Hearth
attribute [local instance] opCStarAlgebra
-- uniform in symbols. A read at chosen data.
variable {a b l r δ c v η:ℝ}{j:ℕ} (P: Spin.Ready j a b l r) (A B: Stamp)(D:A≠B)(e:1≤v)(d:0<c)(h:1≤j)
include D h
private lemma earned(k:0 < (c:ℝ))(s: Stint.Pay) : ∃ g:ℝ,∃ t:ℕ,0<g ∧ ∀ {N:Side}{c':ℝ}(M:Male) (J R U Y:Finset (Per N)), Free c' j M R → Extend U Y t → ∀ {C:Quilt N}, Call R J A B C→ (pair C)ᵀ= -pair C → ∀ {L:Type}[TopologicalSpace L](b:Feet N L){Z:Raw L (Single N)} (x:L) (a e:Tag b.st), Earn s a e Z→ Z x= Plus j M R C → (∀ i:Single N, ht i∈ Y→ ‖acts (star (Z x)) (basisKet i)‖≤g)→ ‖commP j M R J*Seat U‖ ≤ c :=by
 obtain ⟨w,cP,F⟩:= affair (A-B) (sub_ne_zero.mpr D); obtain ⟨g,t,G,H⟩:= regionP (v:=c/w/2) s (by positivity); refine ⟨g,t,G,?_⟩; intro N c' M X R U Y b p C q u L _ d Z x a e hZ f hu; have he:=H d hZ U Y x p hu; rw [f] at he; apply le_trans (plusNorm q M h b U w cP.le u he.2 he.1 F) (le_of_eq ?_); field_simp; ring -- tune
-- exported
variable (δ c v) -- tune explicit
structure Accord (P:Spin.Ready j a b l r) (δ c v:ℝ)(A B:Stamp)(t r' n g k:ℕ)(b':ℝ):Prop where
    toll {N:Side}{F:Core j a b l r N}(H: Honor P F δ)(η:ℝ)(x:Loft F δ c v η)(U Y J R:Finset (Per N)) : k≤N.val→ Ivory x R → Call R J A B (LastC x)→ Vent R J U t r' n→ Extend U Y g→ ∃ p∈ Y,∀ z:Site N, z 0=p→Tape.bias x (node z) ≤ -b'
include e d
lemma expect(t:ℕ) : ∃ r n f k:ℕ,∃ g:ℝ, 0<g∧Accord P δ c v A B t r n f k g:=by
 obtain ⟨a,W⟩:= receipt P e d δ; obtain ⟨R,n,k,u,x,l,T⟩:= broken h P.hP t; obtain ⟨m,f,g,G⟩:= earned A B D h x a; let α:= (1/4:ℝ)*m^2; refine ⟨R,n,f,k,α,(by unfold α; positivity),?_⟩; constructor; intro N F H η y U Y J R hz V q E hv; let C:=LastC y; let A:=Plus j F.M R C; let p:=pureB H y V; let W':= Tape.kiln H.1 c v η; have he:= G F.M J R U Y p hv q (last_sk y) W' y _ _ (W H η) (pureC H y V) -- tune Wf
 obtain ⟨⟨⟨a,b⟩,w⟩,L,K⟩: ∃ i:Single N, ht i∈Y∧ m<‖acts (star (BillLeg y)) (basisKet i)‖:=by by_contra! v; apply not_le.mpr (T hz R J U E _ p (tailB H y V)) (he v)
 refine ⟨a 0,L,fun z t'=>?_⟩; convert (lackFace y (guy z b w) g.le ?_) using 1; · unfold α; ring_nf
 change m≤swing (star _) z b w; rw [pureC H y V, stepShow _ z a t']; exact K.le.trans_eq (by rw [pureC H y V]; rfl); intro i k; exact hop_comm_star _ _ (shore _ k h p q)
end YM.CF.BProof.Bias
