import YM.CF.BProof.Double.Batch
/-! issue kernel, before applying B-PfC on actual symbols. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Double
open Function Filter Fock Finset Branch Stint Align Wick
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {I D G Y:Type}[Fintype I][DecidableEq I][Nonempty I] [Fintype Y][DecidableEq Y]{b:Stage Y I D G}
variable [TopologicalSpace D] {c r L:ℝ}
abbrev billC(p q r s:Pay) := ((p.lodge q).lodge (r.lodge s)).wage 2
abbrev slotL(p q:Pay):= (Pay.simple.add (p.add q)).wage ‖(1/2:ℂ)‖
def cern(A P Q C:Op I): M I:= (oblique A P Q C)ᵀ * slip I
lemma transE {F:D→Op I}{p:Pay}{s t:Tag b}(h:Earn p s t F) : Earn p t.reverseV s.reverseV (fun i=> (F i)ᵀ):=by simpa only [←show ∀ A:Op I,cc (star A)=Aᵀ from fun A=>by rw [cc,star_star]] using h.adj.ccUp -- tune
lemma pullF (hp:0<c)(ht:r<1)(x:0≤L)(a p q u:Pay) : ∃ X:Pay,∀ {I D G Y:Type}[Fintype I][DecidableEq I][Nonempty I] [Fintype Y][DecidableEq Y][TopologicalSpace D]{b:Stage Y I D G}{t:Tag b}{A P Q C:D→Op I}, Capacity b L→ Earn a t t A → Earn p t t P→ Earn q t t Q → Earn u t t.reverseV C→ (∀ i, Double.Deck (A i) (P i) (Q i) (C i) c r) → Earn X (dye t).reverseV (dye t) (fun i=>cern (A i) (P i) (Q i) (C i)):=by
 let S:= Pay.simple; let T:=billC a a a (S.add a); let z:= slotL p q; let X:= billC (q.add z) (z.mul u) (u.mul z) (p.add z); obtain ⟨Z,U'⟩:= inverseCost (margin_pos hp ht) (add_nonneg x x) (T.add X); refine ⟨(T.mul Z).mul (S.wage 2),?_⟩; intro I D G Y _ _ _ _ _ _ b t A P Q C f h l' q' g v
 let V:=t.reverseV; let U:= dye t; have ht:Earn T U U (fun i=>penR (A i)):= billing h (Earn.free a) (Earn.free a) ((Earn.one V).minus h.ccUp)
 have he:Earn z t t (fun i=> camp (P i) (Q i)):=((Earn.one t).minus (l'.plus q')).scalar (c:=(1/2:ℂ)) le_rfl
 have hw(i:D):cc (camp (P i) (Q i))=camp (P i) (Q i):=(v i).wallD; have hf:Earn z V V (fun i=> camp (P i) (Q i)):=by simpa only [hw] using he.ccUp
 have hl:Earn u V t (fun i=>cc (C i)):=by simpa only [restore t] using g.ccUp
 have hm: Earn X U U (fun i=> penL (P i) (Q i) (C i)):= billing (q'.plus he) (he.times hl.adj) (hl.times he) ((show Earn p V V P from ?_).plus hf); swap; · convert l'.ccUp using 1; ext1 i; exact (v i).markA.symm -- tune
 have hk:Earn (S.wage 2) U.reverseV U (fun _=>slip I):=by unfold U; rw [← elevate]; exact family (Earn.free S) (Earn.one V) (Earn.one t) (Earn.free S)
 exact (transE (ht.times (U' (doubled f x) (ht.plus hm) (fun i=> (v i).reserve)))).times hk
end YM.CF.BProof.Double
