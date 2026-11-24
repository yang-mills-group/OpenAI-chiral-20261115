import YM.SU5.Relativistic.FermiStep
set_option autoImplicit false
set_option quotPrecheck false
set_option synthInstance.maxSize 27000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.Reconstruction.FermionSlab
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Fock
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal Classical InnerProductSpace
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat SlabMark Vacancy
variable {Λ:Preparation}{l:ℕ}
lemma airyAbove (S:Finset Cover)(a:Axis)(R:ℕ) : ∀ᶠ z:ℤ in atTop,Tower.separated R (reflectedBox a z S) S:=by
 obtain ⟨n,h⟩:=Tower.sizes S; obtain ⟨t,q⟩:=h a
 filter_upwards [eventually_gt_atTop (t+n+(R:ℤ))] with z h x p y u g
 obtain ⟨i,e,hx⟩:= reflect_stays a z S p
 obtain ⟨m,J⟩:= box_test.mp g
 specialize J a; rw [Pi.sub_apply,hx a,if_pos rfl] at J
 have hp:= q _ e; have hu:= q _ u; omega
lemma airing (S:Finset Cover)(a:Axis): ∃ z:ℤ, Detached Λ l (reflectedBox a z S) S∧ Detached Λ l (reflectedBox a ((Λ.R.L.val)*z) (wingspan Λ l S)) (wingspan Λ l S):=by
 apply Eventually.exists (f:=atTop)
 apply (airyAbove S a _).and ((Tendsto.const_mul_atTop' (f:=id) (show 0<(Λ.R.L.val:ℤ) from by positivity) tendsto_id).eventually (airyAbove (wingspan Λ l S) a _)) -- test

lemma sectorsDis {K:Calibration}{n:Side}{S T:Finset Cover}(h:Disjoint S T)(p:Hosp (S∪T) (K.c n)) : Disjoint (Satin.region S (K.c n)) (Satin.region T (K.c n)) ∧ Disjoint (modesIn (K.c n) (Satin.region S (K.c n))) (modesIn (K.c n) (Satin.region T (K.c n))):=by
 have he:Disjoint (Satin.region S (K.c n)) (Satin.region T (K.c n)):=by
    apply Finset.disjoint_left.mpr; intro i a b; obtain ⟨x,t,rfl⟩:= mem_image.mp a; obtain ⟨y,v,g⟩:= mem_image.mp b
    obtain rfl:= p.seat_ (mem_union_left _ t) (mem_union_right _ v) g.symm; exact Finset.disjoint_left.mp h t v
 exact ⟨he,Finset.disjoint_left.mpr fun i u=> fun t=> Finset.disjoint_left.mp he ((modes_at ..).1 u) ((modes_at ..).1 t)⟩

-- construct W sutured; no link/cue condition conflicts at fronts
section
variable {N:Side}{S T:Support (More N)}
private def fixed (S : Support (More N))(x y:Pane N) : Pane N:= fun e=> if e.1∈ S then x e else y e
def setTwo (S:Support (More N))(x y:Fields N): Fields N:=(fixed S x.1 y.1,fixed S x.2 y.2)
lemma seamTwo {A B:Mark N}(b c:Bool)(p:Disjoint S T)(h:AtSupport b S A) (t:AtSupport c T B)(x y:Fields N) : (A*B) (setTwo S x y)= A x * B y:=by
 let z:=setTwo S x y; change A z*B z=A x*B y
 refine congrArg₂ (HMul.hMul (γ:=FC (Single N))) (h.dep z x (fun i g _=> if_pos g) (fun i g _=> if_pos g)) (t.dep z y ?_ ?_) <;> exact (fun i g _=> if_neg (Finset.disjoint_left.mp p.symm g))
end
lemma normaM (a:Axis)(z:ℤ){K:Calibration}{f:Family K}(n:Side)(x:Fields (K.c n)):‖mirror K a z f n (reflFields a z x)‖ = ‖f n x‖:= by unfold mirror reflMark; rw [reflFields_inv, theta,twist_norm,norm_cc]
end YM.CF.Buffered.Afterglow.Tower.Reconstruction.FermionSlab
