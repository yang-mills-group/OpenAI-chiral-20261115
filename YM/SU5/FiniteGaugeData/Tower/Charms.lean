import YM.SU5.FiniteGaugeData.Tower.Frontage
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 6500
set_option maxHeartbeats 350000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.Vacancy
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark OS.Semigroup MeshClock Set
/-!
# Ergodic axis and order exchange for the graded systems

At limiting rung s, charges already identified. These compressed moments
are **unconditional** on restoration hypotheses. Uniform for number of
moments FIXED, via flow on actually bounded carriers (no distribution
smearing appearing at this estimate). Forthcoming challenge ensure continuity
in space and/or passage beyond separated reads for continuum x, this lemma
stays on grids. -/
variable {Λ:Preparation}{lp:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus lp))(H:Real.exp 1≤Λ.x)
local notation "K"=>tent Y H
variable {i k:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}(V:Universal Y H i k I E)(s:ℕ)
variable {D:ℕ→Family (tent Y H)→Family (tent Y H)}{a b:ℕ→ℕ}(Q:Coherent (i:=i) (k:=k) (E:=E) Y H D a b)(Qt:Clipped Y H (i∘a) (k∘b))
variable (j:Axis)(strict:Bool)(C:Arena Y H Q.circuit j 0 strict)
local notation "A" j:max c:max=>Ark.Ht Y H Q.circuit j 0 strict c
local notation "S₀" j:max c:max s:max=> office Y H V s Q j strict c -- tune strict
local notation "Ω" j:max C:max=>floorV Y H Q.circuit j 0 strict C
local notation "P₀" j:max c:max s:max=> Console.sky (S₀ j c s) (look j)
variable {S:Type*}[Fintype S](X:S→ observable (tent Y H) strict)
variable (j':Axis)(B:Arena Y H Q.circuit j' 0 strict)
variable (Y₁:∀i,Veranda Y H s j strict (X i))(Y₂:∀i,Veranda Y H s j' strict (X i))

-- ANY permutation on fixed-rung matrices. crucial using ALL planes.
private lemma another_order{I:Type*}(x:List I)(h:x.Nodup):∃f:I→ℕ,x.Pairwise (fun i j=>f i<f j):=by
 classical
 induction x with
 | nil=> exact ⟨fun _=>0,List.Pairwise.nil⟩
 | cons i x ih=>
    obtain ⟨h,p⟩:=List.nodup_cons.mp h
    obtain ⟨k,a⟩:=ih p
    let f(j:I):=if j=i then 0 else k j+1
    have he(j:I)(r:j∈x):f j=k j+1:=if_neg (show j≠i from fun e=>h (e ▸ r))
    refine ⟨f,List.pairwise_cons.mpr ⟨fun j m=>by rw [he _ m,show f i=0 from if_pos rfl]; omega,?_⟩⟩
    refine List.Pairwise.imp_of_mem ?_ a
    intro z i t b v; change f z < f i; rw [he z t, he i b]; exact Nat.add_lt_add_right v 1
lemma charms (L L':List S)(h:j≠j')(p:L.Nodup)(P:L.Perm L'):
 innerAth Y H V s Q Qt j strict C X Y₁ L=innerAth Y H V s Q Qt j' strict B X Y₂ L':=by
 have t:=p.perm P
 obtain ⟨q1,H1⟩:=another_order L p; obtain ⟨q2,H2⟩:=another_order L' t
 let q(i:S)(a:Axis):ℕ:=if a=j then q1 i else q2 i
 have h1 : L.Pairwise (fun i k=>q i j<q k j):=H1.imp (by simp [q])
 have h2:L'.Pairwise (fun i k=>q i j'<q k j'):=H2.imp (by simpa [q,Ne.symm h])
 refine tendsto_nhds_unique (f:=outerAth (E:=E) Y H s strict X q L) (consensus Y H V s Q Qt j strict C X Y₁ q L p h1) ?_
 apply (consensus Y H V s Q Qt j' strict B X Y₂ q L' t h2).congr
 intro i
 unfold outerAth; apply Average.eq_of; intro x
 rw [score_eq Y H V Q Qt j strict C X _ L' L P.symm]
lemma permutes(L L':List S)(p:L.Nodup)(P:L.Perm L')(Z:∀i,Veranda Y H s j strict (X i)):
 innerAth Y H V s Q Qt j strict C X Y₁ L=innerAth Y H V s Q Qt j strict C X Z L':=by
 obtain ⟨k,p'⟩:=exists_ne j
 let C':= Classical.choice (voyage_H Y H V Q.circuit k 0 strict)
 let V₁(i:S):=Classical.choice (anyporch Y H s k strict (X i))
 refine (charms Y H V s Q Qt j strict C X k C' Y₁ V₁ L L' p'.symm p P).trans ?_
 exact (charms Y H V s Q Qt j strict C X k C' Z V₁ L' L' p'.symm (p.perm P) (List.Perm.refl ..)).symm
end YM.CF.Buffered.Afterglow.Tower.Vacancy
#check List.Pairwise.imp_of_mem
#print axioms YM.CF.Buffered.Afterglow.Tower.Vacancy.charms
