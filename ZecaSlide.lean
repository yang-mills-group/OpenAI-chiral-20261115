import YM.SU5.FiniteGaugeData.Tower.BoxWorks
import YM.SU5.FiniteGaugeData.Tower.Sight
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 6000
set_option maxHeartbeats 350000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.SlabMark
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis Set
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
local notation "K"=>tent Y H
local notation "L₀"=>Λ.R.L.val
variable {i k:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}(V:Universal Y H i k I E)(s:ℕ)
variable {D:ℕ→Family (tent Y H)→Family (tent Y H)}{a b:ℕ→ℕ}(Q:Coherent (i:=i) (k:=k) (E:=E) Y H D a b)
variable (Qt : Clipped Y H (i∘a) (k∘b))
variable (j:Axis)(strict:Bool)(C:Arena Y H Q.circuit j 0 strict)
local notation "A"=> Ark.Ht Y H Q.circuit j 0 strict C
local notation "Γ" i:max=> Tower.Field Y H i j 0 strict
local notation "κ" s:max=>actor Y H s Q.circuit j 0 strict C
local notation "Ε"=>advance Y H V Q.circuit j 0 strict C
local notation "θt" s:max i:max=> MeshClock.whenly (timeMesh Λ) s i
local notation "B" s:max f:max h:max=>boxOp Y H V s Q Qt j strict C _ f h
variable (w u:ℕ)(f:Entry Y H s j strict w)(g:Entry Y H s j strict u)(hw:0 < w)(hu:0 < u)
local notation "U"=>relocate K
local notation "c"=>ruler (tent Y H).B



variable (g':Entry Y H s j strict w)(y:ℂ)
noncomputable def jamAdd: Entry Y H s j strict w := by
 refine ⟨f.val+g'.val, ?_⟩
 obtain ⟨S,t,h⟩:= f.property
 obtain ⟨T,z,e⟩:= g'.property
 refine ⟨S∪T,(t.mono Finset.subset_union_left).add
      (z.mono Finset.subset_union_right),fun x m=>?_⟩
 exact (Finset.mem_union.mp m).elim (h x) (e x)
noncomputable def jamScale: Entry Y H s j strict w := by
 -- Lean forget f g' if not in type? section variables in def captured? jamAdd too.
 refine ⟨y • f.val,?_⟩
 obtain ⟨S,t,h⟩:=f.property
 exact ⟨S,InTest.smul _ t,h⟩
include V C hw
local notation "F" z:max t:max p:max=> furnished Y H s Q j strict w z t p
lemma jam_add : B s (jamAdd Y H s j strict w f g') hw=B s f hw+B s g' hw:=by
 apply test_high Y H V s Q j strict C
 intro n d x
 rw [add_apply,snatch Y H V s Q Qt j strict C w _ hw d,
     snatch Y H V s Q Qt j strict C w _ hw d,
     snatch Y H V s Q Qt j strict C w _ hw d]
 change arrows Y H V Q.circuit j 0 strict C n _=
   arrows Y H V Q.circuit j 0 strict C n _+arrows Y H V Q.circuit j 0 strict C n _
 rw [← map_add]
 apply congrArg (_); apply Subtype.ext
 rw [slab_eq]
 change stream Y H D s (n-s) (f.val.val+g'.val.val) * _
    = ↑((slabT Y H n j strict _ (F f n d)) x)+
      ↑((slabT Y H n j strict _ (F g' n d)) x)
 rw [woven_add Y H Q.circuit _ _ (test_entry Y H s j strict f)
     (test_entry Y H s j strict g'), add_mul, slab_eq,slab_eq]; rfl
lemma jam_scale : B s (jamScale Y H s j strict w f y) hw=y • B s f hw:=by
 apply test_high Y H V s Q j strict C
 intro n d x
 rw [ContinuousLinearMap.smul_apply,snatch Y H V s Q Qt j strict C w _ hw d,
     snatch Y H V s Q Qt j strict C w _ hw d]
 change arrows Y H V Q.circuit j 0 strict C n _=
   y • arrows Y H V Q.circuit j 0 strict C n _
 rw [← map_smul]
 apply congrArg _; apply Subtype.ext
 rw [slab_eq]
 change stream Y H D s (n-s) (y • f.val.val) * _
    = y • ((↑((slabT Y H n j strict _ (F f n d)) x)):Family K)
 rw [woven_smul Y H Q.circuit _ _ (test_entry Y H s j strict f),
     smul_mul_assoc,slab_eq]; rfl

end YM.CF.Buffered.Afterglow.Tower.SlabMark
