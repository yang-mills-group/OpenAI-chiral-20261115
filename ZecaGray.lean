import ZecaPith
import YM.SU5.Six.MSplit
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 320000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
namespace Spine
variable (P: Spine) (j:Axis) (x:P.Spectrum0 j)
open Aria Set TopologicalSpace Metric

open scoped TensorProduct
open Six
local notation "κ"=> P.calibration
local notation "R"=> ruler P.par.block
local notation "H"=> P.large
local notation "Y"=> P.run
local notation "Φ"=> P.stateSpace j x
local notation "X"=> P.PortionHil j x
local notation "σ"=> P.projection.clipped
local notation "C₀"=> P.room j
local notation "R₀"=> P.history
local notation "J"=> P.Slabs j
local notation "T"=> P.Test


variable (s w:ℕ)


variable (pw:0<w)
local notation "A" => P.chairs j x s w pw
local notation "B" => P.pith j x s w pw

private lemma gone {U:Type} [AddCommGroup U] [Module ℂ U]{u:U} (z:ℂ)(p:z≠1)(e:u=z•u):u=0:=
  have h:(1-z)•u=0 := by rw [sub_smul,one_smul,← e,sub_self]
  (smul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr p.symm)


private lemma mul0 {U:Hilbert} (F:U.Op):TensorProduct.mapL F (0:U.Op)=0:=by
 
 apply ContinuousLinearMap.ext
 intro z
 change TensorProduct.mapL F (0:U.Op) z=0
 induction z using TensorProduct.induction_on with
 | zero=>exact map_zero _
 | tmul x y=>exact TensorProduct.tmul_zero ..
 | add a b p q=> rw [map_add,p,q,zero_add]
/-- product vanishes on a seed-charge: cost at removal aperture
of matter factor alone gives nontrivial phase. Exact. -/
lemma nutshell (Q:Bool)(S L D:Finset Cover)(p:S∪L⊆D)(q:Disjoint S L)
  (r:Between κ j 0 (ruler P.par.block*w) D)(f:P.Test)
  (v:f.val∈ DressedPair κ Q S L D) : B f=0:=by
 have he:DressedPair κ Q S L D≤
      (LinearMap.ker (B)).map (screenHall κ).val.toLinearMap:=by
    refine Submodule.span_le.mpr ?_
    rintro z ⟨u,t,y,h,rfl⟩
    let a:T:=⟨scalar κ u,broadCompile κ D (.seed t)⟩

    have hx: InTest κ true D false y:= (raw_test κ Q S L h).1.mono p
    let b:T:=⟨y,broadCompile κ D hx⟩
    let c:Cover→SU.E:= fun i=> if i∈L then SU.central else 1
    let z:=phaseName Q
    have hb:b∈bay κ D true:=hx
    have h₁:A b = A (z•b):=P.chairs_paint j x s w pw D r b (z•b) hb 
          ((bay κ D true).smul_mem hb _) c
          (pocket_charge κ Q S L D c p (fun _ x=> if_neg fun u=>Finset.disjoint_left.mp q x u)
             (fun _ x=>if_pos x) h)
    rw [map_smul] at h₁
    have h₀:A b=0:=gone z (pname_ne Q) h₁
    refine ⟨a*b,LinearMap.mem_ker.mpr ?_,rfl⟩
    rw [P.pithFactors j x s w pw a b ⟨D,u,t,rfl⟩ (raw_test κ Q S L h).2,h₀]
    exact mul0 (U:=X) _
 obtain ⟨u,i,o⟩:=he v
 exact (congrArg (B) (Subtype.ext o :u=f)).symm.trans i

/-- Split nulls the *slab* on all vectors, not just vacuum or when the
other leg transforms trivially. -/
lemma shells (Q:Bool)(D:Finset Cover)(r:Between κ j 0 (ruler P.par.block*w) D)
 (f:T)(v:f∈P.sensing D s Q): B f=0:=by
 have h:P.sensing D s Q ≤ LinearMap.ker B:= by
    refine Submodule.span_le.mpr ?_
    rintro g ⟨U,V,L,p,u,t,e,_⟩
    exact P.nutshell j x s w pw _ _ _ _ p (P.pin_disjoint _ _ _ t)
           (fun i h=> r i (u h)) g e
 exact h v

lemma shell_brief (χ:P.Test→ₗ[ℂ]ℂ)
 (dec:Six.Comparison P.calibration (P.singleState j s x) χ) 
 (f:T)(h:P.straight j s w f):
 inner ℂ (P.Pome j x) (B f (P.Pome j x))= χ f:=by
 obtain ⟨I,d,a,b,rfl,v⟩:=P.straight_exhaust j s w f h
 rw [map_sum,map_sum,_root_.sum_apply,inner_sum]
 refine sum_congr rfl fun i _=>?_
 specialize v i
 rw [dec.factors _ _ v.2.2.1 v.2.2.2,dec.link _ v.2.2.1,dec.matter _ v.2.2.2,
     P.pithFactors j x s w pw _ _ v.2.2.1 v.2.2.2]
 exact congrArg₂ (·*·) (P.chairs_pearl j x s w pw _ v.1) (P.chairs_pearl j x s w pw _ v.2.1)
