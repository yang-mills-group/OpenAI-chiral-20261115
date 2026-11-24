import YM.SU5.Reconstruction.LinkMeasures.Preferred
import YM.SU5.Reconstruction.LinkMeasures.MorningRoom
set_option autoImplicit false
set_option synthInstance.maxSize 30000
set_option maxRecDepth 6000
set_option maxHeartbeats 400000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Satori
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis Tapestry
open Set
variable (S:Finset Cover)(K:Calibration)
local notation "W" => Swatch S
local notation "X" => ScoreBook S
-- assembling the literal algebra. No physical test requested under widened support to test closure.
lemma lecturer (f:W)(h:f∈ literal S) (i:Evens S) : ∃ g∈ glancing S, ∀ y:ScoreBook S,(accession S (f i)).val y = g y :=by obtain ⟨g,v,t⟩:= (show ∃ g∈ glancing S,mentor S g=f i from h i (Set.mem_univ _)); rw [←t]; exact ⟨g,v,mentor_read S g⟩
lemma literal_from (f:W) (p:∀ i:Evens S, ∃ g∈ glancing S, ∀ y:ScoreBook S,(accession S (f i)).val y=g y): f∈ literal S:=by intro i _; obtain ⟨g,v,t⟩:=p i; exact ⟨g,v,(seatFaith S).symm.injective (Subtype.ext (show (accession S (mentor S g)).val=(accession S (f i)).val from funext fun y=> (mentor_read S g y).trans (t y).symm))⟩

lemma almond: colorless K S∈ literal S:=by
 obtain ⟨m,p⟩:= (Buffered.separates K S).exists; have h: Hosp S (K.c m):=⟨p⟩
 apply literal_from; intro i; refine ⟨algebraMap ℂ _ (eye S K m h i 1),(show _ ∈ sealA S from (sealA S).algebraMap_mem _),fun y=>?_⟩
 rw [←head_price S K m h,pointOp, ←appearRender, bareUnit]; rfl
lemma teamed (f F:W)(x:X)(m:Side): pointOp S K m (brocade K S f F) x=pointOp S K m f x * pointOp S K m F x:=by unfold pointOp; rw [←appearRender, ←appearRender, ←appearRender,bareMult]; rfl
lemma amult(f F:W)(a:f∈ literal S)(b:F∈ literal S) : brocade K S f F∈ literal S:=by
 obtain ⟨m,p⟩:= (Buffered.separates K S).exists; let M:=K.c m; have p':Hosp S (K.c m):= ⟨p⟩
 choose v w t using lecturer S f a; choose V q wRe using lecturer S F b
 apply literal_from; intro i
 let x(j:Evens S):= spool M (tagWord S j.val); let τ(j k:Evens S):= eye S K m p' i (x j*x k); let y(j k:Evens S):= (v j)*(V k)
 refine ⟨∑ j:Evens S, ∑ k:Evens S, (τ j k) • y j k,(glancing S).sum_mem (fun j _=> (glancing S).sum_mem (fun k _=> (glancing S).smul_mem _ (show _∈sealA S from (sealA S).mul_mem (w j) (q k)))), fun z=>?_⟩
 rw [←head_price S K m p',teamed,paid_as S K m p',paid_as S K m p']; simp_rw [t,wRe, sum_mul, mul_sum, map_sum,ContinuousMap.sum_apply,ContinuousMap.smul_apply]; refine sum_congr rfl fun j _=> sum_congr rfl fun k _=>?_ ; rw [Algebra.smul_mul_assoc, Algebra.mul_smul_comm,map_smul,map_smul]; change v j z * (V k z * τ j k)= τ j k*(v j z * V k z); ring
-- payment is as a *literal subalgebra of determining polynomials*, here on ONE level and actual gauge AND matter there. This won't have to be the family that advances, which may require remodelling a singular link kernel.
noncomputable def Polished :Subalgebra ℂ (Dome K):= by
 let T:= (literal S).map (badge K S); exact {
 carrier:= T
 one_mem':=⟨_,almond S K,laureled K S⟩
 zero_mem':= T.zero_mem
 add_mem':= fun a b=> T.add_mem a b
 mul_mem':= fun {x y} u v=> by
    obtain ⟨F,a,rfl⟩:=u; obtain ⟨Z,b,rfl⟩:= v; exact ⟨_,amult S K F Z a b,badge_brocade K S F Z⟩
 algebraMap_mem':= fun z=>by rw [Algebra.algebraMap_eq_smul_one]; exact T.smul_mem _ (show 1∈T from ⟨_,almond S K,laureled K S⟩)
 }
noncomputable def labOfGauge : Subalgebra ℂ (Dome K):=Polished S K ⊓ enclave K
lemma pol_here (x: Dome K): x∈Polished S K ↔∃ v∈ literal S, badge K S v=x:= Iff.rfl
lemma gaugeHere (x:Dome K): x∈labOfGauge S K ↔ (∃ v∈ literal S,badge K S v=x)∧ Neutral K x.val:=Iff.rfl
lemma pol_bay : Polished S K ≤ bay K S true:=by intro x hx; obtain ⟨v,h,rfl⟩:= (pol_here S K x).1 hx; exact locatesBadge ..
end YM.CF.Buffered.Afterglow.Satori
#print axioms YM.CF.Buffered.Afterglow.Satori.labOfGauge
