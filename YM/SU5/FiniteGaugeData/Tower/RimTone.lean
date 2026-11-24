import YM.SU5.FiniteGaugeData.Tower.CapStone
/-!
# Simultaneous clustered moments on joint projected algebras (all j)

Put all at same higher and higher resolution r then take Consensus. Keeping
r fixed in Consensus is enough for its neighborhood, allowing r→∞ afterwards
within the SAME limiting circle and joint origin. No continuity of limits of
boost reps. These moments suffice for determining the compressed algebra,
unlike convergence of one-point tests at a distributional pose; still
need passage to spacetime continuum, distributions, Lorentz etc etc.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 380000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.Vacancy
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark OS.Semigroup MeshClock Set
variable {Λ:Preparation}{lp:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus lp))(H:Real.exp 1≤Λ.x)
local notation "K"=>tent Y H
local notation "L₀"=>Λ.R.L.val
variable {i k:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}(V:Universal Y H i k I E)(s:ℕ)
variable {D:ℕ→Family (tent Y H)→Family (tent Y H)}{a b:ℕ→ℕ}(Q:Coherent (i:=i) (k:=k) (E:=E) Y H D a b)(Qt:Clipped Y H (i∘a) (k∘b))
variable (j:Axis)(strict:Bool)(C:Arena Y H Q.circuit j 0 strict)
local notation "A"=>Ark.Ht Y H Q.circuit j 0 strict C
local notation "D₀" i:max c:max=> Aurora Y H V Q i strict c
local notation "S₀" s:max=> office Y H V s Q j strict C
local notation "P₀" s:max=> Console.sky (S₀ s) (look j)
local notation "π"=> (D₀ j C).orthogonalProjectionOnto
local notation "relic"=> (D₀ j C).subtypeL
local notation "Ω"=>floorV Y H Q.circuit j 0 strict C
local notation "F₀" j:max c:max=>seat0 Y H V Q j strict c
abbrev Beacon(Kx: Calibration)(b:Bool):=ℕ×observable Kx b
variable {S:Type*}[Fintype S](X:S→ Beacon (tent Y H) strict)(Z:∀i,Veranda Y H (X i).1 j strict (X i).2)
local notation "B₀" s:max X:max=>Veranda.placed Y H V s Q Qt j strict C X
local notation "N" s:max=>cap Y H V s Q Qt j strict C
local notation "Q₀" i:max=> (N (X i).1) (X i).2
noncomputable def heavies (t:List S):ℂ:=
 inner ℂ (F₀ j C) (Average.ordered (H:= {space:= (D₀ j C)}) t (fun i=>Q₀ i) (F₀ j C))
lemma spotted (p:List S):
 heavies Y H V Q Qt j strict C X p= inner ℂ Ω (Average.ordered (H:=A) p (fun i=> (D₀ j C).starProjection.comp (B₀ (X i).1 (Z i))) Ω):=by
 set H':Hilbert:={space:=(D₀ j C)}
 let s (i:S):=Q₀ i
 let a(i:S):= (D₀ j C).starProjection.comp (B₀ (X i).1 (Z i))
 have he(p: List S)(x:H'): relic (Average.ordered (H:=H') p s x)=Average.ordered p a (relic x):=by
   induction p generalizing x with
   | nil=>rfl
   | cons i u ih=>
      rw [Average.orderly,Average.orderly,← ih]; unfold s; rw [onAny _ _ V _ Q Qt j strict C (Z i)]; rfl -- tune
 change inner ℂ (F₀ j C) (Average.ordered (H:=H') p s (F₀ j C)) = _
 change inner ℂ Ω (relic (Average.ordered (H:=H') p s (F₀ j C))) = _
 rw [he]; rfl

-- use continuity both, no projection convergence in op norm needed
private lemma many_back(p:List S)(u:S→ (A).Op): -- notation
 Tendsto (fun r=>Average.ordered p (fun i => (P₀ r).comp (u i)) Ω) atTop (𝓝 (Average.ordered (H:=A) p (fun i => (D₀ j C).starProjection.comp (u i)) Ω)):=by
 induction p with
 | nil=> exact tendsto_const_nhds
 | cons i p h=>
    simp_rw [Average.orderly,ContinuousLinearMap.comp_apply]
    let Z:=Average.ordered (H:=A) p (fun i=>(D₀ j C).starProjection.comp (u i)) Ω
    apply Console.lagZ (S₀ 0) (b:=1) (D:=fun r=>P₀ r)
    · intro i; rw [← names]; apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one; intro v; rw [one_mul]; exact (Conserves Y H V i Q j strict C).norm_starProjection_apply_le _
    · exact ((u i).continuous.continuousAt (x:=Z)).tendsto.comp h
    exact strands ..

lemma between_axes (a:Axis)(B:Arena Y H Q.circuit a 0 strict)(p:j ≠ a)(t t':List S)(e:t.Nodup)(g:t.Perm t'):
 heavies Y H V Q Qt j strict C X t=heavies Y H V Q Qt a strict B X t' :=by
 let V' (n:ℕ)(i:S):= upward Y H Q strict (X i).2 (X i).1 (n-(X i).1)
 let Z(i):=Classical.choice (anyporch Y H (X i).1 j strict (X i).2)
 let T0 (i:S):=Classical.choice (anyporch Y H (X i).1 a strict (X i).2)
 let U:= Finset.sup (Finset.univ:Finset S) fun i=>(X i).1
 let u i:=B₀ (X i).1 (Z i)
 have hx(i:S):(X i).1≤ U:=Finset.le_sup (f:=fun i=>(X i).1) (Finset.mem_univ i)
 rw [spotted Y H V Q Qt j strict C X Z,spotted Y H V Q Qt a strict B X T0]
 refine tendsto_nhds_unique_of_eventuallyEq (l:=atTop (α:=ℕ)) -- check
    (f:=fun n=> inner ℂ Ω (Average.ordered (H:=A) t (fun i=>(P₀ n).comp (B₀ (X i).1 (Z i))) Ω))
    (g:=fun n=> inner ℂ (floorV Y H Q.circuit a 0 strict B) (Average.ordered (H:=Ark.Ht Y H Q.circuit a 0 strict B) t' (fun i=>(Console.sky (office Y H V n Q a strict B) (look a)).comp (Veranda.placed Y H V (X i).1 Q Qt a strict B (T0 i))) (floorV Y H Q.circuit a 0 strict B)))
    (tendsto_const_nhds.inner (many_back Y H V Q j strict C t _)) (tendsto_const_nhds.inner (many_back Y H V Q a strict B t' _)) ?_
 filter_upwards [eventually_ge_atTop U] with n hn
 let z i:= addLevel Y H V (X i).1 Q j strict (Z i) n (le_trans (hx i) hn); let r i:= addLevel Y H V (X i).1 Q a strict (T0 i) n (le_trans (hx i) hn)
 have ht:=charms Y H V n Q Qt j strict C (V' n) a B z r t t' p e g
 convert ht using 1
 · unfold innerAth z; simp_rw [←allLevels Y H V _ Q Qt j strict C] -- implicit z unfold
 · unfold innerAth r; simp_rw [←allLevels Y H V _ Q Qt a strict B]
lemma any_order (t v:List S)(h:t.Nodup)(p:t.Perm v): heavies Y H V Q Qt j strict C X t=heavies Y H V Q Qt j strict C X v:=by
 obtain ⟨a,h'⟩:=exists_ne j
 let B:=Classical.choice (voyage_H Y H V Q.circuit a 0 strict)
 exact (between_axes Y H V Q Qt j strict C X a B h'.symm t v h p).trans (between_axes Y H V Q Qt j strict C X a B h'.symm v v (h.perm p) (List.Perm.refl ..)).symm

end YM.CF.Buffered.Afterglow.Tower.Vacancy
#print axioms YM.CF.Buffered.Afterglow.Tower.Vacancy.any_order
