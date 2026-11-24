import YM.SU5.Aria.Studio
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 250000
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
variable {a j:Axis}{P: Spine} (x:P.Spectrum0 a)
open Aria Set TopologicalSpace Metric Casting
local notation "χ[" k "]"=> P.advocate a x k
local notation "H[" k "]"=> P.ManyF k χ[k]
local notation "Ω[" k "]"=> P.heaven k χ[k]
local notation "Ψ[" k "]"=> P.seasons k χ[k]
local notation "ω[" k "]"=> P.colorZero k χ[k]
local notation "W[" k "]"=>P.cartage k χ[k]
local notation "E[" k "]"=>(Ψ[k]).E
local notation "V[" k "]"=>P.tableau k χ[k]
variable (B D:P.Apron) (k:Axis)
def flashY:= P.wealth k (P.advocate a x k) (B.engine P k χ[k] ω[k])
def glareY := (star (P.tableau k χ[k] 0 (B.engine P k χ[k]))) Ω[k]
-- BUY cross-axis Laplace formula on selected translation-continuum sector
abbrev usher {A:Type*}(x y:A): Bool→A
 | false=>x
 | true=>y
local notation "L"=> ([false,true]: List Bool)
local notation "U" => usher B D
local notation "q[" r "]"=> usher (0:Vantage) r
local notation "d[" k "]"=> (B.realWidth P k + D.realWidth P k)
local notation "M[" r "]"=> P.commonWell a x U q[r] L
variable (r:Vantage)
lemma memorial_two : P.memorial k χ[k] U L q[r]= inner ℂ (glareY x B k) (E[k] ((r k-d[k]).toNNReal) (W[k] r (flashY x D k))):=by
 let A':=(V[k] 0 (B.engine P k χ[k])); let F':= V[k] r (D.engine P k χ[k])
 unfold memorial; rw [← Aria.rector_view (Ψ[k]) Ω[k] _ _ _ (P.heaven_hot k χ[k]) 0]
 let w:= B.realWidth P k; let u:=D.realWidth P k; change inner ℂ Ω[k] (E[k] _ (A' (E[k] ((r k-u - ((0:Vantage) k+w)).toNNReal) (F' Ω[k]))))= inner ℂ (A'.adjoint Ω[k]) _
 rw [←OS.Semigroup.swing (Ψ[k]), P.heaven_hot,show r k-u-((0:Vantage) k+w)=r k-(w+u) from (by rw [Pi.zero_apply]; ring)] -- check
 unfold F'; rw [P.tableMaps, ContinuousLinearMap.adjoint_inner_left] -- syntax direction check
 rfl
lemma avail_cross (J:P.Ellis a x)(hk:d[k]<r k): M[r]=inner ℂ (glareY x B k) (E[k] ((r k-d[k]).toNNReal) (W[k] r (flashY x D k))):=by
 have he:P.Turnstile k U L q[r]:=List.pairwise_pair.mpr (show ((0:Vantage) k + B.realWidth P k) < r k - D.realWidth P k from by rw [Pi.zero_apply,zero_add]; linarith)
 exact (P.common_cult a x U q[r] L J (List.Perm.refl _) he).trans (memorial_two x B D k r)
lemma flashY_glare : glareY x (B.kiss P k) k = flashY x B k:=by
 unfold glareY flashY
 have he:mirrorΩ k (0:Vantage)=0:=by funext i; by_cases p:i=k<;>simp [mirrorΩ,p]
 rw [← he] -- oops rewrites other 0
 rw [← P.lives_twin,star_star,P.tableMaps,P.cart_zero]; rfl
variable (t p:ℝ≥0)
local notation "τ" q:max => Real.toNNReal q
local notation "f₁" k:max=> flashY x B k
local notation "f₂" k:max=> flashY x D k
variable (j) (g₁:Vantage)
private lemma aisleP(x y:ℝ): aislePt k (x+y)= aislePt k x+aislePt k y:=by funext i; by_cases h:i=k<;>simp [aislePt,h]
lemma passP (x':ℝ)(u v:Vantage)(g:u= v+ aislePt k x') : W[k] u=W[k] v:=by rw [g,P.cart_paves,P.cart_aisle]; rfl
lemma of_slideP (u v:Vantage)(g:∀ i:Axis,i≠k→ u i=v i) : W[k] u=W[k] v := passP x k (u k-v k) u v (by
  funext i; by_cases h:i=k
  · subst i; simp [aislePt] <;> abel
  simp [aislePt,h,g i h])
lemma shiftP (u v:Vantage)(g:∀ i:Axis,i≠k→ u i=v i) : (E[k] t).comp (W[k] u)=(W[k] v).comp (E[k] t):=by rw [of_slideP x k u v g]; ext z; exact warm_drive ..
variable(J:P.Ellis a x)(h:k≠j)
local notation "B₁"=> B.kiss P j
-- daylight j expected heated with any h,t; kˆ from D1 & D2. rigid exact
abbrev roseTail (r:Vantage)(t:ℝ≥0):= update r j ((B.realWidth P j + D.realWidth P j)+(t:ℝ))
-- Function.update disambig. note h vs hh
include J h
lemma flash_tail (hk:d[k]<r k) (ht:0<t): inner ℂ (f₁ j) (E[j] t (W[j] r (f₂ j)))=inner ℂ (glareY x (B.kiss P j) k) (E[k] (τ (r k-d[k])) (W[k] (roseTail j B D r t) (f₂ k))):=by
 let u:= roseTail j B D r t
 let z:Bool→P.Apron:= usher (B.kiss P j) D
 have h₁ : (B.kiss P j).realWidth P j=B.realWidth P j:= rfl; have h₂ : (B.kiss P j).realWidth P k=B.realWidth P k:= rfl
 have ht' (h:ℝ≥0) (v:ℝ): τ (v+(h:ℝ)-v)=h:=by rw [add_comm v,add_sub_cancel_right,Real.toNNReal_coe]
 have he:u j=d[j]+(t:ℝ):= update_self ..; have hs:u k=r k:= update_of_ne h ..; have hv:0<(t:ℝ):= ht
 have H:= avail_cross x B₁ D j u J (by rw [h₁,he]; linarith); have P₁:= avail_cross x B₁ D k u J (by rw [h₂,hs]; exact hk)
 rw [h₁,he,ht',of_slideP x j u r (fun i g=> update_of_ne g ..), flashY_glare] at H; rw [h₂,hs] at P₁; exact H.symm.trans P₁
-- make dense for witnesses, bankview is by Studio; U center thermal still span
omit J h
abbrev Flicker (P:Spine):= P.Apron × {r:ℝ≥0 //0<r}
def specY (F:Flicker P):= E[k] F.2.val (flashY x F.1 k)
lemma flash_grant : Dense (Submodule.span ℂ (Set.range (specY x k)): Set H[k]):=by
 let Z:= P.wealth k χ[k]; let A:= P.ColorHil k χ[k]; let VV:=Submodule.span ℂ (Set.range (specY x k)); let V:= VV.comap Z.toLinearMap
 have he:(Submodule.span ℂ (Set.range (P.oneSide k χ[k])))≤ V:= Submodule.span_le.mpr (by
     rintro v ⟨⟨s,u,p⟩,rfl⟩; obtain ⟨n,t,_,ht,Q,a₀,H⟩:=P.wasTrue k χ[k] s u p; rw [P.entersAt] at H; exact (show Z (P.viewF k χ[k] s p)∈VV from Submodule.subset_span (show _∈Set.range (specY x k) from ⟨(Q,⟨t,ht⟩),H.symm⟩)))
 intro v; exact P.rewarded k χ[k] v ▸ (show Z (P.enter k χ[k] v)∈closure (VV:Set H[k]) from MapsTo.closure (f:=((Z):A→H[k])) (s:=(V:Set A)) (fun i e=>e) Z.continuous ((P.partner_dense k χ[k]).mono (SetLike.coe_mono he) (P.enter k χ[k] v)))
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.flash_tail
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.flash_grant
