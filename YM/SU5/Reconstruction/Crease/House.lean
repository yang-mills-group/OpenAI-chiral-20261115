import YM.SU5.Reconstruction.Crease.Foothold
import YM.SU5.Reconstruction.Crease.Proscenium
/-!
# Audited rank receipt. How to read & merge into Tomita graph identity for Wedge
-/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.BridgeClub
open Function Set Filter MeasureTheory Spectral Analysis Metric ContinuousLinearMap Picket CrossedFrame
open scoped BigOperators Topology InnerProductSpace ComplexOrder
variable {H K D:Hilbert}(C:Clasp K H D) (J:Flash H) (M:Net H)(Ω:H)(Γ:Set H.Op)
local notation "P" => C.plume
local notation "R" => C.shadow
local notation "δ" => J.f
-- using Γ programs pinned. Rank is density of these sums, not assuming complete P-space clocks.
abbrev label (A : H.Op):= A Ω+ J.f (star A Ω)
def Rank := Dense (Submodule.span ℂ (label J Ω '' Γ):Set H)
structure Club :Prop where
 pin : Γ ⊆ (M:Set H.Op)
 covers (x:H.Op): x∈ Γ→ star x∈ Γ
 pole (x:H.Op)(p:x∈ Γ) : P (J.f (star x Ω))=R (x Ω)
 reflect (x:H.Op)(p:x∈M) : J.shade x ∈ M.commutant
 opp : J.f Ω=Ω
 rank: Rank J Ω Γ
variable {C J M Ω Γ}(h:Club C J M Ω Γ)
namespace Club
include h
lemma pose (x:H.Op)(e:x∈Γ) : P (label J Ω x)=x Ω:= (C.formulates (x Ω) _ (h.pole x e)).1.symm
lemma rePose (x:H.Op)(e:x∈Γ) : R (label J Ω x)= J.f (star x Ω):=(C.formulates (x Ω) _ (h.pole x e)).2.symm
lemma economize (S:Set H) (p:IsClosed S) (e:∀ x∈Γ,label J Ω x∈ S)(z:(0:H)∈S)(u:∀ x∈S,∀ y∈ S,(x:H)+y∈S)(k:∀ x∈S,∀ s:ℂ,s • (x:H)∈S)(x:H) : x∈ S:= by
   let T:Submodule ℂ H:={carrier:=S,zero_mem':=z,add_mem':=fun {x y} p q=> u x p y q,smul_mem':=fun r x y => k x y r} -- implicit
   have he : Submodule.span ℂ (label J Ω '' Γ) ≤ T:=Submodule.span_le.mpr (by rintro _ ⟨x,v,rfl⟩; exact e x v)
   exact closure_minimal (fun _ x=>he x) p (h.rank x)
lemma phonon (x:H): P (J.f x)= J.f (R x):= by
 let A:H→L⋆[ℂ] H:= C.plume.comp J.f; let B:H→L⋆[ℂ]H:= J.f.comp R
 have he (t:H.Op): label J Ω (star t)=J.f (label J Ω t):= by rw [label,label,map_add,J.twice,star_star,add_comm]
 -- sign: P J label = star tΩ=J R label
 apply h.economize ({x:H| A x=B x}) (isClosed_eq A.continuous B.continuous) _ _ _ _ x
 · intro t p; change P (δ _)= δ (R _); rw [← he,h.rePose t p,h.pose _ (h.covers t p),J.twice]
 · change A 0=B 0; simp
 · exact fun x (hx:A x=B x) y (hy:A y=B y) => show A (x+y)=B (x+y) by rw [map_add,map_add,hx,hy]
 exact fun x (hx:A x=B x) r => show A (r • x)=B (r • x) by rw [map_smulₛₗ,map_smulₛₗ,hx]
lemma regain (x:H) : R (J.f x)= J.f (P x):=by rw [Clasp.shadow, sub_apply, h.phonon]; change J.f x-J.f (x-P x)=_; rw [map_sub]; abel
lemma reverse (A:H.Op)(e:A∈ M.commutant) : P (A Ω)=R (J.f (star A Ω)):=by
 let w:=A Ω; let v:= J.f (star A Ω);
 apply ext_inner_right ℂ; intro x
 rw [Clasp.through_self _ C.plume_self,Clasp.through_self _ C.shadow_self]
 let L:H→L[ℂ]ℂ:= (innerSL ℂ w).comp P; let K':H→L[ℂ]ℂ:= (innerSL ℂ v).comp R
 refine h.economize {q:H | L q=K' q} (isClosed_eq L.continuous K'.continuous) ?_ (show L 0= K' 0 by simp) ?_ ?_ x
 · intro B p; change inner ℂ (A Ω) (P _)=inner ℂ (J.f _) (R _)
   rw [h.pose _ p, h.rePose _ p,J.light]
   -- RHS <star B Ω, star A Ω>= < A starB Ω,Ω>; LHS <starB AΩ,Ω>. via comm B*
   rw [show star A=A.adjoint from rfl, adjoint_inner_right, ← adjoint_inner_left B]; have h':=DFunLike.congr_fun (VonNeumannAlgebra.mem_commutant_iff.mp e _ (star_mem (h.pin p))) Ω
   rw [show B.adjoint (A Ω)= A (star B Ω) from h']; -- tune
 · exact fun x (p:L x=K' x) y (q:L y= K' y) => show L (x+y)=K' (x+y) by rw [map_add,map_add,p,q]
 exact fun x (p:L x=K' x) c=> show L (c • x)=K' (c • x) by rw [map_smul,map_smul,p]
-- forward via adjoint opposite core by reflection, simpler: use h.reverse on J conj M
lemma charge (A:H.Op)(e:A∈ M) : P (J.f (star A Ω))= R (A Ω):= by
 have t:= h.reverse _ (h.reflect A e); rw [← J.shade_star, Flash.shade_at, Flash.shade_at, h.opp,J.twice,h.phonon] at t
 rw [h.phonon,← t,J.twice]
end Club
end YM.BridgeClub
