import GaugeFieldConstruction.VertigoΛL

/-!
# The word isometry. The charged (ManyF timeslice) Hilbert is used in the application for J.
A common invariant word domain on reconstruction, although the input OPs on named charges also
pay on a larger domain over the purchaser's space. All **ordered** products, not assuming
uniqueness in the chosen phase across another purchase.
-/
set_option autoImplicit false
set_option maxHeartbeats 170000
noncomputable section
namespace YM.NSF.Boundary
open MeasureTheory Filter Function Set Complex YM.Boundary Kernel
open scoped Topology BigOperators NNReal ContDiff InnerProductSpace
variable {G:Gauge}{L:Register G}{S:Table L}{W:Surface S}{R:S.Rotation}{x:S.RealSpin}{F:Wightman S}
variable {B:Hilbert}(h: F.Realizes (W:=W) R x)

local notation "Con" => F.operators.domain
structure WordLiftSt (F:Wightman S){H:Hilbert}(K:Submodule ℂ H)(A:Sentence S→K)(Γ:Letter S →(K→ₗ[ℂ] K)) where
  rays: F.operators.H →ₗᵢ[ℂ] H
  onWord (b): rays (F.operators.vector b)= (A b).val
  pocket: F.operators.domain →ₗᵢ[ℂ] K
  town(x:F.operators.domain):rays x.val=(pocket x).val
  acts(f) (x:F.operators.domain): pocket (F.operators.edits f x)= Γ f (pocket x)
variable (K:Submodule ℂ B) (A:Sentence S→K) (Γ:Letter S →(K→ₗ[ℂ] K))
  (H:∀ (f:Sentence S)(g:Sentence S), inner ℂ (A f : K) (A g)= W.kernel F.J f g) (T:∀ c b, A (c::b)= Γ c (A b))
include h H T
lemma word_dic : Nonempty (WordLiftSt F (H:=B) K A Γ):=by
 let Z(b):=(A b).val
 obtain ⟨I,-,hw,hp⟩:= Soil.universal_embed (TraceWordΛL h) (M:=B) Z H
 let P:F.operators.H→ₗᵢ[ℂ]B:={ I.toLinearMap with norm_map':=hp }; have hs(b): P (F.operators.vector b)= (A b).val:= hw b
 let Q:= P.toLinearMap
 have he(x:F.operators.H)(p:x∈ F.operators.domain):P x∈K:=by
    refine (show F.operators.domain≤ K.comap Q from ?_) p
    rw [h.total.cyclic]; apply Submodule.span_le.mpr; rintro _ ⟨b,rfl⟩; exact (K.mem_comap).2 ((hs b).symm ▸ (A b).property) -- syntax
 let J:Con →ₗᵢ[ℂ] K:={ (Q.restrict he) with norm_map':= fun x=>hp x.val } -- he has explicit x and p
 have hA(b): J (F.operators.evaluates b)= A b:= Subtype.ext (hs b)
 refine ⟨P,hs,J,(fun _=>rfl),fun f x=>?_⟩; let O:=J.toLinearMap
 have hv(x:F.operators.H)(p:x∈Con) : J (F.operators.edits f (⟨x,p⟩:Con))=Γ f (J (⟨x,p⟩:Con)):=by
    apply Submodule.span_induction (p:=fun x (p:x∈Submodule.span ℂ (range F.operators.vector))=> ∀ X:Con,X.val=x→ J (F.operators.edits f X)=Γ f (J X)) ?_ ?_ ?_ ?_ (h.total.cyclic ▸ p) (⟨x,p⟩:Con) rfl
    · rintro y ⟨c,rfl⟩ q e; rw [show q=F.operators.evaluates c from Subtype.ext e,hA]; exact (hA (f::c)).trans (T f c)
    · intro p k; rw [show p=0 from Subtype.ext k,map_zero,map_zero,map_zero]
    · intro x y u z s t p k; let a:Con:=⟨x,h.total.cyclic.symm ▸ u⟩; let b:Con:=⟨y,h.total.cyclic.symm ▸ z⟩; rw [show p=a+b from Subtype.ext k,map_add,map_add,map_add,s a rfl,t b rfl]; rw [map_add]
    intro c x u s p k; let a:Con:=⟨x,h.total.cyclic.symm ▸ u⟩; rw [show p=c • a from Subtype.ext k,map_smul,map_smul,map_smul,s a rfl]; rw [map_smul]
 exact hv x x.property
omit h H T

namespace WordLiftSt
variable {K A Γ}(W:WordLiftSt F (H:=B) K A Γ)
lemma litPage (p:Sentence S):W.pocket (F.operators.evaluates p)=A p:=Subtype.ext ((W.town _).symm.trans (W.onWord p))
-- handy for derived field ops
abbrev sends (J:Con→ₗ[ℂ] Con)(D:K→ₗ[ℂ]K):Prop:= W.pocket.toLinearMap ∘ₗ J = D ∘ₗ W.pocket.toLinearMap
lemma sends_at (x) (f) {J:K→ₗ[ℂ]K}(h:J=Γ (x,f)): W.sends (F.operators.field x f) J := by rw [h]; exact LinearMap.ext (W.acts (x,f))
lemma sends_scale (c:ℂ)(J:Con→ₗ[ℂ]Con)(D:K→ₗ[ℂ]K)(u:W.sends J D): W.sends (c • J) (c • D):=by unfold sends; rw [LinearMap.comp_smul,LinearMap.smul_comp,u]
lemma sends_add (J M:Con→ₗ[ℂ]Con)(D D':K→ₗ[ℂ]K)(u:W.sends J D)(q:W.sends M D'): W.sends (J+M) (D+D'):=by unfold sends; rw [LinearMap.comp_add,LinearMap.add_comp,u,q]
lemma sends_sum {I:Type*}(i:Finset I)(J:I→ Con→ₗ[ℂ]Con)(D:I→ K→ₗ[ℂ]K)(u:∀ j∈i,W.sends (J j) (D j)): W.sends (∑ j∈i,J j) (∑ j∈i,D j):= by
 classical
 induction i using Finset.induction with
 | empty=> simp only [sends,Finset.sum_empty,LinearMap.zero_comp, LinearMap.comp_zero]
 | insert j i g s=> rw [Finset.sum_insert g,Finset.sum_insert g]; exact sends_add W (J j) _ _ _ (u j (Finset.mem_insert_self ..)) (s (fun i e=> u i (Finset.mem_insert_of_mem e)))
lemma via_cash (J:Con→ₗ[ℂ]Con)(D:K→ₗ[ℂ]K)(p:W.sends J D)(x:Con) : W.pocket (J x)= D (W.pocket x):= DFunLike.congr_fun p x
lemma invoice (J:Con→ₗ[ℂ]Con)(D:K→ₗ[ℂ]K)(u:W.sends J D): inner ℂ F.operators.omega (J F.operators.omega)=inner ℂ (A []) (D (A [])):=by
 have hv: W.pocket F.operators.omega= A []:= W.litPage []
 rw [←W.pocket.inner_map_map, W.via_cash _ _ u,hv]
lemma symmetricReceipt (J:Con→ₗ[ℂ]Con)(D:K→ₗ[ℂ]K)(u:W.sends J D)(v:LinearMap.IsSymmetric D):LinearMap.IsSymmetric J:=fun x y=> by rw [←W.pocket.inner_map_map,←W.pocket.inner_map_map x (J y),W.via_cash _ _ u,W.via_cash _ _ u,v]
lemma sends_prod (J M: Con→ₗ[ℂ]Con)(D D':K→ₗ[ℂ]K)(u:W.sends J D)(q:W.sends M D') : W.sends (J*M) (D*D'):=by apply LinearMap.ext; intro x; change W.pocket (J (M x))= D (D' (W.pocket x)); rw [W.via_cash _ _ u, W.via_cash _ _ q]
lemma invoice_pair (J M: Con→ₗ[ℂ] Con)(D D': K→ₗ[ℂ] K)(u:W.sends J D)(q: W.sends M D') :
    inner ℂ F.operators.omega ((J*M) F.operators.omega)
     - inner ℂ F.operators.omega (J F.operators.omega)*inner ℂ F.operators.omega (M F.operators.omega)=
     inner ℂ (A []) ((D*D') (A [])) -inner ℂ (A []) (D (A []))*inner ℂ (A []) (D' (A [])):=by
 rw [W.invoice _ _ (W.sends_prod _ _ _ _ u q), W.invoice _ _ u, W.invoice _ _ q]
end WordLiftSt
#print axioms word_dic
#print axioms WordLiftSt.invoice_pair
#print axioms WordLiftSt.symmetricReceipt
end YM.NSF.Boundary
end
