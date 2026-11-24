import YM.CF.Gully.Luck
set_option autoImplicit false
set_option maxHeartbeats 550000
set_option synthInstance.maxSize 22000
noncomputable section
namespace YM.CF.Gully
open Function Fock Filter Metric NormedSpace Lat Lattice Branch Cube Tenant MeasureTheory Phase Finset Mir Scroll Spire RP Str Petal Manifest Palot Stilo Dial Paige Vault Brace RG Push.AbsoluteSums Trees
open scoped Topology Classical BigOperators InnerProductSpace Matrix Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {m B L N:Side}
local notation "Λ" => CSide m B
local notation "ξ" => Domain m B
open Maize Gloss Floe Ave Phase.Sample Jet Pastry Drapes Gas
variable {r e U K A H:ℝ}{n:ℕ}
variable {a v b c d:ℝ}
open Scion Skye Ione Tulip Scree
variable (s:Era m) {p:1≤H}
abbrev Marsh(m B:Side): Ewe m B→ₐ[ℝ] Cipher (CSide m B):= Artifact (ore_b (Tulip.helix (CSide m B)))
abbrev Campus B m e U n (F : Briar m B e→ Ewe m B) (H:ℝ) (p:1≤H)(a b:ℝ):= HatX e H p U n F a b
lemma lingQ(X:Ewe m B): Marsh m B (Rayp s B X)= suit_Y (netB m B s) (Marsh m B X):=by
 let U:=netB m B s; let Y:= prepU (castX U) (WA s B) (xtra s.charge) Λ; apply bringB (Tulip.helix Λ) s.charge (detX s.s) ?_ X; change portW (helix _).symm (LA s B).val= Y.val; ext; rfl -- tune
lemma lantern(g:Court m B)(X:Ewe m B): Marsh m B (routeM m B g X)= paintR false false (tradew Λ g) (Marsh m B X):=by
 let V:= Ave.balls m B g; have ht: routeM m B g X= paintR false false V X:= rfl; rw [ht]; apply bringB (helix Λ) false false ?_
 ext x y; rcases x with ⟨⟨x,b⟩,s⟩; rcases y with ⟨⟨y,c⟩,t⟩
 by_cases r:x=y<;>by_cases h:b=c <;>simp [V,balls,Lat.conjG,portW,tradew,helix,jump_apply,r,h,SpinIdx,color] -- tune
structure Inscribed (K:ℝ)(e:ℝ)(n:ℕ)(S:Stamp m B)(H:ℝ)(F:Briar m B e→ Cipher Λ)(w:ℝ):Prop where
 pos: 0 ≤ w
 grove: w ≠ 0 → Grove (terr _) S
 grammar(i:Briar m B e) : Flour (camp S) (F i).val
 gauge(i:Briar m B e)(x:Court m B) : F (routeS x i) = paintR false false (tradew Λ x) (F i)
 locality (i j:Briar m B e): Agrees S i.val j.val→ F i=F j
 continuous_T: Continuous F
 jets:∀ (E:Type)[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E](f:E→Briar m B e)(T:Set E), IsOpen T→ (∀ x∈T,TransK n (fun i=>(f i).val) x K)→∀ x∈T, Allows n (fun i=>dilF H (F (f i))) x w
lemma cave_a {T:Briar m B e→ Ewe m B}{S:Stamp m B}{v:ℝ}(h:Chalk e H p U n S T v): Inscribed (m:=m) U e n S H (Marsh m B ∘ T) v:=by
 let X:=Marsh m B; have he:=h.home; refine ⟨he.price,he.shape,fun i=> ?_,fun i x=> ?_,fun i j v=>congrArg X (he.locality v), X.toLinearMap.continuous_of_finiteDimensional.comp he.ct,?_⟩
 · have hz:= cloud_i (ore_b (helix Λ)) (cairn m B S) (T i).val (he.gram i); apply hz.lift; intro x u; obtain ⟨t,y,hx⟩:=mem_map.mp u; subst x; have hy:carrier Λ t.2∈S:=(mem_filter.mp y).2; exact mem_filter.mpr ⟨mem_univ _,hy⟩
 · change X (T ((PinK m B e H p).pick x i))=_; rw [← he.dress]; exact lantern ..
 intro E _ _ _ f A o t x v'; simp only [Function.comp_apply]; simp_rw [Marsh,←dipV]; let V:Ewe m B→L[ℝ] Cipher Λ:=⟨X.toLinearMap,X.toLinearMap.continuous_of_finiteDimensional⟩
 rw [← one_mul v]; refine Allows.linear (F:= Ewe m B) (G:=Cipher Λ) V (h.actsJ E f A o t x v') ?_; apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one; intro u; rw [one_mul]; exact railN (ore_b (helix Λ)) u.val
structure Cereal (K:ℝ)(e:ℝ)(n:ℕ)(H:ℝ)(F:Briar m B e→ Cipher Λ)(a c:ℝ):Prop where
 seed :∃ (T:Stamp m B→ Briar m B e→Cipher Λ)(w:Stamp m B→ℝ),(∀ i:Stamp m B,Inscribed K e n i H (T i) (w i))∧ (∀ i:Site ξ,hitE a w i ≤ c) ∧ ∀ x, F x=∑ i,T i x
lemma hold_C {F:Briar m B e→ Ewe m B}(h:HatX e H p U n F a c) : Cereal (m:=m) U e n H (Marsh m B ∘ F) a c:=by
 obtain ⟨T,w,h,p,g⟩:=h; refine ⟨_,w,fun i:Stamp m B=>cave_a (h i),p,fun x=>?_⟩; rw [Function.comp_apply,g,map_sum]; rfl
end YM.CF.Gully
