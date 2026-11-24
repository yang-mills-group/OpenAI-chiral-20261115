import YM.CF.Hive.Roil
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 20000
set_option linter.unusedVariables false
noncomputable section
namespace YM.CF.Hive
open Function Filter Metric NormedSpace Finset Fock Lattice Wilson Laurent Lat Rush SU Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant Phase Broc Matrix Scroll Thera Branch Laic Cube
open scoped Matrix.Norms.L2Operator Matrix Topology ContDiff MatrixOrder BigOperators InnerProductSpace Kronecker
attribute [local instance] opCStarAlgebra
open Urn Hake Levier Spire Scree Stilo
attribute [local instance] opCStarAlgebra
open Acorn Nacre Skye MeasureTheory Jet
variable {N B m L:Side}{j k:ℕ}{z K v a b d c e H t:ℝ}
local notation "N₀"=> CSide m B
variable (S:Seal (Skye.Seat (CSide m B)))(s:Sweep (CSide m B))(A:Ids (CSide m B))(X:Axx (Skye.Seat (CSide m B)) (Single (CSide m B)) (Castle m B e (actS s S))) -- order
abbrev ferryQ(A:Bool)(X:FC (Single N₀)):=if A then cc X else X
abbrev χ(s:Sweep N):=s.charge.xor (detX s.s)
def charm(i:DeckU X.2.1): Axx (Skye.Seat N₀) (Single N₀) (Castle m B e S):=(actS s⁻¹ X.1,castJ s⁻¹ X.2.1 i,(jive s⁻¹ A X.2.1 i) • (cSignX (χ s⁻¹) ∘ (X.2.2.1 ∘ moveD s A)), X.2.2.2) -- cost use nominal. Pro greater not Pro larger if zero? build
lemma acro (Z:Seal (Skye.Seat N₀))(g:Ids N₀)(x:ℂ)(V:FC (Single N₀)): mallC Z g (x • V)= cSignX (χ (chip Z g)⁻¹) x • mallC Z g V:=by
 unfold mallC; rw [RingHom.comp_apply]; let s:= (chip Z g)⁻¹; have ht:teen s (x • V)=cSignX (χ s) x • teen s V:=lot_s ..; rw [show teen (chip Z g)⁻¹ (x • V)= _ from ht]; exact lot_s ..
lemma vivX (U:Ids N₀)(S:Seal (Skye.Seat N₀))(X:Axx (Skye.Seat N₀) (Single N₀) (Castle m B e (strideG S U)))(x:Castle m B e S): (mallC S U) (vowC X (strideH S U x))=∑ i:DeckU X.2.1,vowC (charm S (chip S U) U X i) x:=by
 unfold vowC; rw [acro, swing,Finset.smul_sum]; refine sum_congr rfl fun i _=>?_ ; rw [smul_smul]; unfold charm; dsimp only [Function.comp_apply]; rw [mul_comm]; rfl
lemma modalT (T:Branch.Field (Skye.Seat N₀))(G:Acorn.Master (Castle m B e S) (Skye.Seat N₀)) (F: Castle m B e S→ℂ) {U:Seal (Skye.Seat N₀)} (h:Acorn.Pro G U F a)(z:ℂ)(p:‖z‖ ≤ 1): Acorn.Pro G U (z • F) a:=by
 have hx:= h.sc z; have he:= mul_le_of_le_one_left h.pos p
 exact ⟨h.pos,h.travel,hx.cont,fun i=>(hx.sumline i).trans he,hx.reads,fun E _ _ _ U f k t x g=>(hx.plot _ _ f _ t _ g).mono he⟩
lemma repay (i:DeckU X.2.1)(l:ShiftD k v H e S A s) (t:fits (landX k H (actS s S) e) (home_n _) (actS s S) X): fits (landX k v S e) (home_n _) S (charm S s A X i):=⟨fun j p=>by have hp:actS s⁻¹ (actS s S) ⊆ actS s⁻¹ X.1:= map_subset_map.mpr t.1; exact hp (show j∈actS s⁻¹ (actS s S) from by rwa [actG_l]),grove_t _ _ t.2.1, (tick_size s⁻¹ X.2.1 i).symm ▸ t.2.2.1,tick_in _ _ t.2.2.2.1 i, modalT S (terr _) _ _ (pSign _ _ (ferry A s l t.2.2.2.2)) _ (jive_le ..)⟩ -- T imp
lemma far_p (h:(actS s S)⊆ X.1)(z a:ℝ): (∑ i:DeckU X.2.1,hireC a z S (charm S s A X i))= hireC a (Fintype.card Play*z) (actS s S) X:=by
 have hp:Acorn.cost a S (actS s⁻¹ X.1)=Acorn.cost a (actS s S) X.1:=by
    unfold Acorn.cost Branch.rent; rw [card_sdiff_of_subset h,card_sdiff_of_subset ?_]; simp [actS]; have hp:actS s⁻¹ (actS s S)⊆actS s⁻¹ X.1 := map_subset_map.mpr h; rw [actG_l] at hp; exact hp
 unfold hireC; simp_rw [show ∀ i,(charm S s A X i).2.2.2=X.2.2.2 from fun _=>rfl,show ∀ i,(charm S s A X i).1= actS s⁻¹ X.1 from fun _=>rfl,show ∀ i,(charm S s A X i).2.1.length=X.2.1.length from tick_size _ _,hp,sum_const]; rw [card_univ,hallN]; rw [nsmul_eq_mul,Nat.cast_pow,mul_pow]; ring -- tune multiplication pow
lemma appear (A':Ids N₀)(i:DeckU X.2.1)(x y:Castle m B e S)(t:fits (landX k H (actS s S) e) (home_n _) (actS s S) X)(h:Set.EqOn A A' (actS s⁻¹ X.1))(v:∀ i, Agrees (actS s⁻¹ X.1) (x.val i) (y.val i)): (charm S s A X i).2.2.1 x=(charm S s A' X i).2.2.1 y:=by
 unfold charm; simp only [Pi.smul_apply,Function.comp_apply]; rw [jive_in (S:=X.1) s⁻¹ A X.2.1 t.2.2.2.1 i h,t.2.2.2.2.reads _ _ (ferryG X.1 A A' s x y h v)]
end YM.CF.Hive
