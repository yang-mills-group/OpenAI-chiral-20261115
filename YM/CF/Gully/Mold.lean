import YM.CF.Gully.Edge
import YM.CF.Ione.Tape
import YM.CF.Spire.Thick
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
open Scion Skye Hive Ione Scree
variable (s:Era m)
local notation "C"=> netB m B s
def weQ (s:Era m):Stamp m B≃ Stamp m B where
 toFun:= actS (netB m B s)
 invFun:= actS (netB m B s⁻¹)
 left_inv X:=by rw [map_inv,actG_l]
 right_inv X:=by rw [map_inv]; convert actG_l (netB m B s)⁻¹ X using 1; rw [inv_inv]
def LaPY (F:Oil (e:=e) m B)(S:Stamp m B)(x:Briar m B e): Cipher Λ:= rip m • ∑ s:Era m,RainD s (F (weQ s S)) x
abbrev plaza (F:Briar m B e→Cipher Λ):Prop:=∀ s:Era m,∀ i,F (shotV s i)= suit_Y (netB m B s) (F i)
def rain_X (w:Stamp m B→ℝ)(S:Stamp m B):= ‖rip m‖*∑ s:Era m,w (weQ s S)
private lemma scat_a (w:Stamp m B→ℝ)(x:Site ξ): hitE a w ((boxA C).symm x) = hitE a (fun i=>w (weQ s i)) x:=by
 unfold hitE hit0; rw [sum_filter,sum_filter]; conv_lhs => rw [←Equiv.sum_comp (weQ s)]
 apply sum_congr rfl; intro i _; simp [weQ,actS,rent]
lemma rot_E (F:Oil (e:=e) m B)(S:Stamp m B):∀ i,LaPY F (linkQ s S) (shotV s i)= suit_Y C (LaPY F S i):=by
 intro i; unfold LaPY; rw [map_smul]; apply congrArg; conv_rhs=> rw [← Equiv.sum_comp (Equiv.mulLeft s)]
 rw [map_sum]; apply sum_congr rfl; intro t _; have ht:weQ t (linkQ s S) =linkQ (s*t) S:= roll_O ..
 rw [ht]; change suit_Y _ (F (linkQ (s*t) S) (shotV t (shotV s i)))=suit_Y C (suit_Y (netB m B (s*t))⁻¹ (F (linkQ (s*t) S) _)); rw [shot_m, moon_Y,map_mul,mul_inv_rev]; simp
lemma gloom {U1:Briar m B e→Cipher Λ}{F:Oil (e:=e) m B} (h:plaza U1) (g:∀ i,U1 i=∑ j,F j i):∀ x:Briar m B e, U1 x=∑ S,LaPY F S x:=by
 intro x; unfold LaPY; rw [←smul_sum,sum_comm]; have ht(s:Era m):(∑ S:Stamp m B,RainD s (F (weQ s S)) x)=U1 x:=by unfold RainD; rw [←map_sum,Equiv.sum_comp (weQ s) (fun i=> F i (shotV s x)),←g,h s x,moon_Y,mul_inv_cancel,toon_Q] -- Equiv.sum_comp match
 rw [sum_congr rfl (fun s _=>ht s),sum_const, ← Nat.cast_smul_eq_nsmul ℝ,card_univ,smul_smul,show rip m*_=1 from inv_mul_cancel₀ (by exact_mod_cast Fintype.card_ne_zero),one_smul]
structure PlotQ (K:ℝ)(n:ℕ)(H e:ℝ)(T:Briar m B e→ Cipher Λ)(a c:ℝ):Prop where
 seed :∃ (F:Oil (e:=e) m B) (w:Stamp m B→ℝ), (∀ i,Inscribed K e n i H (F i) (w i)) ∧ (∀ i,hitE a w i ≤ c) ∧ (∀ i,T i=∑ S,F S i) ∧ ∀ i:Era m,∀ S x, F (linkQ i S) (shotV i x)=suit_Y (netB m B i) (F S x)
lemma yearZ {T:Briar m B e→ Cipher Λ}(h:Cereal U e n H T a c)(t:Δt n K U)(g:plaza T): PlotQ K n H e T a c:=by
 obtain ⟨F,w,p,u,h'⟩:=h.seed; refine ⟨LaPY F,rain_X w,fun i=>layer i _ (stem_V (A:=fun s=>RainD s (F (weQ s i))) (x:=fun s=> w (weQ s i)) (fun s:Era m=> bar_d s (p (weQ s i)) t)),fun i=>?_ ,gloom g h',fun i=>rot_E i F⟩ -- prop structure
 unfold rain_X hitE; simp_rw [mul_left_comm (rent ..),←mul_sum]; apply le_trans (b:= ‖rip m‖*(∑ _j:Era m,c))
 · apply mul_le_mul_of_nonneg_left _ (norm_nonneg _); simp_rw [mul_sum] -- tune
   rw [sum_comm]; exact sum_le_sum (s:=univ) (g:=fun s:Era m=>c) fun s h=>le_trans (scat_a (a:=a) s w i).symm.le (u _)
 apply le_of_eq; simp only [sum_const,nsmul_eq_mul,card_univ]; rw [Real.norm_of_nonneg (by unfold rip; positivity : 0 ≤ rip m),← mul_assoc, show rip m*_=1 from inv_mul_cancel₀ (by exact_mod_cast Fintype.card_ne_zero),one_mul]
end YM.CF.Gully
