import Anomaly.Compass.Grid
import Anomaly.Compass.Nest
import Anomaly.Apert.Sync
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 700000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Vow.TreasuryFog
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Skye Scree Cadre Palot
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tulip Fock Rush Scroll Paige Vault Phase Acorn Spire
open Pastry Vow Rue Hake Jet Sault Stax Rill Ione Clock Salt Mew PowerSeries Sour Turning
attribute [local instance] opCStarAlgebra
open scoped Mew
variable {n N B:Side}
local notation "Ω"=> mid N B
open QuadClock Neon Bake Larch Roots Py Swell Analysis Pressure Oath Moto Porticus
variable {p:BudgetPoint}{q l m n₀:ℕ}{h w μ c d x a b v s' τ Q:ℝ} {F: ForceBudget (mid N B)}
variable {s:Sweep (mid N B)} {E: Bag (mid N B)}{o:Site (mid N B)}
-- Use predicate for users to transform physical probe Baby then all ETA ups using launches. allows storing ASYMMETRIC probe prices and translating increments consumers.
structure Flint (P:BudgetPoint) (K:Bag (mid N B))(S:Support (More (mid N B)))(G:RegBudget (mid N B))(U:Cusp (mid N B))(t:ℂ)(Φ:ArcΦ)(o:Site (mid N B))(s q:ℕ)(h x a b w u z:ℝ): Prop where
  yard : Cube.node o∈ S
  step : Barrage P q S h K x a b
  mood: ∀ (V:Ids (mid N B))(W T:Aura (mid N B)→ℝ)(t':∀ i, Flight P q i h (K i) (W i) (T i)),Ice s o P h w u z (marksCopy P (singlePole V K t' (Cube.node o))) G U t Φ
-- certify base probes. K,F,S.
variable {Φ:ArcΦ}{U:Cusp (mid N B)}{ξ:ℂ}{L:RegBudget (mid N B)} {S:Support (More (mid N B))} {e z:ℝ}
lemma Flint_emit (K: Flint p E S L U ξ Φ o l q h x a b e z w) : Axon l o p L h e Φ∧ ‖ξ‖≤ w∧(∀ x, Cube.node o∉ (x:Aura Ω).val → U x=0):=by
 obtain ⟨t,v,J,Q⟩:= K.step.price; let X:= K.mood (Classical.arbitrary _) t v J; exact ⟨X.axle,X.phase,X.stout⟩
lemma Flint_gain (V: Flint p E S L U ξ Φ o l q h x a b e z w) {v m L₀ s ψ:ℝ}(ha:a ≤ v)(f:b ≤ m)(g:e ≤ L₀)(t:z ≤  s)(k:w ≤ ψ): Flint p E S L U ξ Φ o l q h x v m L₀ s ψ:=by -- trick L shadow
 refine ⟨V.yard,V.step.bigR ha f,?_⟩; intro W T a i; apply (V.mood W T a i).gain_μ <;> assumption
lemma drillSlope (p':Drill p q n₀ l o h x E Φ a b 0)(hp:1≤h) (H:Taxi.DayT p.order μ)(u:0 ≤ μ)(g:Gala p.power p.order 100 τ 3)(c:10 ≤ p.B)(k:p.threshold=temp τ)(e:1 ≤ radiusB τ)(Z:20 < (More (mid N B)).val)(m: 3 ≤ (mid N B).val) : ∃ M L t, Flint p E (grooveB n₀ p (node o)) M L t Φ o l q h x a a (Δv p μ*b) (Extr_h l p μ*b) b:=by
 obtain ⟨G,F,H',L⟩:=p'.yard.price
 let t':= Classical.arbitrary (Ids Ω)
 obtain ⟨x_,v,q₀⟩:=p'.stamp G F t' H'; let M:= singlePole t' E H' (node o)
 obtain ⟨V,K,T,Y,u0,v0,k0⟩:=baseIce l o hp H u g c k e Z m x_ q₀
 have hu:0<h^2:=pow_pos (zero_lt_one.trans_le hp) _
 have hv: Y=Φ:=by have ht:pilasters l p o M= Y:= v0.symm; change ‖(pilasters l p o M).1- _‖≤0 ∧ ‖(pilasters l p o M).2-_‖* _ ≤0 at v; rw [ht] at v; exact Prod.ext (sub_eq_zero.mp (norm_le_zero_iff.mp v.1)) (sub_eq_zero.mp (norm_le_zero_iff.mp (nonpos_of_mul_nonpos_left v.2 hu))) -- left/right check
 exact ⟨V,K,T,halo_subset _ _ (mem_singleton_self _), p'.yard,fun V W X t=> by rw [←hv,booth_one H' t' _ t V]; exact u0⟩
-- energy only from Barrage budget.This for Y. e launch at bPS.Progress assertion.K.Fray. Also Null storage later.
lemma reservoir (H:Barrage p q S h E (p.supportExponent+8/(p.B:ℝ)) a b)(t:node o∈S) (hp:1≤h) (Y:Taxi.DayT p.order μ)(u:0 ≤ μ)(g:Gala p.power p.order 100 τ 3)(c:10 ≤ p.B)(k:p.threshold=temp τ)(e:1 ≤ radiusB τ)(Z:20 < (More (mid N B)).val)(m: 3 ≤ (mid N B).val) (f:ℝ) (hf:Nor.reserveT p.power p.order p.B ((p.B:ℝ)⁻¹)*|b|≤f) :∃ M L t Φ, Flint p E S M L t Φ o l q h (p.supportExponent+8/(p.B:ℝ)) a b (Δv p μ*f) (Extr_h l p μ*f) f:=by
 obtain ⟨G,F,Q,v,z,kc⟩:=H.price
 let t':= Classical.arbitrary (Ids Ω); let I:= Fin 1; let P:= fun (_:Fin 1) i=> Q i
 obtain ⟨A,B,T,D,u0,v0,k0⟩:=baseIce l o hp Y u g c k e Z m (protoInc _ P t' (0:Fin 1) _ (by omega) (zero_le_one.trans hp) kc hf) (fun i v=>station _ _ _ P t' _ (0:Fin 1) i v)
 exact ⟨A,B,T,D,t,H,fun V W X t=> by rw [booth_one Q t' _ t V]; exact u0⟩
local notation "UK"=> (arc_s (s).s (Levier.spinU false (s).s) Φ)
local notation "Yξ"=> cartTurn s E
lemma yardPull (V:Flint p E S L U ξ Φ o l q h x a b e z w)(hp:1≤h)(o':Site Ω) (u:mPath s o'=o) (W:HavenL (mid N B) p l)(g:s∈Whirl (mid N B)): Flint p Yξ (actY s S) (dashF s L) (dashK s U) (Spire.payZ s ξ) UK o' l q h x (strive_E p.order*a) (strive_E p.order*b) (duty_Q p.order p.power*e) (strive_E p.order*z) w:=by
 subst o
 have ht:= urge s g E V.step (zero_le_one.trans hp)
 refine ⟨?_,ht,?_⟩
 · unfold actY; rw [mem_map_equiv]; change boxA s (node o')∈S; rw [←nodeA]; exact V.yard
 obtain ⟨G,Q,K,u⟩:= V.step.price
 intro T W' B' p'
 let H:=V.mood T G Q K; apply iceLaw (i:=H) _ _ _ _ _ _ _ _ _ _ _ (zero_le_one.trans hp) (Ice_γ (zero_le_one.trans hp) H).1 W.rooms W.period g _ (Levier.spinZ ..)
 exact marksTurn s (o:=fun _=>_) (u:=fun _=>_) (fun (_:Fin 1) i=>K i) (fun (_:Fin 1) i=> p' i) T (0:Fin 1) (0:Fin 1) (fun V _=>fun X=> runs s E V X) rfl
end YM.CF.Vow.TreasuryFog
