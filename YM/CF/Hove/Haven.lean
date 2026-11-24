import YM.CF.Hove.Leaf
import YM.CF.Hove.Wade
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Hove
open Function Filter Metric Fir Lattice Laurent Next.Free Bloch Finset Lat Stationary Rush Cube Scroll SU Drapes Fir Peaks Dial Paige Brace Vault Fock Tulip Font Spire Nacre Ember Pec
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix Matrix.Norms.L2Operator Kronecker MatrixOrder Classical
attribute [local instance] opCStarAlgebra
open Tap Hake Urn Yaw Levier Proa Rill

variable (j m:ℕ)(e:Even j)(p:4≤j)(v:2≤ m)
variable {c f :Side}(o:Site c)(G:Ratio c f)(w:Odd G.count.val)(T:Script Male)(u:Use j G.count T)(L:Op (Single f))(M:Male)
local notation "Sρ"=> (heel G o)
local notation "W"=> nook_T o m
local notation "φ"=> nook_T (heel G o) m
local notation "Zτ"=> paid_M
local notation "Ψ"=> chipF j G w T M (heel G o)
open Haro Branch Laic
variable {t:ℝ}(Y:cro G t)(P:Meter TailB G t)(Q:Meter Grave G t){a b A C a' c':ℝ}{l k n j':ℕ}(X:∀ i:TailB,Support (More f)→ Toll (Iota G))(pR:∀ i x,Suite (badge _) (pinH G t true) (pinH G t false) x (X i x) (P i x))(hk:∀ i,incline (hall G t) j' a' (fun _=>C) b (X i))(hc:0≤a')(hb:3*a≤b)(hp:0<a)(he:a ≤ 1)(h:0≤ C)
variable {ι:Type}(S_:ι→Male)(U:WG ι)(i:ι)(Po:∀ i n,U i n 1=0)(z:Y.val=1)(Hv:∀ b,Along j G.count w (Thread j) b (S_ i) G 1)(Hy:fulfills G w t (j:=j) S_ U i P Q Y)
local notation "Mρ"=> (mintY m (a:=a) (C:=C))
local notation "Δp"=> pulled G Y P L
local notation "tG"=> (Thread j) -- tune Use
local notation "ΣJ"=> totF j G w (Thread j) (S_ i)
variable (J:Finset (Support (More f)))(hJ:∀ D:Support (More f),D∉J → l ≤ D.card)
local notation "Ξ"=> domF (heel G o)
variable (V:TendV j m)
local notation "G_p"=> chipF j G w (Thread j) (S_ i) (heel G o) (Ξ L)
local notation "Sθ"=> (paid_M Sρ L m)
local notation "L₀"=> (G.count.val:ℝ)
local notation "Xl"=> (2*((2:ℝ)^m*Mρ l*Mρ 0)+ V.A/L₀^5)
structure Grant (j m:ℕ) extends TendV j m where
 F:ℝ
 hx:0 ≤ F
 coin:∀ {c f:Side}(o:Site c)(G:Ratio c f)(w:Odd G.count.val)(T:Script Male),Use j G.count @T →∀ M:Male,∀ X:Dome,∀ a b:ℝ,‖X.1‖≤ a → (∀ i, ‖X.2.1 i‖≤b)→(∀ i,‖X.2.2 i‖≤b) → paid_M o (chipF j G w T M (heel G o) X) m≤ F * ((lace 0 G.count)^2*a+8*(lace 0 G.count*lace 1 G.count)*b)
include p e v
lemma give_a : Nonempty (Grant j m):=by obtain ⟨t⟩:= thunder j m e p v; obtain ⟨C,he,P⟩:=field_v j m e p; exact ⟨t,C,he,@P⟩
variable (K:Grant j m) {x y:ℝ}(hz:‖mornC (heel G o) L‖≤ x)(hX:∀ a:Axis,‖partX (heel G o) L a‖≤y)(hY:∀ a:Axis,‖partY (heel G o) L a‖≤y)(n0:ℕ)(hδ:2*n0<c.val)
local notation "δ"=> (2*((2:ℝ)^m*Mρ l*Mρ 0)+ K.A/L₀^5)
local notation "D0"=> baseF false
local notation "D1"=> baseF true
local notation "ΩY"=> ((Ξ L))
local notation "ζ"=> (lace 0 G.count)
local notation "ξ"=> (lace 1 G.count)
local notation "θ"=> (1+(n0:ℝ))
local notation "κ"=> κP m
local notation "Δ₀"=> (κ*δ*Sθ)
local notation "Z₀"=> (K.C+‖baseF false‖+‖baseF true‖+1)
include hz hX hY hδ Po Hv Hy z w pR hk hc hb hp he hJ h
local notation "Zx"=> partX o (Δp J)
local notation "Zy"=> partY o (Δp J)
local notation "Tx"=> partX (heel G o) L
local notation "Ty"=> partY (heel G o) L
local notation "ZZ"=> (mornC (heel G o) L)
lemma dom_v :
 Zτ o (Δp J-G_p) m ≤ δ*Sθ ∧
 Zτ o (Δp J) m ≤ K.F*(ζ^2*x+8*(ζ*ξ)*y)+δ*Sθ ∧
 ‖mornC o (Δp J) - (ζ:ℂ)^2 • ZZ‖≤ Δ₀ + ((2*Z₀^2)*(ζ^2*x)+(8*Z₀^2)*(ζ*ξ*y))/θ∧ ∀ a:Axis,
 ‖Zx a- ((ζ:ℂ)*(ξ:ℂ)) • culm (Tx a)‖≤ Δ₀+ (Z₀^2*(ζ^2*x)+12*Z₀^2*(ζ*ξ*y)/θ) ∧
 ‖Zy a- ((ζ:ℂ)*(ξ:ℂ)) • culm (Ty a)‖≤ Δ₀+ (Z₀^2*(ζ^2*x)+12*Z₀^2*(ζ*ξ*y)/θ) :=by
 have p0:= cord j m e p v o G w L Y P Q X pR hk hc hb hp he h S_ U i Po z Hv Hy J hJ K.toTendV -- ABI
 let V₀:= G_p; let U':= Δp J
 let T_:= K.bench; have hu:=canUse j G.count w
 have hx:=T_ false o G w (Thread j) hu (S_ i) n0 hδ -- def not
 have hy:=T_ true o G w (Thread j) hu (S_ i) n0 hδ
 let p':Op (Single c):= U'-V₀; have hZ(ι:Kt)(j':ℝ)(h: j' ≤ κ*Zτ o p' m): j' ≤ Δ₀:=by
    have hx:0 ≤ κP m:=by unfold κP Haro.ξP; have hs:=mpe false; have hv:=mpe true; positivity
    exact h.trans ((mul_le_mul_of_nonneg_left p0 hx).trans_eq (mul_assoc _ _ _).symm)
 have Hp: V₀ + p'= U':=by unfold p'; abel
 refine ⟨p0,?_,?_,fun b=>?_⟩
 · change paid_M o U' m ≤ _; nth_rw 1 [←Hp]; exact (paidp_sum ..).trans (add_le_add (K.coin _ _ _ _ hu _ _ _ _ hz hX hY) p0)
 · have hQ:mornC o p'=mornC o U'-mornC o V₀:=show snapH (rampF false o) (rampF true o) (U'-V₀) = _ from map_sub ..
   have hg:=comet_v j G w (S_ i) o (Thread j) K.C K.ht n0 ΩY hx hy x y hz hX hY -- notation
   refine le_trans ?_ (add_le_add (hZ tagF _ (ζr o p' m)) hg); rw [hQ, show culm (Ξ L).1=ZZ from (true_P ..).1 ]; apply le_trans (le_of_eq _) (norm_add_le ..); congr 1; abel
 constructor
 · refine le_trans ?_ (add_le_add (hZ tagF _ (opox o p' m b (by omega))) (tonic_X j G w (S_ i) o (Thread j) K.C K.ht n0 ΩY hx hy x y hz hX hY b)); rw [show partX o p' b=partX o U' b-partX o V₀ b from (show snapH (spanH false o b) (rampF true o) (U'- V₀)=_ from map_sub ..)]
   apply le_trans (le_of_eq _) (norm_add_le ..); congr 1; abel
 refine le_trans ?_ (add_le_add (hZ tagF _ (opoy o p' m b (by omega))) (tonic_Y j G w (S_ i) o (Thread j) K.C K.ht n0 ΩY hx hy x y hz hX hY b)); rw [show partY o p' b=partY o U' b-partY o V₀ b from (show snapH (rampF false o) (spanH true o b) (U'-V₀)=_ from map_sub ..)]
 apply le_trans (le_of_eq _) (norm_add_le ..); congr 1; abel
end YM.CF.Hove
#print axioms YM.CF.Hove.dom_v
#print axioms YM.CF.Hove.give_a
