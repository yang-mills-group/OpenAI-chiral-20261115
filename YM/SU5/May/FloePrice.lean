import YM.SU5.May.FloeExchange
import YM.SU5.May.FloeSpoke
import YM.SU5.May.FloeChristal
import YM.SU5.May.FloeGauge
set_option autoImplicit false
set_option maxHeartbeats 450000
set_option synthInstance.maxSize 30000
set_option maxRecDepth 3000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.May.Floe
open Function Filter Finset Fir Lattice Laurent Next.Free Bloch Lat Ember Jill Rush
open scoped Topology BigOperators ContDiff InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator Classical
attribute [local instance] opCStarAlgebra
open Onyx Fock SU Flare Kea Sods Emu Dial Cube Tulip Spire Scroll Thera
open Fock Reflect
open Lamour (lakeP lakeK)
open Hygrometry Personality PriceCliff
open RG Wilson Phase Mir Vale Vale.Grace Peaks Paige Vault
open Stationary (Gaia)
open Buffered.Lifted Buffered.Afterglow.Tower.Tilted
open scoped ComplexOrder
local notation "Ω" => Complex.I
variable {K: Pressure.Teller group} {P: Patch}{B:Side}{e:ℝ}{Y: Pricing K.j P.L P.odd_side (Thread K.j)}(A:Grasp Y B e)(g:0≤e)(h:1≤K.j) (p:Pearl A) (u:Stamped K.j P.L P.odd_side Y)
variable {m:Side}(R:Ramp)(M:Jill.Male)(k:A.roundZ ≤ (CSide m B).val)(w:Pad K.j (CSide m B))
variable {α β:Type*}
local notation "N"=> CSide m B
local notation "Σ"=> changeM (m:=m) A 1 M
local notation "R↑"=> whisper R
local notation "R₀"=> land_tilt R
local notation "V" p:max => (whisper R).cell p
local notation "Λ" p:max => (whisper R).role p
open Arctic
variable (U:α→ Cover)(X:α→Personality) (b:Bool) [Fintype β] (F:β→ List α)(v:β→ℂ)
abbrev reality (s:Side)(j:ℕ)(i l:α⊕α): ℂ:=ice j s M 1 (posted (whisper R) U i) (posted (whisper R) U l) (Packed (whisper R) X i) (Packed (whisper R) X l)
local notation "K₀" => reality R M U X (CSide m B) K.j
def myth (s:Side)(j:ℕ)(i l:α⊕α):ℂ:= match i,l with
 | Sum.inl i, Sum.inr l=> cake ((whisper R).role (X i)) (X l) j M.val ((whisper R).cell (U i)) (U l)
 | i,l=> reality R M U X s j i l
local notation "Kr"=> myth R M U X (CSide m B) K.j
variable (t:∀ i,wheat (F i)= b)
private lemma chord_size (l:List α)(e: wheat l=b): Reflect.chord b= (if l.length%2=0 then 1 else Ω):=by
 rw [Hygrometry.wheat_grade] at e; rw [←e]; by_cases h:l.length%2=0 <;> unfold Reflect.chord <;> split_ifs <;> grind
include h k w t g
lemma startingPose : SpinPrice (changeM (m:=m) A 1 M) (poseX (whisper R) b (utter U X N 1 F v))= ∑ i:β,∑ j:β, star (v i)*thaw (tariff ∘ X) (reality R M U X (CSide m B) K.j) (F i) (F j)*v j:=by
 let L:= (whisper R); let s:= posted L U; let x:=Packed L X
 have he:= overhead A g k w M
 rw [Hygrometry.runCost L]; rw [SpinPrice.pool]; refine sum_congr rfl fun i _=>?_ ; rw [SpinPrice.pool]; apply sum_congr rfl; intro j _; rw [SpinPrice.cash]; change priceWeight X F v b i j * SpinPrice Σ (rollC (ton ∘ fun a=> player N (s a) 1 (x a)) (pairOrder (F i) (F j)))=_; rw [reckons M w.1 h he (fun a=>player (CSide m B) (s a) 1 (x a)) (fun _=>player_tones ..)]; unfold priceWeight thaw; rw [chord_size b _ (t i)]; change (ite _ _ _) * star (v i)* _ * veil (tariff ∘ X) _ * runes (K₀) (pairOrder (F i) (F j))= _; ring

omit h k w t g
variable [LinearOrder α][Fintype α] {RR:ℕ→ℝ}(N':ℕ→Side)(Q: Yard (fun i=>CSide (N' i) B) RR)(q:BudgetPoint)(𝒱:∀ i,Clear R K.j (U i))
local notation "Pk" => tariff ∘ X
-- syntax pollution V i
include h k p u Q g q w 𝒱
lemma payment_promise : 0 ≤ ∑ i:β,∑ j:β, star (v i)*thaw (tariff ∘ X) Kr (F i) (F j)*v j := by
 apply wick_honoured
 · intro i; exact tariff_ne_zero _
 · intro i j; exact coin_mirror A g h p u R M k w (X i) (X j) (U i) (U j)
 · intro i j; exact rank_flip ..
 apply sprite_nonneg; intro i; exact polar_refund A g h N' Q q R X U M.property 𝒱 i
omit h k p u Q g q w 𝒱
-- difference.One orientation.F.Price.D.Weights norm 1 from PAY.X. lemma independent of Grasp.General.
variable (x y:α⊕α→α⊕α→ℂ)
def rimeCost(κ:ℕ)(Z:ℝ):= (↑(2*κ+1:ℕ):ℝ)^(2*κ) * ((2*κ:ℕ):ℝ)* Z^(2*κ)
local notation "d"=> tariff ∘ X
local notation "Now" k:max =>∑ i,∑ j, star (v i)*thaw (tariff ∘ X) k (F i) (F j)*v j
private lemma veil_weight(l:List α): ‖veil (tariff∘X) l‖=1:=by induction l with| nil=>simp [veil]| cons i l ih=> rw [show veil (tariff∘X) (i::l)=tariff (X i)*veil (tariff∘X) l from rfl,norm_mul,ih, tariff_norm,mul_one]
lemma quota_lens (ε Z':ℝ) (p:1≤Z') (e: 0≤ ε)(Y:∀ i j,‖x i j‖ ≤ Z')(W:∀ i j,‖y i j‖ ≤ Z')(L:∀ i j,‖x i j-y i j‖ ≤ ε) (κ:ℕ)(h:∀ i, (F i).length ≤ κ): ‖(Now x)-(Now y)‖ ≤ rimeCost κ Z' * ε * (∑ i:β,‖v i‖)^2:=by
 let B0:=rimeCost κ Z' * ε; have h(i j:β) : ‖thaw d x (F i) (F j)-thaw d y (F i) (F j)‖≤ B0:=by
    unfold thaw; rw [← mul_sub,norm_mul,norm_mul (ite ..),veil_weight]; set t:= (if (F i).length%2=0 then (1:ℂ) else Ω); rw [show ‖t‖=1 from by unfold t; split <;> simp,mul_one,one_mul]
    have he: (pairOrder (F i) (F j)).length≤ 2*κ:=by simp only [pairOrder,List.length_append,List.length_map]; have i:=h i; have j:=h j; omega
    exact (ballots p e x y Y W L _ _ he).trans_eq (by unfold B0 rimeCost; ring)
 rw [←sum_sub_distrib]; refine (norm_sum_le ..).trans ?_; simp_rw [←sum_sub_distrib]; rw [sq]; set X':=(∑ i:β,‖v i‖); change _≤ B0*(X'*_); rw [←mul_assoc]; nth_rw 2 [mul_comm _ X']; -- fragile
 unfold X'; simp_rw [Finset.sum_mul,Finset.mul_sum]; refine sum_le_sum fun i _=> (norm_sum_le ..).trans (sum_le_sum fun j _=>?_); rw [←sub_mul,←mul_sub (star _),norm_mul,norm_mul,norm_star]; gcongr; exact h i j -- adjust ring order
end YM.CF.May.Floe
#print axioms YM.CF.May.Floe.payment_promise
#print axioms YM.CF.May.Floe.startingPose
#print axioms YM.CF.May.Floe.quota_lens
