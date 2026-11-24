import YM.SU5.Voyager.Cinder
import YM.SU5.Voyager.Shine
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
variable (j) (k:Axis)
-- spacetime regulator apparatus
lemma cart_sum (g f:Vantage): W[j] (g+f)= W[j] g * W[j] f:=cart_paves ..
lemma cart_adj (g:Vantage):star (W[j] g)= W[j] (-g):=by
 -- API
 exact P.cart_reverses ..
lemma cart_comm (g r:Vantage): Commute (W[j] g) (W[j] r):=by change W[j] _*_=W[j] _*_; rw [←cart_sum,←cart_sum,add_comm]
variable (r y:Vantage)(B D:P.Apron)(J:P.Ellis a x)
variable (t g:ℝ≥0)(n:ℕ)
local notation "φ"=> flashY x B j
local notation "ψ"=> flashY x D j
local notation "ρ"=> aislePt k (g:ℝ)
local notation "Ψ₀"=> flashY x D k
local notation "μ"=> glareY x (B.kiss P j) k
local notation "Q[" r "]"=> (W[k] (roseTail j B D r t) Ψ₀)
local notation "G[" υ "," ν "]"=> (Apron.realWidth P υ k + Apron.realWidth P ν k)
local notation "l[" r "]"=> Real.toNNReal (r k-G[B,D])
-- spacing
private lemma further (h:k≠j): roseTail j B D (r+ρ) t=roseTail j B D r t+ρ:=by
 funext i; by_cases h':i=j
 · subst i; simp [aislePt,roseTail,h,Ne.symm h]
 simp [roseTail,h']
def deltaMove(r:Vantage): (P.ManyF j χ[j]).Op:= W[j] r - 1
lemma deltaSum : deltaMove j x r= W[j] r-1:=rfl -- j arg position?
lemma delta_norm (z:H[j]): ‖deltaMove j x y z‖ ≤ 2*‖z‖:= by change ‖W[j] y z-z‖≤_; exact (norm_sub_le ..).trans_eq (by rw [P.cart_norm]; ring)
lemma delta_commute : Commute (W[j] r) (deltaMove j x y):= (cart_comm j x ..).sub_right (Commute.one_right ..)
lemma delta_shadow (t:ℝ≥0): Commute (E[j] t) (W[j] r):= shiftP x j t r r (fun _ _=>rfl) -- shiftP arg
local notation "Δ"=> deltaMove j x
variable (h:k≠j)
include J h
lemma mayFlash (ht:0<t)(hu:G[B,D]<r k):
   inner ℂ φ ((E[j] t * W[j] r * (Δ ρ)^n) ψ)=inner ℂ μ ((E[k] l[r] * (E[k] g-1)^n) Q[r]):=by
 induction n generalizing r with
 | zero=> rw [pow_zero,mul_one,pow_zero,mul_one]; exact flash_tail j x B D k r t J h hu ht -- arg
 | succ n ih=>
   have he: W[j] r * ((Δ ρ)^(n+1)) = W[j] (r+ρ) * ((Δ ρ)^n)- W[j] r * ((Δ ρ)^n):=by rw [pow_succ', ← mul_assoc,deltaSum,mul_sub,mul_one,←cart_sum,_root_.sub_mul]
   have hy:(r+ρ) k=r k+(g:ℝ):=by simp [aislePt];
   have hp:G[B,D]<(r+ρ) k:=by rw [hy]; linarith [g.property]
   rw [mul_assoc (E[j] _), he, mul_sub, ← mul_assoc (E[j] _), ← mul_assoc (E[j] _),ContinuousLinearMap.sub_apply, inner_sub_right, ih r hu, ih (r+ρ) hp]
   have hg:l[(r+ρ)] =l[r]+g:= by rw [hy, show r k+(g:ℝ)-G[B,D]=r k-G[B,D]+(g:ℝ) from (by ring)]; exact (Real.toNNReal_add (sub_nonneg.mpr hu.le) g.property).trans (congrArg (l[r] + ·) (Real.toNNReal_coe))
   have hh: Q[(r+ρ)] = Q[r]:= by rw [further j k r B D t g h, P.cart_paves, P.cart_aisle, ContinuousLinearMap.comp_id] --fix argument includes P implicit and x?
   have hx: E[k] (l[r]+g)*(E[k] g-1)^n-E[k] l[r]*(E[k] g-1)^n=E[k] l[r]*(E[k] g-1)^(n+1):=by rw [← _root_.sub_mul,pow_succ',← mul_assoc,mul_sub,mul_one]; congr; exact (Ψ[k]).time ..
   rw [hh,hg, ←inner_sub_right, ←ContinuousLinearMap.sub_apply,hx]
def quality (g:ℝ≥0)(t:ℝ)(n:ℕ):ℝ:= (2*(g:ℝ)*n/t)^n
lemma flash_cost (ht:0<t)(hu:G[B,D]<r k):
  ‖inner ℂ φ ((E[j] t * W[j] r * (Δ ρ)^n) ψ)‖ ≤ (‖μ‖*‖Ψ₀‖)*quality g (r k-G[B,D]) n:=by
 rw [mayFlash j x k r B D J t g n h ht hu]; let T:= E[k] l[r] * (E[k] g-1)^n
 have hc:0<r k-G[B,D]:=sub_pos.mpr hu
 have hv: ‖T‖ ≤ quality g (r k-G[B,D]) n:=by
    have he:=OS.Semigroup.Plate.many_climbs (Ψ[k]) l[r] g n (Real.toNNReal_pos.mpr hc); rwa [Real.coe_toNNReal _ hc.le] at he
 refine (norm_inner_le_norm ..).trans ((mul_le_mul_of_nonneg_left ((T.le_opNorm Q[r]).trans (mul_le_mul_of_nonneg_right hv (norm_nonneg _))) (norm_nonneg _)).trans_eq ?_)
 rw [P.cart_norm]; ring
omit J h
lemma delta_sum(x' z:H[j]): inner ℂ x' (E[j] t (W[j] (r+y) z))-inner ℂ x' (E[j] t (W[j] r z))=inner ℂ x' (E[j] t (W[j] r (Δ y z))):=by
 change _= inner ℂ x' (E[j] t (W[j] r (W[j] y z-z))); rw [P.cart_paves, ContinuousLinearMap.comp_apply,map_sub,map_sub,inner_sub_right]
lemma sales(t:ℝ≥0)(B':Flicker P) (w:H[j]) : inner ℂ (specY x j B') (E[j] t w) = inner ℂ (flashY x B'.1 j) (E[j] (B'.2.val+t) w):= by unfold specY; rw [OS.Semigroup.swing, OS.Semigroup.time]; rfl
lemma geared{u:ℝ≥0} (z:H[j]): (E[j] u) (W[j] r ((Δ y ^ n) z))= W[j] r ((Δ y ^ n) (E[j] u z)):= by
 let h':= ((delta_shadow j x r u).mul_right (((delta_shadow j x y u).sub_right (Commute.one_right ..)).pow_right n)) -- subs via rfl
 change (((E[j] u)*(W[j] r*(Δ y)^n)) z)=(((W[j] r*(Δ y)^n)*E[j] u) z)
 exact DFunLike.congr_fun h'.eq _
lemma salesR(F D:Flicker P) : inner ℂ (specY x j F) ((E[j] t * W[j] r * (Δ y)^n) (specY x j D)) = inner ℂ (flashY x F.1 j) ((E[j] (F.2.val+t+D.2.val) * W[j] r * (Δ y)^n) (flashY x D.1 j)):=by
 let u:= D.2.val; let ψ':= flashY x D.1 j; let w:= Δ y ^ n
 change inner ℂ _ (E[j] t (W[j] r (w (E[j] u ψ'))))= inner ℂ _ (E[j] (F.2.val+t+D.2.val) (W[j] r (w ψ')))
 rw [sales j x, ← geared j x r y n, OS.Semigroup.time (Ψ[j]) (F.2.val+t) D.2.val]; rfl
include J h
local notation "φ[" F "]"=> specY x j F
local notation "gain[" F "," B "]"=> (‖glareY x (Apron.kiss P j (Prod.fst F)) k‖ * ‖flashY x (Prod.fst B) k‖)
lemma earn (F B:Flicker P) (p:G[F.1,B.1]<r k): ‖inner ℂ φ[F] ((E[j] t * W[j] r * (Δ ρ)^n) φ[B])‖≤ gain[F,B]*quality g (r k-G[F.1,B.1]) n:=by
 have hv:0<F.2.val+t+B.2.val:= add_pos_of_nonneg_of_pos (by positivity) B.2.property
 rw [salesR]; exact flash_cost j x k r F.1 B.1 J _ g n h hv p
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.earn
