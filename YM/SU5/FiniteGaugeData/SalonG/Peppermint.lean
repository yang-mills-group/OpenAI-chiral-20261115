import YM.SU5.FiniteGaugeData.SalonG.Sortie
set_option autoImplicit false
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock Pastry Satin
open Reed (Fine)
attribute [local instance] opCStarAlgebra
namespace SalonG
open Nacre Heat Charm Chrono Journey
set_option quotPrecheck false
section papyrus
variable (K:Calibration)(m:Side)(a:Axis)
variable {L:Loom (K.c m)} {D:ℝ} {X:W K→ₗ[ℂ]ℂ}
local notation "N"=> (K.c m)
local notation "φ"=> (K.c m).val
local notation "Ω"=> Equity K m L X D
local notation "η"=> K.ℓ
abbrev headland (K:Calibration)(r:ℕ):= yard K (r+K.ℓ+1)
abbrev canal (K:Calibration)(r:ℕ):= 2*headland K r + r
abbrev endurance (K:Calibration)(r:ℕ):= 2 *(canal K r)+addgap K+(r+K.ℓ+1)
variable (E:Equity K m L X D)
variable {x y z t u:W K}{S T:Finset Cover}{r d n:ℕ}
include E
lemma Equity.house {B:ℝ}(t:Locator K x S)(w:RealWidth K x m B)(e:∀ i:Axis, rest K m (region S (K.c m)) i r)(p:r+addgap K ≤ (K.c m).val): ‖X x‖ ≤ Real.exp (D*((2*(r+addgap K):ℕ):ℝ)^4)*B:= by
 obtain ⟨X',e',v⟩:= E.pays; rw [← v]; exact (e'.homestead e p ((show InTest _ _ _ _ _ from t).support m)).trans (mul_le_mul_of_nonneg_left w.cashW (Real.exp_pos _).le)
local notation "φ₀"=> (φ:ℤ)
local notation "J"=> headland K r
local notation "J₀"=> (headland K r:ℤ)
local notation "D'"=> canal K r

omit E
lemma fundedQ : r+K.ℓ ≤ headland K r:=by unfold headland yard; have he:= tic_pos K; nlinarith
lemma effC (v:endurance K r ≤ (K.c m).val): headland K r + r + K.ℓ ≤ (K.c m).val ∧ 2*canal K r+addgap K≤ (K.c m).val:=by unfold endurance canal at *; have he:= fundedQ (r:=r) K; omega
lemma rearLevel (d:ℕ): Level K (yard K d) := by
 refine ⟨2*(d:ℤ),?_⟩; rw [yard_ice]; unfold gaugeShift; ring
lemma sum_level {n x:ℤ}(p:Level K n)(t:Level K x): Level K (n+x):=by
 obtain ⟨i,rfl⟩:=p; obtain ⟨j,rfl⟩:=t; exact ⟨i+j,by unfold gaugeShift; ring⟩
lemma proceedLevel (d n:ℕ) : Level K (proceed K n d):=by induction n with
 | zero=> rw [proceed,mul_zero,Nat.cast_zero]; exact level_zero K
 | succ n ih=> rw [proceed_succ,Nat.cast_add]; exact sum_level K ih (rearLevel K d)
structure Peck (K:Calibration)(m:Side)(a:Axis)(q:ℤ)(r:ℕ)(S:Finset Cover) : Prop where
 main : Cardboard K m a q r S
 cross : ∀ i≠a, Cardboard K m i 0 r S -- only centered at 0!
local notation "A"=> Peck K m a
namespace Peck
variable {K m a}
lemma raises_p {x y:ℤ}(p:Peck K m a x r S)(h:(y:Per (More (K.c m)))=x) : Peck K m a y r S:= ⟨p.main.raises h,p.cross⟩
lemma monoP {x y:ℤ}(p: Peck K m a x r S)(e:y-(d:ℤ) ≤ x-(r:ℤ))(v:x+(r:ℤ) ≤ y + (d:ℤ)): Peck K m a y d S:= ⟨p.main.monoC e v,fun i f=> (p.cross i f).monoC (by omega) (by omega)⟩
lemma peck_refl {x:ℤ}(p:Peck K m a x r S)(q:ℤ): Peck K m a (2*q-x) r (refract a q S):=⟨p.main.reflector0 _,fun i h=>(p.cross i h).cross h.symm _⟩
lemma conjP {x:ℤ}(p:Peck K m a x r S)(t:Peck K m a x r T): Peck K m a x r (S∪T):= ⟨p.main.conjU t.main,fun i e=>(p.cross i e).conjU (t.cross i e)⟩
lemma apport {z:ℤ}(p:Peck K m a z r S) (i:Axis): rest K m (region S (K.c m)) i (2*r):=by
 by_cases he:i=a; · subst i; exact p.main.ledger
 exact (p.cross i he).ledger -- indentation fragile
-- square costs, wing=j+ shift
lemma station_p {q:ℤ} (p:Peck K m a q r S): Peck K m a q (canal K r) (S∪refract a (q+ (headland K r:ℤ)) S):= by
 apply conjP (p.monoP _ _) ((p.peck_refl _).monoP _ _) <;> unfold canal<;> omega
lemma across_p {q:ℤ} (j:ℤ)(p: Peck K m a (q+(K.c m).val) r T) : Peck K m a (2*j-(q:ℤ)+ ↑(K.c m).val) r (refract a j T):= by
 refine (p.peck_refl j).raises_p ?_; rw [show 2*j-q+φ₀=2*j-(q+φ₀)+φ₀*2 from by ring,Int.cast_add,more_zero,add_zero]
lemma stationN_p {q:ℤ}(p:Peck K m a (q+(K.c m).val) r S): Peck K m a (q+(K.c m).val) (canal K r) (refract a (q+ (headland K r:ℤ)) S∪S):= by
 apply conjP ((p.across_p _).monoP _ _) (p.monoP _ _) <;> unfold canal <;> omega
end Peck
private lemma plusD (r:ℕ){q:ℤ}(e:Level K q): Level K (q+(headland K r:ℤ)):= sum_level K e (rearLevel K (r+ η+1))
variable (r) in
abbrev TellerC (K:Calibration)(D:ℝ):= Real.exp (D*((2*(2*canal K r +addgap K):ℕ):ℝ)^4)
variable {K m}
include E
lemma Equity.maximal {q:ℤ}(e:Level K q)(v:endurance K r ≤ (K.c m).val) {B C:ℝ} (p: Peck K m a q r S) (t: Peck K m a (q+(K.c m).val) r T) (X':Locator K x S)(Y':Locator K y T)(h:RealWidth K x m B)(b:RealWidth K y m C):
    ‖X (x*y)‖^2 ≤ (TellerC r K D)*(B*B)*((TellerC r K D)*(C*C)) := by
 let z:= q+ (headland K r:ℤ)
 have he:= effC K m v; have hx:=fundedQ (r:=r) K
 have hv:= E.separated K m a z X (plusD K r e) X' Y' (p.main.beforeL (x:=z) (by unfold z; omega) (by unfold z; omega)) (t.main.afterL (x:=z) (by unfold z; omega) (by unfold z; omega)); -- syntax
 refine hv.trans ?_; have hp':= p.station_p; have ht':= t.stationN_p (q:=q)
 refine mul_le_mul (house K m E (locate_join _ _ (locate_sub _ X' subset_union_left) (locate_sub _ (locate_cold K S a z X') subset_union_right)) (h.mule (h.reflected a z)) hp'.apport he.2) (house K m E (locate_join _ _ (locate_sub _ (locate_cold K T a z Y') subset_union_left) (locate_sub _ Y' subset_union_right)) ((b.reflected a z).mule b) ht'.apport he.2) (norm_nonneg _) (mul_nonneg (Real.exp_pos _).le (mul_self_nonneg B))

lemma Equity.convoy {C:ℝ}(e:PaidSpan K m d n)(v:Ahead a 0 K.ℓ S)(t:Locator K x S)(h:RealWidth K x m C)(p:endurance K (Ran (d:=d) (T:=S) K) ≤ (K.c m).val):
    let w:=wagon K a d n x; let r:=Fold K a 0 w w
    let B:= TellerC (Ran (d:=d) (T:=S) K) K D * ((C*C)*(C*C))
    ‖X (Fold K a (proceed K n d) r r)‖ ≤ B := by
 intro w r B
 let q := ((proceed K n d):ℤ); let T:= rear K a d n S; let U := refract a 0 T; let r':= Ran K (T:=S) (d:=d)
 have hT:Peck K m a q r' T:= ⟨east_r K m a,fun i f=> ((grace K m i S).deduct (a:=a) (Ne.symm f) (d*(n+2):ℕ)).monoC (by unfold r' Ran; omega) (by unfold r' Ran; omega)⟩; have hU:Peck K m a (q+(K.c m).val) r' U:= ⟨west_r K m a e,fun i f=> (hT.cross i f).cross (Ne.symm f) _⟩ -- later west_r doesn't require t? check
 have h₁:Peck K m a q r' (refract a q T ∪ T) := by
    apply Peck.conjP _ hT; convert hT.peck_refl q using 1<;> omega
 have h₂:Peck K m a (q+(K.c m).val) r' (refract a q U ∪ U):= by
    apply Peck.conjP _ hU; convert hU.across_p q using 1<;> omega
 let u:= fire K a 0 w
 have hx:Locator K w T:= loc_tic K S a _ t; have ht:= locate_cold K T a 0 hx
 have hz := helve_loc (K:=K) a hx hx -- same at 0 U
 have ht' {Z}{f:W K}(u:Locator K f Z): Locator K (Fold K a q f f) (refract a q Z∪ Z):= locate_join K _ (locate_sub K (locate_cold K Z a q u) subset_union_left) (locate_sub K u subset_union_right)
 have hw:RealWidth K w m C:= h.tick a _
 have bv {z:W K}(t:RealWidth K z m C): RealWidth K (Fold K a q z z) m (C*C) := (t.reflected a q).mule t
 have hp : Fold K a q r r=Fold K a q w w* Fold K a q u u:=by
    change fire K a q (u*w)*_= _; unfold r Fold; change fire K a q (u*w)*(u*w)=fire K a q w * w * (fire K a q u*u); rw [ice_join]; rw [commW K (fire K a q u) (fire K a q w),commW K u w]; exact Commute.mul_mul_mul_comm (b:=fire K a q u) (commW _ _ _) _ _
 have hB:0≤B:= mul_nonneg (Real.exp_pos _).le (mul_self_nonneg _); refine (sq_le_sq₀ (norm_nonneg _) hB).mp ?_; rw [show (proceed K n d:ℤ) = q from rfl,hp, sq B]; exact E.maximal a (proceedLevel K d n) p h₁ h₂ (ht' hx) (ht' ht) (bv hw) (bv (hw.reflected a 0))
end papyrus
#print axioms Equity.convoy
end SalonG
end YM.CF.Buffered.Afterglow.Hierarchy
