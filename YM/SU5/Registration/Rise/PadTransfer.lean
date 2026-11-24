import YM.SU5.Registration.Rise.Handling
import YM.SU5.Six.TransitWall
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 220000
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
open Aria Set TopologicalSpace Metric

/-! # Reel at a positive allowance on the earlier mesh

Carry cap prices there to a SOT* (ManyF) approximation elsewhere. No assumption
that width-to-width equality of *endcaps* extends to *composed* norms. Here use
composition laws of the real (Eucl price units) slabs, with all the moves done on
the unprojected ColorHil. Then on the resulting engine take circumstances as needed
in ManyF. This is the back-transfer for the proof in the other direction. -/
open Casting Six
variable (P: Spine)(j:Axis) (x:P.Spectrum0 j)
local notation "T"=>timeMesh P.par
local notation "Φ"=> P.colorSpace j x
local notation "H"=> P.ColorHil j x
local notation "S"=> P.physicalEnergy j x
local notation "G"=> P.ManyF j x
local notation "U"=> P.truck j x
local notation "E"=> (S).E
local notation "EU"=> (P.seasons j x).E
local notation "ρ"=> P.wealth j x
local notation "μ"=> P.enter j x
local notation "M" s:max n:max=> whenly (timeMesh P.par) s n

/-- point-centered width j -/
def Apron.allowance (P:Spine)(j:Axis)(A:P.Apron):ℝ≥0:= whenly (timeMesh P.par) A.s (A.u j)
lemma Apron.width_real (D:P.Apron): D.realWidth P j=(D.allowance P j:ℝ):= natural_time .. -- A arg placement namespace? `(D)` type P root appears last, args order P j D.
lemma Apron.width_p (D:P.Apron): 0<D.allowance P j:= when_pos _ _ _ (D.pos j)
def stageH (A:P.Apron)(l r:ℝ≥0) : (H).Op:= E (l-A.allowance P j) * A.engine P j x * E (r-A.allowance P j)

private def canopy (H₁ H₂ : Hilbert)(R:H₁.space →L[ℂ] H₂.space) (Y:H₂.space →L[ℂ] H₁.space) : H₁.Op→L[ℂ]H₂.Op:= (ContinuousLinearMap.compL ℂ H₂.space H₁.space H₂.space R).comp ((ContinuousLinearMap.compL ℂ H₂.space H₁.space H₁.space).flip Y)
def toStageG : (P.ColorHil j x).Op→L[ℂ](P.ManyF j x).Op:= canopy H G (ρ) (μ).toContinuousLinearMap
def stageG (A:P.Apron)(l r:ℝ≥0) : (P.ManyF j x).Op:= P.toStageG j x (P.stageH j x A l r)

lemma stage_apply (B:(P.ColorHil j x).Op)(y:G) : P.toStageG j x B y = ρ (B (μ y)) := rfl
lemma toG_cost (B:(P.ColorHil j x).Op) : ‖P.toStageG j x B‖ ≤ ‖B‖:=by
 have hp: P.toStageG j x B=P.tableau j x 0 B:=by unfold tableau; rw [neg_zero,P.cart_zero]; rfl
 rw [hp]; exact P.tableau_pay ..
lemma bank_both (A:(H).Op)(t s:ℝ≥0) : P.toStageG j x (E t * A * E s)= EU t * P.toStageG j x A * EU s :=by
 ext1 v; -- change ensures casts
 change ρ (E t (A (E s (μ v))))= EU t (ρ (A (μ (EU s v))))
 rw [←P.soleHeat]; exact P.bankHeat ..
lemma charter_toG (A:(H).Op)(p:P.VMark): P.toStageG j x (P.charter j x p A)= P.cartage j x (P.laysM p) * P.toStageG j x A * P.cartage j x (P.laysM (-p)):=by
 ext1 v; change ρ (U p (A (U (-p) (μ v))))= P.cartage j x (P.laysM p) (ρ (A (μ (P.cartage j x (P.laysM (-p)) v))))
 rw [P.cart_and, P.uses_cart j x (P.laysM p)]; exact (P.roll_motion j x (p ∘ Subtype.val) _).symm -- from Solitaire; ]

lemma heater_both (t u s v:ℝ≥0)(A:(H).Op) : E (t+u)*A*E (s+v)=E t*(E u*A*E s)*E v:=by
 rw [show E (t+u)=E t*E u from (S).time t u, show E (s+v)=E s*E v from (S).time s v]; simp only [mul_assoc]
lemma charter_heat (B:(H).Op)(p:P.VMark)(t s:ℝ≥0) : P.charter j x p (E t* B * E s)= E t * P.charter j x p B * E s:=by
 ext1 v; change U p (E t (B (E s (U (-p) v))))=E t (U p (B (U (-p) (E s v))))
 simp only [P.sixWard_truck_heat]
lemma charter_rewind (B:(H).Op)(p:P.VMark) : P.charter j x (-p) (P.charter j x p B)=B:=by
 unfold charter; rw [neg_neg]; ext1 v; simp only [ContinuousLinearMap.comp_apply]
 have he(a:H): U (-p) (U p a)=a:= by rw [←ContinuousLinearMap.comp_apply,←P.truck_paves,neg_add_cancel,P.truck_zero]; rfl
 rw [he,he]
lemma heater_norm (t s:ℝ≥0)(A:(H).Op): ‖E t*A*E s‖ ≤ ‖A‖:= (norm_mul_le ..).trans ((mul_le_of_le_one_right (norm_nonneg _) ((S).shrinks _)).trans ((norm_mul_le ..).trans (mul_le_of_le_one_left (norm_nonneg _) ((S).shrinks _))))
lemma stage_scale_r (A:(H).Op)(t s:ℝ≥0)(z:ℂ): E t*(z • A)*E s=z • (E t*A*E s):=by rw [Algebra.mul_smul_comm,Algebra.smul_mul_assoc]
lemma stage_more (A:P.Apron) {t t' u u':ℝ≥0} (v:A.allowance P j≤t)(u₁:t≤t')(e:A.allowance P j≤u)(h:u≤u') : P.stageH j x A t' u'= E (t'-t)*P.stageH j x A t u * E (u'-u):=by
 unfold stageH
 set a:=A.allowance P j; rw [show t'-a=(t'-t)+(t-a) from (tsub_add_tsub_cancel u₁ v).symm,show u'-a=(u-a)+(u'-u) from ((tsub_add_tsub_cancel h e).symm.trans (add_comm (u'-u) _))] -- tune order
 exact P.heater_both ..
lemma stage_cheaper (A:P.Apron) {t t' u u':ℝ≥0} (v:A.allowance P j≤t)(u₁:t≤t')(e:A.allowance P j≤u)(h:u≤u') (z:ℂ) : ‖z • P.stageH j x A t' u'‖ ≤ ‖z • P.stageH j x A t u‖:=by rw [P.stage_more j x A v u₁ e h,← P.stage_scale_r]; exact P.heater_norm ..

variable (A:P.Apron) (s v:ℕ)(p:Cover)
local notation "d" => A.zoom P s j

-- integer fits permit. Point `P.meshPose s p j` is stamp center, not entire stencil.
-- compare [0,v] at level s and use symmetric allowance a at center, >=v suffices
structure StampHere : Prop where
 atMesh:A.s ≤ s
 climbs:(A.zoom P s j:ℤ) ≤ p j
 fits:p j+(A.zoom P s j:ℤ) ≤ v
-- conversions & consequences
lemma gives_here (e:A.s ≤ s)(t:A.realWidth P j≤ P.meshPose s p j)(k:P.meshPose s p j ≤ ((M s v):ℝ)-A.realWidth P j): P.StampHere j A s v p:=by
 rw [←A.zoom_bell P j s e] at t k; let x:=A.zoom P s j; have he:P.meshPose s p j=bell T s (p j):=rfl
 rw [he] at t k; have ht:bell T s ((x:ℤ)+p j) ≤ bell T s v:= by rw [bell_add,natural_time T s v]; exact (add_comm ..).trans_le ((le_sub_iff_add_le).mp k)
 exact ⟨e,(bell_le ..).1 t, le_trans ((add_comm _ (x:ℤ)).le) ((bell_le ..).1 ht)⟩
lemma StampHere.height (h:P.StampHere j A s v p): (p j).toNat=p j:= Int.toNat_of_nonneg ((Int.natCast_nonneg (d)).trans h.climbs)
lemma StampHere.rooms (h:P.StampHere j A s v p) : A.allowance P j ≤ M s (p j).toNat ∧ (M s (p j).toNat)+A.allowance P j ≤ M s v :=by
 have he: A.allowance P j=M s (d):=(matchR T A.s s (A.u j) h.atMesh).symm
 rw [he,←when_add]; have hp:= h.height P j A s v p
 have hN:= h.climbs; have hQ:= h.fits; exact ⟨(when_le ..).2 (by omega), (when_le ..).2 (by omega)⟩
lemma StampHere.center(h:P.StampHere j A s v p) : P.meshPose s p j=((M s (p j).toNat):ℝ):= (show bell T s (p j)=bell T s (p j).toNat from congrArg (bell T s) (h.height P j A s v p).symm).trans (natural_time ..)
local notation "ℓ"=> (p j).toNat
local notation "δ"=> (ℓ)-(d:ℕ)
local notation "r"=> v-((ℓ)+(d:ℕ))
local notation "X₀"=> P.chartAll p (A.full P s)
local notation "G₀"=> P.shifts j ((d:ℤ)-p j) (P.chartAll p (A.full P s))
variable (h:P.StampHere j A s v p)
local notation "η"=> (A.allowance P j)
local notation "α" => M s ((p j).toNat)
local notation "u!" => M s v
include h
lemma StampHere.restates : P.shifts j (δ:ℕ) (G₀) = X₀ ∧ (δ)+(d+d)+(r)=v:=by
 have h0:= h.height P j A s v p; have hi:=h.climbs; have hv:=h.fits; rw [P.shifts_sum]; exact ⟨by rw [show (((δ:ℕ):ℤ)+(↑(d:ℕ)-p j))=0 by omega,P.shifts_zero],by omega⟩
lemma StampHere.moneyL : M s (δ) = (α)-(η):=by
 have hN: A.allowance P j=M s (d):=(matchR T A.s s (A.u j) h.atMesh).symm
 rw [hN]; have hi: d≤(p j).toNat:=by have ht:=h.climbs; have he:= h.height P j A s v p; omega
 have he:(M s (δ))+(M s d)=(α):=(when_add T s ..).symm.trans (congrArg _ (tsub_add_cancel_of_le hi)); rw [← he,add_tsub_cancel_right]
lemma StampHere.moneyR : M s (r) = (u!)-((α)+(η)):=by
 have hN: A.allowance P j=M s (d):=(matchR T A.s s (A.u j) h.atMesh).symm
 have hi: (ℓ)+d≤v:= by have ht:= h.height P j A s v p; have hg:=h.fits; omega
 have he:(M s r)+(M s ((ℓ)+d))=(u!):=(when_add T s r _).symm.trans (congrArg (whenly T s) (tsub_add_cancel_of_le hi))
 rw [hN,←when_add,←he,add_tsub_cancel_right]
-- `transported` writes in integer door units here. Restate crossover of engine.
omit h
-- helpers to avoid paying for proof-irrelevance normalization of HUGE transported-card
-- expressions inside `E`, use (X) equality on P.Test with same s before expansion.
private lemma frame_identity {w:ℕ}(hw:0<w)(b:P.Card j s w){Y:P.Test}(hp:P.InCase j s w Y)(e:P.voxTest j s b.val=Y)(hq:P.voxTest j s b.val∈enclave P.calibration)
    (C:(P.ColorHil j x).Op) (h:C=(P.colorSpace j x) (P.door j s w hw b hq)): hp.charges x hw=C :=(congrArg (fun u:P.Physical j=> P.colorSpace j x u) (hp.cases_eq_door hw b e)).trans h.symm
private lemma fixesLeft (a b c:ℕ)(B Y:P.Test)(e:P.shifts j a Y=B)(x':v=a+c+b)(A₁ A₂:ℝ≥0)(p₁:A₁=M s a)(p₂:A₂=M s b)(g:P.InCase j s v B)(h₁:0<c)(h₂:0<v)
    (C:(P.ColorHil j x).Op)(w:P.InCase j s c Y)(u:w.charges x h₁=C):
    g.charges x h₂= E A₁ * C * E A₂ :=by
 refine (g.charges_eq x (w.padIn a b) rfl x' e.symm h₂).trans ((w.charges_pad x a b h₁).trans ?_)
 rw [u,p₁,p₂]
include h
lemma StampHere.presents {Z:P.Test}(e:Z=X₀) (hw:0<v) (c:P.InCase j s v Z):
    c.charges x hw= E ((α)-(η)) * P.charter j x (P.vtile s p) (A.engine P j x) * E ((u!)-((α)+(η))) :=by
 obtain ⟨b,g,gX,gC⟩:= A.transported P j x s h.atMesh p
 have hv:= A.zoomP P j s
 exact fixesLeft P j x s v (δ) (r) ((d)+(d)) Z (G₀) ((h.restates P j A s v p).1.trans e.symm) (h.restates P j A s v p).2.symm _ _ (h.moneyL P j A s v p).symm (h.moneyR P j A s v p).symm c (add_pos hv hv) hw _ (InCase.ofVox P j b g gX) (frame_identity P j x s _ b (InCase.ofVox P j b g gX) gX g _ gC)
-- solve for `stageH` by spending the remaining margins, real semigroup. >= total V.
lemma StampHere.cashed {Z:P.Test}(e:Z=X₀) (hw:0<v) (c:P.InCase j s v Z) (t:ℝ≥0) (u:u! ≤ t):
    P.stageH j x A t t=P.charter j x (-(P.vtile s p)) (E (t-(α)) * (c.charges x hw)* E (t+(α)-(u!))):=by
 obtain ⟨he,hy⟩:= h.rooms P j A s v p
 let a:= t-(α); let b:=t+(α)-(u!); let x₁:= (α); let s':=(u!)
 have h₁: (α) ≤ t:= le_trans (le_add_of_nonneg_right (show 0≤η from by positivity)) (le_trans hy u)
 have ha:a+(x₁-(η))=t-(η):= tsub_add_tsub_cancel h₁ he
 have hb:s'-(x₁+(η))+b=t-(η):= by
    unfold b s'; change (u!)-(α+η)+(t+(α)-(u!))=_; rw [add_comm _ (t+(α)-(u!))]; rw [tsub_add_tsub_cancel (le_trans u (le_add_of_nonneg_right (show 0≤α from by positivity))) hy]; apply tsub_eq_tsub_of_add_eq_add; abel
 rw [h.presents P j x A s v p e hw c, ←P.heater_both,← P.charter_heat, ha,hb,P.charter_rewind]; rfl
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms Spine.StampHere.cashed
#print axioms Spine.stage_cheaper
#print axioms Spine.charter_toG
#print axioms Spine.bank_both
