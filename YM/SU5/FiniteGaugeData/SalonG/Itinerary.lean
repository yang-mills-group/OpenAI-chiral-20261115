import YM.SU5.FiniteGaugeData.SalonG.JourneyL
set_option autoImplicit false
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock Pastry Satin
open Reed (Fine)
attribute [local instance] opCStarAlgebra
open Py Py.Rate LocalLimit Preparation Journey Fiber Vale VolumeCape FullBill
set_option quotPrecheck false
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(h:Real.exp 1≤ Λ.x)
local notation "Kₜ"=> tent Y h
local notation "N₁" i:max s:max=> side Y i s
local notation "Wₐ" i:max s:max => (Y.voyage i).CapeT s
local notation "D₀"=> aliasLaw Λ
local notation "D₁"=> distanceLaw l
local notation "L₁"=> Λ.R.L
local notation "C₀"=> (VolumeCape.Dream.plot l).C
local notation "Xᵣ" i:max k:max=> (Y.voyage i).X (Y.uv k)
local notation "Tᵣ" i:max k:max s:max=> ((Y.voyage i).X (Y.uv k)).gram s
variable (S T: Finset Cover)(s i k:ℕ)
open Nacre Heat Charm Chrono Journey
namespace SalonG
variable (d n e:ℕ)(a:Axis) -- d width, n resolution steps, e train height
abbrev seriesQ (Λ:Preparation)(l:ℕ)(S:Finset Cover): ℕ → Finset Cover
 | 0=> S
 | n+1=> GridStep Λ l (seriesQ Λ l S n)
local notation "Z" n:max=> seriesQ Λ l S n
abbrev streamQ (s:ℕ)(S:Finset Cover)(P: Call Λ l): (n:ℕ)→ Catalog S →L[ℂ] Catalog (seriesQ Λ l S n)
 | 0=> ContinuousLinearMap.id ℂ (Catalog S)
 | n+1=> (P (seriesQ Λ l S n) (s+n)).comp (streamQ s S P n)
-- Sharp at EACH entry offers all. default 0 transition when fail
abbrev Reservations (i k:ℕ) : Call Λ l:= fun u e=> snag Y h u e i k
abbrev Pension (S:Finset Cover)(s i k n:ℕ) : Catalog S →L[ℂ] Catalog (seriesQ Λ l S n) := streamQ s S (Reservations Y h i k) n
abbrev energyS (Λ: Preparation) (d n:ℕ) := Λ.R.L.val^n*d
lemma energy_zero : energyS Λ d 0=d:= by unfold energyS; rw [pow_zero,one_mul]
lemma energy_step : energyS Λ d (n+1) = Λ.R.L.val*energyS Λ d n:= by unfold energyS; rw [pow_succ',mul_assoc]
lemma series_geo (v:Studio a 0 (yard Kₜ d) (reserve Λ l) S): Studio a 0 (yard Kₜ (energyS Λ d n)) (reserve Λ l) (seriesQ Λ l S n):=by
 induction n with
 | zero => rw [energy_zero]; exact v
 | succ n ih=> have hx:= ih.grow; rw [mul_zero] at hx; rw [energy_step,yard_mul (K:=Kₜ),Nat.cast_mul]; exact hx
variable (f:W (tent Y h))(p:Locator (tent Y h) f S)
-- working catalogue for all steps, even at off-offer entries (zero then purchases of zero).
include p in
lemma dealers : Tint.Durable Kₜ (composeQ Kₜ (Z n) (Pension Y h S s i k n (reading Kₜ S f p))) := by
 induction n with
 | zero=> change Tint.Durable Kₜ (composeQ Kₜ S (reading Kₜ S f p)); rw [reading_p]; exact (well_for Kₜ f).2
 | succ n ih=>
    let z:=(Pension Y h S s i k n) (reading Kₜ S f p)
    change Tint.Durable Kₜ (composeQ Kₜ (Z (n+1)) (snag Y h (Z n) (s+n) i k z)); classical
    by_cases u:Offered Y (Z n) (s+n) i k
    · exact Tint.snag_durable Y h (Z n) (s+n) i k u z ih
    rw [show snag Y h (Z n) (s+n) i k=0 from dif_neg u,ContinuousLinearMap.zero_apply,map_zero]; exact (allG Kₜ).zero_mem
abbrev sparkle : Catalog (seriesQ Λ l S n):= (Pension Y h S s i k n) (reading Kₜ S f p)
def Passenger : W (tent Y h):= ⟨composeQ Kₜ (Z n) (sparkle Y h S s i k n f p),⟨compose_test ..,dealers Y h S s i k n f p⟩⟩
lemma ride_loc : Locator Kₜ (Passenger Y h S s i k n f p) (Z n):= compose_t ..
lemma board_stamp : reading Kₜ (Z n) (Passenger Y h S s i k n f p) (ride_loc ..)=Pension Y h S s i k n (reading Kₜ S f p):= compose_inj (Z n) Kₜ (reading_p ..)
lemma join_step (u:Offered Y (seriesQ Λ l S n) (s+n) i k): joinV Y h (s+n) i k (Passenger Y h S s i k n f p) (Passenger Y h S s i k (n+1) f p):= by
 let z:=sparkle Y h S s i k n f p; change ingress Y (s+n) i k (sold Y h (s+n) i (composeQ Kₜ (Z n) z))= sold Y h (s+n+1) i (composeQ Kₜ _ (snag Y h (Z n) (s+n) i k z)); rw [snag_pay Y h (Z n) (s+n) i k u, transitionQ_apply,exchanged]
local notation "H" n:max=> energyS Λ d n
abbrev projectR :Prop:= ∀ u < n, Offered Y (seriesQ Λ l S u) (s+u) i k
local notation "N" n:max=>side Y i (s+n)
lemma season (C: PaidSpan (tent Y h) (momentm Y i s) d e): PaidSpan (tent Y h) (momentm Y i (s+n)) (energyS Λ d n) e:= by
 induction n with
 | zero=> rw [energy_zero]; exact C
 | succ n ih=>
    have hs:(side Y i (s+n+1)).val=(Λ.R.L.val)*(side Y i (s+n)).val:= (sized Y _ _).trans (mul_comm ..)
    have he:= ih.lower; have hr:= ih.upper; rw [show (tent Y h).c (momentm Y i (s+n))=side Y i (s+n) from terrain Y h (Y.ir i) (s+n)] at he hr
    rw [energy_step]; constructor; all_goals rw [show (tent Y h).c (momentm Y i (s+(n+1)))=side Y i (s+n+1) from terrain Y h (Y.ir i) (s+n+1),hs,proceed_step];
    · exact le_trans (le_of_eq (by ring)) (Nat.mul_le_mul_left (Λ.R.L.val) he)
    rw [yard_mul]; exact (Nat.mul_le_mul_left (Λ.R.L.val) hr).trans (le_of_eq (by ring))
lemma passenger_zero : Passenger Y h S s i k 0 f p=f:= Subtype.ext (reading_p Kₜ S f p)
lemma ledgerL (C: PaidSpan (tent Y h) (momentm Y i s) d e) (t:Studio a 0 (yard Kₜ d) (reserve Λ l) S) (u:projectR Y S s i k n):sharp Y h s i k (CarrierF a d e f).val=sharp Y h (s+n) i k (CarrierF a (energyS Λ d n) e (Passenger Y h S s i k n f p)).val:=by
 induction n with
 | zero=> rw [passenger_zero,energy_zero]; rfl
 | succ n ih=>
    have he:=u n (by omega); have ht:=(season Y h s i d n e C).lower; rw [show (tent Y h).c (momentm Y i (s+n))=side Y i (s+n) from terrain Y h (Y.ir i) (s+n)] at ht; rw [energy_step]; exact Eq.trans (ih (fun i t=>u _ (by omega))) (Transit.let_carrier Y h (s+n) i k a he (ride_loc ..) (series_geo Y h S d n a t) (join_step Y h S s i k n f p he) ht)

abbrev bridgesK (S:Finset Cover)(s:ℕ): ℕ→ℝ
 | 0=>1
 | n+1=> salary Y h (seriesQ Λ l S n) (s+n)*bridgesK S s n
local notation "C"=> bridgesK Y h S s
lemma bridgesK_nn : 0 ≤ bridgesK Y h S s n:=by induction n with
 | zero=> exact zero_le_one
 | succ n ih=>exact mul_nonneg (salary_nn Y h _ _) ih
lemma bridge_width : ‖Pension Y h S s i k n‖≤ bridgesK Y h S s n:= by
 induction n with
 | zero=> exact ContinuousLinearMap.norm_id_le
 | succ n ih=> exact (ContinuousLinearMap.opNorm_comp_le ..).trans (mul_le_mul (snag_size Y h _ _ i k) ih (norm_nonneg (Pension Y h S s i k n)) (salary_nn Y h (Z n) (s+n)))
lemma passenger_width {C':ℝ}(b:‖reading Kₜ S f p‖≤ C') : SalonG.Width Kₜ (Passenger Y h S s i k n f p) (duration (Z n)*(bridgesK Y h S s n*C')):= fun i' v=> (width_read (ride_loc Y h S s i k n f p) i' v).trans (mul_le_mul_of_nonneg_left (by rw [board_stamp]; exact (ContinuousLinearMap.le_opNorm ..).trans (mul_le_mul (bridge_width Y h S s i k n) b (norm_nonneg _) (bridgesK_nn Y h S s n))) (duration_pos _).le)

-- limit P iteration (independent of S)
variable {v u:ℕ→ℕ}{I:ℕ→Family (tent Y h)→ℕ→ℂ}{E:ℕ→ Family (tent Y h)→ℂ}{P:Call Λ l}{J:Wicket Λ l}
variable (W':Universal Y h u v I E)(R:Rolled Y h u v J P)
include W' R
def companion : W (tent Y h)→ₗ[ℂ] W (tent Y h) where
 toFun x:= Charm.next Y h s W' R x
 map_add' x y:= next_sum ..
 map_smul' c x:= next_smul ..
def ascended : ℕ→ W (tent Y h) →ₗ[ℂ] W (tent Y h)
 | 0=> LinearMap.id
 | n+1=> (companion Y h (s+n) W' R).comp (ascended n)
lemma ascend_cert : (ascended Y h s W' R n f).val=composeQ Kₜ (Z n) (streamQ s S P n (reading Kₜ S f p)):=by
 induction n with
 | zero=> exact (reading_p Kₜ S f p).symm
 | succ n ih=> exact next_cert Y h (Z n) (s+n) W' R _ (show InTest _ _ _ _ _ from (ih.symm ▸ compose_t (Z n) (tent Y h) (streamQ s S P n (reading Kₜ S f p)))) _ ih.symm
include p in
lemma ascend_loc : Locator Kₜ (ascended Y h s W' R n f) (seriesQ Λ l S n):=by unfold Locator; rw [ascend_cert Y h S s n f p W' R]; exact compose_t ..
lemma ascent_reads : reading Kₜ (Z n) (ascended Y h s W' R n f) (ascend_loc Y h S s n f p W' R)= streamQ s S P n (reading Kₜ S f p):= by apply compose_inj (Z n) Kₜ; rw [reading_p, ascend_cert Y h S s n f p W' R]

-- Cts linear asympt lens
lemma streamG (u':ℕ→ℕ) (p:eligiblePath Y u v u') : Tendsto (fun i=> Pension Y h S s (u i) (v (u' i)) n) atTop (𝓝 (streamQ s S P n)):= by
 induction n with
 | zero => exact tendsto_const_nhds
 | succ n ih=> exact ((show Continuous (fun (p : Slip Λ l (Z n) × (Catalog S →L[ℂ] Catalog (Z n)))=> p.1.comp p.2) from continuous_fst.clm_comp continuous_snd).tendsto _).comp ((calls Y h (Z n) (s+n) R u' p).prodMk_nhds ih)
lemma streams (ε:ℝ)(v':0<ε): ∀ᶠ i in atTop, ∀ k:ℕ, legacy Y (u i) (v k)→ projectR Y S s (u i) (v k) n ∧ ‖Pension Y h S s (u i) (v k) n - streamQ s S P n‖ ≤ ε := by
 filter_upwards [(eventually_all_finset (range n)).mpr (fun j _=> often_offer Y h (Z j) (s+j) W'), path_budget (T:=Catalog S→L[ℂ] Catalog (Z n)) (w:=v) (z:=streamQ s S P n) (A:=fun i k=>Pension Y h S s i k n) Y W'.pick.grow_k (streamG Y h S s n W' R) ε v'] with i hv v k p; exact ⟨fun j t=>hv j (mem_range.mpr t) k p,(v k p).le.trans_eq' (dist_eq_norm _ (streamQ s S P n))⟩
lemma limit_width : ‖streamQ s S P n‖ ≤ bridgesK Y h S s n:= by obtain ⟨b,p⟩:=eligible_exists Y u v W'.pick.grow_k; exact le_of_tendsto (((continuous_norm (E:=Catalog S→L[ℂ] Catalog (Z n))).continuousAt (x:=streamQ s S P n)).tendsto.comp (streamG Y h S s n W' R b p)) (Eventually.of_forall (fun i=> bridge_width Y h S s (u i) (v (b i)) n))
#print axioms ledgerL
#print axioms ascend_loc
#print axioms streamG
end SalonG
end YM.CF.Buffered.Afterglow.Hierarchy
