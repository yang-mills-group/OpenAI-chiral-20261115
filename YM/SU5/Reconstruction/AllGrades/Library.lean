import YM.SU5.Reconstruction.AllGrades.SchoolHall
/-! # Unconditional procurement at the chosen character. Takes leads on even ROOT only, costs on both grades. -/
-- Header
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 5000
set_option synthInstance.maxSize 32000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.FirstWindows.QuantaFields
open Function Set Filter NormedSpace Lattice Wilson Cube MeasureTheory Reflect Advance
  Scroll Skye Window Journey Satin Tapestry
open Vacancy Selected SatinVerification Py Py.Rate LocalLimit Preparation
open scoped Topology BigOperators ComplexOrder InnerProductSpace NNReal ENNReal Classical

attribute [local instance] opCStarAlgebra
open SlabMark MeshClock Tilted
variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l))
  (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H
variable {i k : ℕ → ℕ} {I : ℕ → Family (tent Y H) → ℕ → ℂ}
  {E : ℕ → Family (tent Y H) → ℂ} (V : Universal Y H i k I E)
  (G : GroundExtension (i := i) (k := k) (E := E) Y H)
open Garret NorthTapes
open _root_.YM.Hilbert.Freight
variable (D:Invitation Y H G)
local notation "l₀" b:max s:max t:max F:max => launch Y H G D b s t F
variable (a:Axis)(b:Bool)(s:ℕ)
local notation "Sc"=>studio (tent Y H) a 0 b
variable (P: Inspector Y H G)
local notation "Ω"=> P.pulse
local notation "Bp" s:max => badge Y H V G D a b s P
local notation "hP" p:max f:max=> homePlane Y H V G D a b _ _ p f
local notation "W"=> poleForm (tent Y H) a 0 b
local notation "C₀"=> chime (tent Y H)
local notation "Θ"=> mirror (tent Y H)
local notation "L"=> Λ.R.L.val
open Heat
open WindRose PolarArchives ConePrice SelectionAnalysis Chambers Brazier
variable (C:∀ j, Arena Y H G.history.circuit j 0 false)(j:Axis)
variable (χ: displayAlgebra Y H V G.history G.clipped j false (C j) →⋆ₐ[ℂ] ℂ)
local notation "mK"=> marks (timeMesh Λ)
local notation "K₀"=>displayAlgebra Y H V G.history G.clipped a false (C a)
local notation "Ω₀"=> courseValue Y H V G
local notation "Kw"=>driveAlgebra Y H V G.history G.clipped a false (C a)
local notation "F₊"=> Domain Y H G false (flank a 0)
local notation "Sm" m:max=> strip a (-(m:ℝ)) (m:ℝ)
local notation "Qt" m:max=> flank a (m:ℝ)
local notation "bM" d:max=> strip a (-d) d
local notation "A₀"=> atlasAt Y H V G
local notation "Pt" m:max=> Pub Y H a m
local notation "Bk" d:max f:max => (((badge Y H V G D a b d (atlasAt Y H V G)) f))
local notation "Px" u:max f:max=> ticket Y H G u f
local notation "rF"=> studio (tent Y H) a 0 b
local notation "rW"=> studio (tent Y H) a 0 false
local notation "Δ"=> timeMesh Λ
local notation "Wq" n:max=> walkC Y H a b n
noncomputable def cruise (n:ℕ): Sc →ₗ[ℂ] Sc := Wq (4*Λ.block.val*n)
local notation "Tr"=> cruise Y H a b
lemma cruise_cart (n:ℕ)(x:rF): (Tr n x).val=relocate (tent Y H) a (n:ℤ) x.val:=by
    unfold cruise walkC relocate; rw [cart_apply]; change C₀ a _ _= C₀ a _ _; unfold gaugeT Heat.gaugeShift; change C₀ a _ _= C₀ a (4*(Λ.block.val:ℤ)*(2*n)) _; push_cast; ring_nf
lemma cruise_up {s t:ℕ}(i:s≤ t)(v:ℕ)(x:Sc): Tr (Λ.R.L.val^(t-s)*v) (hP i x)= hP i (Tr v x):=by unfold cruise; rw [level_walk ]; rw [mul_left_comm (4*Λ.block.val)]
variable (n:ℕ)
local notation "T₀"=> tapK Y H G a b s
local notation "B₀"=> LightBudget.prepaid Y H V G a (C a)
local notation "Ce"=> Tarmac.center
lemma center_location (m:mK) (t n:ℕ)(g:Dome (tent Y H))(w:g∈ insideAt Λ l K false (flank a (m:ℝ)) t): Ce Y H a n g∈ insideAt Λ l K false (flank a ((m+lantern Λ t n:mK):ℝ)) t:=by
    apply insideAt_mono _ (here_cov Y H false _ _ (eject a (n:ℤ)) g w)
    apply even_flank; rw [stamps_eject,eject_at]; exact le_of_eq (show _ from rfl)
local notation "Qp" t:max=> lantern Λ t
lemma cruise_raise {s t:ℕ}(i:s≤t)(w:ℕ): (lantern Λ t (Λ.R.L.val^(t-s)*w))= lantern Λ s w:= by
 apply Subtype.ext; rw [lantern_clock,lantern_clock,show Λ.R.L.val^(t-s)*w= MeshClock.acts Δ s t w from rfl, MeshClock.matchR Δ s t w i]
lemma cruise_positive {m:mK} (p:0 < m)(n t:ℕ): 0< m+lantern Λ t n:=by
 apply add_pos_of_pos_of_nonneg p; change (0:ℝ) ≤ _; rw [lantern_clock]; positivity
private lemma cruise_right {s t:ℕ}(u:s≤t)(n:ℕ)(x:rF): homePlane Y H V G D a b s t u (cruise Y H a b n x)= cruise Y H a b (Λ.R.L.val^(t-s)*n) (hP u x):=(cruise_up Y H V G D a b u n x).symm
lemma loan_rides {s t:ℕ}(i:s≤ t)(n:ℕ)(x:Sc)(g:Dome (tent Y H))(m:mK)(p:0 < m)(w:g∈ insideAt Λ l K false (flank a (m:ℝ)) t):
    let L':= Λ.R.L.val^(t-s)*n; let p':= cruise_positive (Λ:=Λ) p L' t;
    loan Y H a b (hP i (Tr n x)) (educate Y H a (m+ (Qp t) L') p' t (Tarmac.center Y H a L' g) (center_location Y H a m t L' g w)) = (Tr L') (loan Y H a b (hP i x) (educate Y H a m p t g w)):=by
 intro L' p'; apply Subtype.ext; rw [cruise_right Y H V G D]
 let g':=educate Y H a m p t g w; rw [cruise_cart]; change ((Tr L') (hP i x)).val * (reposition (tent Y H) (eject a (L':ℤ)) g).val= relocate _ _ _ ((hP i x).val*g.val); rw [relocate_mul,chart_eject,cruise_cart]
local notation "Cℓ" m:max f:max c:max => Candle Y H V G C a m f c
local notation "mD" => Domain Y H G false univ
local notation "Θ₀" => flipMark a (tent Y H)
include D
private lemma at_cmp(x:rF)(m:mK)(p:0 < m) (n:ℕ) (t:ℕ)(e':s≤ t)(u:F₊)(g:Dome (tent Y H))(w:g∈ insideAt Λ l K false (flank a (m:ℝ)) t)(e:(Pt m) u.val=Px t g){d d':ℝ}(v:pour Y H a b x∈ insideAt Λ l K false (bM d) s)(v':pour Y H a b (Tr n x)∈ insideAt Λ l K false (bM d') s)(h:d<(m:ℝ))(h':d'<(m:ℝ))(j₀:0≤ d)(j₁:0≤d')
    (X X': Kw)(Tx:Cℓ m (T₀ x) X)(Tx' : Cℓ (m+lantern Λ s n) (T₀ (Tr n x)) X'):
      inner ℂ (B₀ u) (X'.val (B₀ u)) ≤ inner ℂ (B₀ u) (X.val (B₀ u)):=by
 let s₀:=Λ.R.L.val^(t-s)*n; let m':=m+ lantern Λ t s₀; have hp:0 < m':=cruise_positive p s₀ t; let g':=Ce Y H a s₀ g; let w':= center_location Y H a m t s₀ g w; let v'':= cruise Y H a b n x
 have he88:(Pt m') u.val=Px t g':=by unfold m'; rw [add_comm,←pub_sum,e,PubL Y H V G] -- e shadows after
 have hx:d'<(m':ℝ):= lt_of_lt_of_le h' (by unfold m'; rw [AddSubgroup.coe_add, lantern_clock]; exact le_add_of_nonneg_right (by positivity))
 have H₁:Cℓ m' (T₀ v'') X':=(show m+lantern Λ s n=m' from congrArg (m+·) (cruise_raise e' n).symm) ▸ Tx'
 let Z:= loan Y H a b (hP e' x) (educate Y H a m p t g w)
 let U:= (Tr s₀) Z
 have h₂: inner ℂ (B₀ u) (X.val (B₀ u))=inner ℂ (Bk t Z) (Bk t Z):= (Tx.goes u (Tx.makes u)).symm.trans (root_bill Y H V G D a b s t e' x m p u g w e v h j₀ _)
 have h₃: inner ℂ (B₀ u) (X'.val (B₀ u))=inner ℂ (Bk t U) (Bk t U):=by
    rw [← H₁.goes u (H₁.makes u),root_bill Y H V G D a b s t e' v'' m' hp u g' w' he88 v' hx j₁]; have he:=loan_rides Y H V G D a b e' n x g m p w;
    change inner ℂ (Bk t (loan Y H a b (hP e' v'') (educate Y H a _ _ _ g' w'))) (Bk t (loan Y H a b (hP e' v'') (educate Y H a _ _ _ g' w'))) = _; rw [show loan Y H a b (hP e' v'') (educate Y H a _ _ _ g' w') = U from he]
 have Ht: ‖Bk t U‖≤‖Bk t Z‖:= root_walk_time Y H V G D a b t _ _
 rw [h₂,h₃,inner_self_eq_norm_sq_to_K,inner_self_eq_norm_sq_to_K]
 change ((‖Bk t U‖:ℝ):ℂ)^2≤ ((‖Bk t Z‖:ℝ):ℂ)^2
 -- adjust:
 rw [←Complex.ofReal_pow,←Complex.ofReal_pow]
 exact_mod_cast (pow_le_pow_left₀ (norm_nonneg _) Ht 2)

local notation "H₀"=> Ark.Ht Y H G.history.circuit a 0 false (C a)
lemma candle_walk (x:rF)(m:mK)(p:0 < m) {d d':ℝ} (v:pour Y H a b x∈ insideAt Λ l K false (bM d) s)(v':pour Y H a b (Tr n x)∈ insideAt Λ l K false (bM d') s)(h:d<(m:ℝ))(h':d'<(m:ℝ))(j₀:0≤ d)(j₁:0≤d')
    (X X': Kw)(Tx:Cℓ m (T₀ x) X)(Tx' : Cℓ (m+lantern Λ s n) (T₀ (Tr n x)) X'):
      X' ≤ X:=by
 apply sub_nonneg.mp; change 0 ≤ (X-X':Kw).val; apply (ContinuousLinearMap.nonneg_iff_isPositive _).2; apply (ContinuousLinearMap.isPositive_toLinearMap_iff _).mp; apply (LinearMap.isPositive_iff_complex _).2; intro z
 have hz:0 ≤ inner ℂ z ((X-X':Kw).val z):=by
    apply closure_minimal (t:={x:H₀|0 ≤ inner ℂ x ((X-X':Kw).val x)}) _ (isClosed_le continuous_const (continuous_id.inner (X-X':Kw).val.continuous)) (LightBudget.advance_dense Y H V G a (C a) 0 z)
    rintro z ⟨q,g,k,t,rfl⟩; let w₀:F₊:= ⟨q,t⟩
    change 0 ≤ inner ℂ (B₀ w₀) ((X.val-X'.val) (B₀ w₀)); rw [ContinuousLinearMap.sub_apply,inner_sub_right]; apply sub_nonneg.mpr
    have he:(Pt m) q∈ Domain Y H G false (flank a (m:ℝ)):= by simpa only [zero_add] using (pub_area Y H V G a (t:=m) w₀.val t)
    obtain ⟨r,⟨y,w,e⟩,i⟩:= (((domain_eventually Y H G).1 he).and (eventually_ge_atTop s)).exists
    exact at_cmp Y H V G D a b s C x m p n r i w₀ y w e v v' h h' j₀ j₁ X X' Tx Tx'
 have ht:0 ≤ inner ℂ ((X-X':Kw).val z) z:=by rw [←inner_conj_symm]; simpa only [←Complex.star_def,star_nonneg_iff] using hz
 exact ⟨Complex.ext rfl ht.2, ht.1⟩
lemma charging_walk (x:rF) : album Y H V G C a (T₀ (Tr n x)) ≤ album Y H V G C a (T₀ x):=by
 obtain ⟨d,d₀,h⟩:= coincide_at Y H a (pour Y H a b x) s; obtain ⟨d',u,p⟩:= coincide_at Y H a (pour Y H a b (Tr n x)) s
 obtain ⟨v,H'⟩:= (lanterns (Λ:=Λ) s (max d d')).exists; let t:= lantern Λ s v
 have h':d<(t:ℝ):= lt_of_le_of_lt (le_max_left ..) H'; have v':d'<(t:ℝ):= lt_of_le_of_lt (le_max_right ..) H'
 let m:=t+lantern Λ s n; have hm:0 < t:=show (0:ℝ)<(t:ℝ) from lt_of_le_of_lt d₀ h'; have ht:t ≤ m:=by
    change (t:ℝ)≤ _; change (t:ℝ) ≤ (m:ℝ); rw [show (m:ℝ)= (t:ℝ)+(whenly Δ s n:ℝ) from (by unfold m; rw [AddSubgroup.coe_add,lantern_clock s n])]; exact le_add_of_nonneg_right (by positivity)
 obtain ⟨Y',p₁⟩:= squareCandle Y H V G C a t hm (T₀ x) (shapes_at Y H G a b s x h t h'.le)
 obtain ⟨X,p₀⟩:= squareCandle Y H V G C a m (lt_of_lt_of_le hm ht) (T₀ (Tr n x)) (shapes_at Y H G a b s _ p m (le_trans v'.le ht))
 let R':=reduceToDisplay Y H V G.history G.clipped a false (C a)
 rw [←p₀.learns,←p₁.learns]; change R' X≤ R' Y'; apply sub_nonneg.mp; rw [←map_sub]; exact reduce_nonneg Y H V G.history G.clipped a false (C a) (sub_nonneg.mpr (candle_walk Y H V G D a b s C n x t hm h p h' v' d₀ u Y' X p₁ p₀)) -- check order
local notation "VP" => voterAt Y H V G C j χ
local notation "u₀"=> badge Y H V G D a b s VP
omit D
-- right uses phase move only; ensure exactly on this orientation of this character
local notation "rχ"=> displacement Y H V G.history G.clipped j false (C j) χ a (C a)
private lemma voter_plate (x:rF): (VP).pulse s (W x.val x.val) = (rχ) (album Y H V G C a (T₀ x)):=by
 change price Y H V G C j χ s false _=_ ; rw [← price_across Y H V G C j χ s a ((printedS Y H a b x x).paid.choose_spec), price_oneAt' Y H V G C a _ _ (pour Y H a b x) (f:=W x.val x.val) rfl]; unfold tapK; rw [atStamp]; rfl
include D
lemma voter_cmp (x:rF): inner ℂ (u₀ (Tr n x)) (u₀ (Tr n x))≤ inner ℂ (u₀ x) (u₀ x):= by
 rw [measures_here,measures_here,voter_plate Y H V G a b s C j χ,voter_plate Y H V G a b s C j χ]
 apply sub_nonneg.mp; rw [←map_sub]; exact _root_.map_nonneg _ (sub_nonneg.mpr (charging_walk Y H V G D a b s C n x))
lemma voter_passOld (x:rF): ‖u₀ (Tr n x)‖≤‖u₀ x‖ :=by
 have ht:= voter_cmp Y H V G D a b s C j χ n x
 nth_rw 1 [@norm_eq_sqrt_re_inner ℂ]; nth_rw 1 [@norm_eq_sqrt_re_inner ℂ]; exact Real.sqrt_le_sqrt ht.1 -- nth issue inside norm?

end YM.CF.Buffered.Afterglow.Tower.FirstWindows.QuantaFields
#print axioms YM.CF.Buffered.Afterglow.Tower.FirstWindows.QuantaFields.at_cmp
#print axioms YM.CF.Buffered.Afterglow.Tower.FirstWindows.QuantaFields.loan_rides

#print axioms YM.CF.Buffered.Afterglow.Tower.FirstWindows.QuantaFields.voter_passOld
