import YM.SU5.WakeFields.Players
set_option maxHeartbeats 300000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Py.Rate.LocalLimit.Preparation
open Neon
open Py
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
attribute [local instance] opCStarAlgebra
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Hom Vale Vale.Grace Next.Free Thera Nacre Dial Fock
open Tye Lich Stake Pail Pail.Dew
open Ione Moto Taxi Hove Haro Vow Bake Lilt Prism Rue Larch Push.AbsoluteSums.Trees Salt Jet
open scoped YM.CF.Mew

set_option autoImplicit false
open Mew QuadClock Roots Rive Oise

open QuadClock FullBill Pitching Focus Buffered Afterglow Journey
variable {P:Preparation}{ℓ:ℕ}(Y:Course P (VolumeCape.Dream.Nimbus ℓ))
attribute [-instance] instDecidableEqLex
namespace Yoke.Jewel.Program
open Tapestry Advance Papyrus Papyrus.Franc
variable {n:Side}
open Py.Rate.Pannier CF.Pannier Chancel Rous Pressure Worth Worth.Pays Graph
open Regis Gleam Tempest
open WakeInvestment Gleam.Wake
open Lamour Lamour.Bridge Celeste Clock Hookah Tapestry Cliplet
open Window Ballad Hiro EmberWind EmberWind.MixedCards
open EmberWind.Staff (Beacon)
open Regis.Wake (Paint)

variable (s i k : ℕ)
variable {x A B ρ α E v : ℝ} {J : Type*} [Fintype J]
variable (U : J → EmberWind.Staff) (D : J → MixedCards.Ticket) (L : List J)
local notation "T" => SU.group.ColorIndex
local notation "Γ"=> side Y i s
local notation "Yq" => (RootBook Y i k s)
local notation "M" => (RootBook Y i k s).J.M

lemma noble_global (T' : FC (Single Γ)) (g : SU.E) :
    noble Y s i k (twist (quantU (tradew Γ (fun _ => g))) T') = noble Y s i k T' := by
  let b : Seat Γ → SU.E := fun _ => g
  let t := tradew Γ b
  let m := mateK Γ; let x := flatSea Y s i k
  let u := quantU t
  let S := spar P.K.j M (1:Pane Γ)
  have he : Lattice.gauge b (1:Pane Γ) = 1 := by
    funext i; change g * 1 * g⁻¹ = 1; group
  have ht : Brace.Sparkle Γ P.d M P.K.j := P.U.broadness _
                   (P.J.gran.trans ((Y.voyage i).ownership s).size) _
  have hs : Sea S x := preparedFlat Y s i k
  have H := Tulip.guard0 (N:=More Γ) P.dpos.le
  have hv : twist t S=S := by simpa only [t,S,he] using (ht.covary 1 b H).symm
  have hx : Sea S (acts u.val x) := hv ▸ Lamour.Bridge.lifted t hs
  have hr (f : Wave (Single Γ)) : inner ℂ m (acts u.val f)=inner ℂ m f := by
    nth_rw 1 [←show acts u.val m = m from Girt.mastC b]; exact act_unit_inner ..
  rw [noble_linear, noble_linear]
  change alleyR m x (twist u T')=alleyR m x T'
  rw [alley_match (ht.projection 1 H) hs hx]
  change (inner ℂ m _)⁻¹ * inner ℂ m (acts (twist u T') _) = _
  rw [←Fock.swivel,hr,hr]
  rfl


abbrev tallyC (t : J → ColorL) : ℂ := noble Y s i k (judged U D L Γ t)

omit [Fintype J] in
lemma celebrity (c : J → ColorL) (g : SU.E) :
    tallyC Y s i k U D L (fun i => SU.group.adjoint g (c i)) = tallyC Y s i k U D L c := by
  unfold tallyC; rw [judges,noble_global]

lemma sleek : ContDiff ℝ 1 (tallyC Y s i k U D L) := by
  let T₁ := ((alleyR (mateK Γ) (flatSea Y s i k)).toContinuousLinearMap.restrictScalars ℝ)
  let S := (Yq).J
  rw [show tallyC Y s i k U D L = fun a => T₁ (judged U D L Γ a) from ?_]; swap; · funext a; exact noble_linear ..
  exact T₁.contDiff.comp (smoothA Γ U D L)

-- optic blend. coord eu norm

def hallL (n : Side) : Gleam.Wake.Vessel SU.group (More n) (materialL J) := ⟨fun p => ((U p.1).localFace n,p.2)⟩

def tones (c : materialL J → ℝ) : J → ColorL := fun i => WithLp.toLp 2 (fun j => c (i,j))
lemma tone_sub (c d:materialL J→ℝ) (i:J) : tones (c-d) i = tones c i - tones d i:=rfl
abbrev toneFare := Staff.rackColor + 1
lemma toneFare_pos : 1 ≤ toneFare := by unfold toneFare Staff.rackColor; have h:= Nat.cast_nonneg (α:=ℝ) (Fintype.card T); linarith

lemma tone_cost (c:materialL J→ℝ)(i:J): ‖tones c i‖≤ toneFare * ‖c‖:= by
  let K := Staff.rackColor; have hc : 0 ≤ K := Nat.cast_nonneg _
  apply le_of_pow_le_pow_left₀ (n:=2) (by decide) (mul_nonneg (zero_le_one.trans toneFare_pos) (norm_nonneg c))
  rw [EuclideanSpace.real_norm_sq_eq]
  let d : T → ℝ := fun j => ‖c‖^2; have h(j:T): ‖tones c i j‖^2≤ ‖c‖^2 := pow_le_pow_left₀ (norm_nonneg _) (norm_le_pi_norm c ((i,j):materialL J)) _
  refine le_trans ?_ (show K * ‖c‖^2 ≤ _ from ?_)
  · have hv: (∑ j:T, d j)=K*‖c‖^2 := by simp [d,K,Staff.rackColor]
    rw [←hv]; exact sum_le_sum (fun i _ => by simpa only [d, Real.norm_eq_abs, sq_abs] using h i)
  change _ ≤ ((K+1)*_)^_; rw [mul_pow]; exact mul_le_mul_of_nonneg_right (by nlinarith) (sq_nonneg _)

lemma tone_diff : ContDiff ℝ 1 (tones (J:=J)) := by
  apply contDiff_pi.mpr; intro j
  let F : ((materialL J) → ℝ) →ₗ[ℝ] ColorL :=
       ⟨⟨fun x => tones x j, fun _ _=>rfl⟩, fun _ _=>rfl⟩
  exact F.toContinuousLinearMap.contDiff

def tint (c:materialL J → ℝ) := tallyC Y s i k U D L (tones c)

lemma tint_diff : ContDiff ℝ 1 (tint Y s i k U D L) := (sleek Y s i k U D L).comp tone_diff
lemma tint_material (ρ:ℝ) (A:Pane Γ):
    tint Y s i k U D L ((hallL U Γ).material ρ A)=tallyC Y s i k U D L (fun i => (U i).cargoS Γ A ρ) := rfl

abbrev standardTuition (E : ℝ) (m R : ℕ) := sizeRent (2*m) R * flatTicket E^(2*m)
lemma tuition_nn (E : ℝ) (m R : ℕ) : 0 ≤ standardTuition E m R := by
  have h : 0 ≤ flatTicket E^(2*m) := Even.pow_nonneg (by exact even_two_mul _) _
  exact mul_nonneg (by unfold sizeRent; positivity) h

variable (pI:Investment P E v) (S : Support (More (side Y i s))) (h : ∀ j : J, EmberWind.Staff.scope (U j) (Journey.side Y i s) ∈ S)
variable {ε : ℝ} {R : ℕ} (hu : S.card ≤ R)
include pI hu
lemma noble_paid {F:FC (Single Γ)} {c:ℝ}{m:ℕ}(p: Cadre (modesIn _ S) (2*m) c F) :
    ‖noble Y s i k F‖ ≤ standardTuition E m R * c := by
  have hc:= (norm_nonneg _).trans p.price
  have hz : Lyrics (modesIn _ S) (2*m) (c*sizeRent (2*m) R) F :=
    p.output.expend le_rfl (mul_le_mul_of_nonneg_left (size_issue hu (2*m)) hc)
  exact (noble_bound Y s i k F 0).trans ((hz.post _ (invest_W Y s i k pI 0 (by norm_num))
              (flatT_pos pI)).trans_eq (by unfold standardTuition; ring))

include h
omit [Fintype J] in
lemma flavor_paid {c:J → ColorL}{K:ℝ}(g:1 ≤ K)(hv:∀ i, ‖c i‖≤K) :
    ‖tallyC Y s i k U D L c‖≤ standardTuition E L.length R*(MixedCards.topFare*K)^L.length :=
  noble_paid Y s i k pI S hu (judged_color _ g U D L c h hv)

omit [Fintype J] in
lemma flavor_exchange {c c':J → ColorL}{K:ℝ}(g:1 ≤ K) (hv:∀ i, ‖c i‖≤K) (hw:∀ i, ‖c' i‖≤K)
    (hp:∀ i,‖c i-c' i‖≤ε) (he:0≤ε) :
    ‖tallyC Y s i k U D L c - tallyC Y s i k U D L c'‖ ≤ standardTuition E L.length R * (L.length * (MixedCards.topFare*K)^L.length * ε) := by
  unfold tallyC; rw [noble_linear,noble_linear,←map_sub,←noble_linear]
  exact noble_paid Y s i k pI S hu (judged_change _ g U D L _ h hv _ hw hp he) -- syntax

abbrev palettePrice (E : ℝ)(r m : ℕ) := standardTuition E m r *((MixedCards.topFare*toneFare)^m *(1+m*toneFare))
lemma ready_color : Paint (tint Y s i k U D L) L.length (palettePrice E R L.length) := by
  let X:=MixedCards.topFare; let m:= L.length; let B:=standardTuition E m R; let C:= toneFare
  have h0:B ≥ 0 := tuition_nn ..; have hX : 0 ≤ X := MixedCards.fare_nn; have hC : 1 ≤ C := toneFare_pos
  have hp (x:ℝ)(t:1≤x) (i:materialL J →ℝ)(hk:‖i‖≤x) : ∀ k, ‖tones i k‖≤C*x:= fun k =>
     (tone_cost i k).trans (mul_le_mul_of_nonneg_left hk (zero_le_one.trans hC))
  constructor
  · exact tint_diff ..
  · intro K hK x hx
    apply (flavor_paid Y s i k U D L pI S h hu (one_le_mul_of_one_le_of_one_le hC hK) (hp K hK x hx)).trans
    change B*(X*(C*K))^m ≤ B*((X*C)^m*(1+(m:ℝ)*C))*K^m
    rw [←mul_assoc X, mul_pow _ K]; have he : 1≤1+(m:ℝ)*C:= le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) (zero_le_one.trans hC))
    calc _ ≤ B*((X*C)^m*K^m)*(1+(m:ℝ)*C) := le_mul_of_one_le_right (mul_nonneg h0 (mul_nonneg (pow_nonneg (mul_nonneg hX (zero_le_one.trans hC)) _) (pow_nonneg (zero_le_one.trans hK) _))) he
         _ = _ := by ring
  intro K hK x y hx hy
  have hg := fun i => (tone_sub x y i) ▸ tone_cost (x-y) i
  refine (flavor_exchange Y s i k U D L pI S h hu (one_le_mul_of_one_le_of_one_le hC hK) (hp K hK x hx) (hp K hK y hy) hg (mul_nonneg (zero_le_one.trans hC) (norm_nonneg _))).trans ?_
  change B*((m:ℝ) * (X*(C*K))^m*(C*‖x-y‖)) ≤ B*((X*C)^m*(1+(m:ℝ)*C))*K^m*‖x-y‖
  rw [←mul_assoc X,mul_pow _ K]; nlinarith only [mul_nonneg (mul_nonneg (mul_nonneg h0 (pow_nonneg (mul_nonneg hX (zero_le_one.trans hC)) m)) (pow_nonneg (zero_le_one.trans hK) m)) (norm_nonneg (x-y))]
#print axioms flavor_paid
#print axioms flavor_exchange
#print axioms ready_color
end Yoke.Jewel.Program
end YM.CF.Py.Rate.LocalLimit.Preparation
