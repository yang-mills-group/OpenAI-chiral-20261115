import YM.SU5.Reconstruction.Cashier.Booth
import YM.SU5.Selected.Highlite
set_option quotPrecheck false
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 6000
set_option maxHeartbeats 490000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.SlabMark.Bankroll
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
local notation "K"=>tent Y H
local notation "L₀"=>Λ.R.L.val
variable {i k:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}(V:Universal Y H i k I E)(s:ℕ)
open SatinVerification Tapestry PhaseChoice
variable (G:GroundExtension (i:=i) (k:=k) (E:=E) Y H)(j:Axis) (C:Arena Y H G.history.circuit j 0 false)(w:ℕ)
  (S:Finset Cover)(t:Between (tent Y H) j 0 (ruler Λ.block*w) S)(hw:0<w)
local notation "uM"=> (L₀^(s+1-s)*w)
local notation "Wh"=>wingspan Λ l S
local notation "Rx"=>render S (tent Y H)
local notation "B"=>allBox Y H V G j S s C w t hw
local notation "Ξ" s:max w:max=>advance Y H V G.history.circuit j 0 false C (MeshClock.whenly (timeMesh Λ) s w)
open Buffered.Reliance Buffered.Reliance.ShortWave
open Selected
open Buffered.Concord (Meter)
-- tune mixed namespace
variable {r:ℕ} (d q u:ℕ) {J:Calibration}
local notation "Φ"=>CF.Pannier.Chancel.payout d q u
open CF.Pannier.Chancel
open Selected
local notation "ρ"=>grain Φ
local notation "Ψ"=>Sen ρ Φ
variable {d q u}
lemma megabetween (t:addgap K ≤ payout d q u) (v:Cliplet.Mural.Invoice K (payout d q u) w): Between K j 0 (ruler Λ.block*w) Ψ:=
 between_grain t _ _ (by change ((12:ℤ)* Φ) ≤ 16*(Λ.block.val:ℤ)*(w:ℤ); have ht :12*Φ ≤ (16*Λ.block.val)*w:= v.lo; exact_mod_cast ht)
lemma buzz {x : Cover}{i:Cover} (a:i∈buzzbox x) : |i j-nodeC x j|≤ 2:=by -- syntax
 unfold buzzbox at a
 simp [visits,square] at a
 rcases a with (a|a|a|a|a)
 all_goals subst i; norm_num [step_apply, negDir, posDir]; repeat' split
 all_goals rw [abs_le]; omega

lemma giant (t:addgap K ≤ payout d q u) (v:Cliplet.Mural.Invoice K (payout d q u) w): Between K j 0 (ruler Λ.block*w) (grindscape (booty ρ d q) Ψ):=by
 intro i p
 rcases mem_union.mp p with l|l; · exact megabetween Y H j w t v i l
 obtain ⟨a,u',p⟩:= mem_biUnion.mp l; let x:= booty ρ d q a
 have ht:=bounds_Sen_grain (Papal.stake_centers Y H (grain (payout d q u)) d q u a) j
 have hX:= abs_le.mp (buzz j (x:=x) p); let b':= payout d q u; let K':=tent Y H
 change 3 * (b':ℤ)+1 ≤ nodeC x j ∧ nodeC x j ≤ 5*(b':ℤ)+1 at ht
 change 0+K'.ℓ ≤ i j ∧ i j+K'.ℓ ≤ ruler Λ.block*w
 have hv:16*(Λ.block.val:ℤ)*(w:ℤ)≥12*(b':ℤ):= by exact_mod_cast (show 12*b'≤ (16*Λ.block.val)*w from v.lo)
 have h0 :0<b':=addgap_pos.trans_le t
 have hz :2*K'.ℓ ≤ b':= by change addgap K' ≤ b' at t; unfold addgap stepgap at t; omega
 unfold ruler; constructor <;> linarith

section cuts
variable (L:Finset (Face ℤ))(p: restsOn L S){f:Family (tent Y H)}(y: Swatch S)
local notation "D₀" i:max=>tintMark L (Buffered.Concord.Meter i) (tent Y H)
include p
-- compare any purchased support here.
noncomputable def strip (n:ℕ) (y: Swatch S)(p:restsOn L S) : Swatch S:= fabric S K (((tint_price L S _ K p).widen).mul (texture S K y) : InTest K true S false ((D₀ n) * ((Rx) y)))
local notation "Sr" n:max=> strip Y H S L n y p
lemma costume (n:ℕ): render S K (Sr n)= D₀ n* ((Rx) y):=render_fabric ..
lemma supportedCostume : Tendsto (fun i:ℕ=> B (Sr i)) atTop (𝓝 (B y)):=by
 let z(i:ℕ):=Sr i-y
 have he i: Rx (z i)= unveil Y H L (render S K y) i:= by unfold z unveil; rw [map_sub,costume]
 obtain ⟨v,m⟩:=Journey.valuation Y H (texture S K y); have hp i:=layered_cost Y H L m i
 have h: Dues Y H G s ((Rx) ∘ z):=by
    refine Eventually.of_forall fun i₀=>?_; let m':=i (G.rows i₀); let ψ:= terrain Y H (Y.ir m') s
    let L':= (Y.voyage m').CapeT s
    filter_upwards [gap_is_nil Y H L (x:= (Rx) y) ψ L'] with i hi
    apply tendsto_const_nhds.congr'; filter_upwards [hi] with n hn
    change 0= Tapestry.exhibit Y H s m' ((Rx) (z n)) (drawn L' i)
    rw [he]; exact (morph ψ (drawn L' i) hn).symm -- Expr rewrite
 have ht:=responsiveBox Y H V G j S s C w t hw z (1*v+v) (fun i=> sample_price Y H S (z i) ((he i).symm ▸ hp i)) h
 have h':= ht.add (tendsto_const_nhds (x:=B y)); simpa only [z,(B).map_sub,sub_add_cancel,zero_add] using h'
where
 morph {m n:Side}(w:m=n)(x: Fields n) {k:Mark m} (h:(w ▸ k : Mark n) x=0): arrange m n w k x=0:=by subst n; exact h
variable {r₀:ℝ}
include t
lemma fitted (v: StampFoot Y H V s G j C w S f r₀): ∀ᶠ i in atTop, StampFoot Y H V s G j C w S ((D₀ i) * f) r₀ := by
 let x:=fabric _ _ v.1; have hx:Rx x=f:=render_fabric .. -- v Definally ?
 have hv:=stenciled Y H V s G j C w S t v.2.2.choose x |>.1 ((hx.symm) ▸ v)
 filter_upwards [(((supportedCostume Y H V s G j C w S t v.2.2.choose L p x).add_const (Ξ s w)).norm).eventually (gt_mem_nhds hv)] with i u
 rw [←hx,← costume Y H S L p x]; exact (stenciled Y H V s G j C w S t v.2.2.choose _).2 u
end cuts
end YM.CF.Buffered.Afterglow.Tower.SlabMark.Bankroll
#print axioms YM.CF.Buffered.Afterglow.Tower.SlabMark.Bankroll.giant
#print axioms YM.CF.Buffered.Afterglow.Tower.SlabMark.Bankroll.fitted
