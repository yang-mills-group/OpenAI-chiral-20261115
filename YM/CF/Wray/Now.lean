import YM.CF.Wray.Sum
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Wray
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
variable{N P B:Side}{S:StepData (Domain N B) (Domain P B)}{T: Tube SU.group S}{K:Teller SU.group}{G:Ratio (mid N B) (mid P B)}{R:Patch}{L:ChartRatio SU.group}
variable {d e η t z g b c A B':ℝ} {j k k' m n l:ℕ}
variable (V:Grace K R L)
open Lich.Muster Lor
open Jet Vol Rel
local notation "G5"=>SU.group
variable {x y0 β:ℝ}(pp:BudgetPoint){t₀ v v₁ p11 p22 p3 p4:ℝ}
local notation "SN"=> Site (Domain N B)
open Cascade
open Fief
open Yaw Pig
open Lich.Muster Push.AbsoluteSums
open Iva Eire
local notation "ζ"=> (radiusB x)
open Trees Footprint Iva Eire
variable (F:Pilot)(Z:Pluck R) (I: Stake.Isle){σ:ℝ}(Q: Tun I Z F σ){H:Muster G S x d T}
variable {U:Grasp V.U B d}{W:GivenX V U}{X: GramM (mid N B)}{Y: GramM (mid P B)}(M: Sheep V U W G Y.J X.J (k+2) n A)(P_:∀ X: Support (Domain P B),Lend P B d X)
variable {r:ℕ}
local notation "K'"=> Hos S r
variable (D:Support (Domain N B))(i:Hos S r) (Y': Hos S r→Support (Domain P B)→ℝ)(Z': Hos S r→ Sweep (mid P B))(T₁:Ids (mid P B))
variable (w':Hive.Vista U Y.J.M Y.J.P P_ (k+2) M.q ((Fintype.card Play:ℝ)*t) M.lot M.tone)
local notation "Nx"=> Domain N B
local notation "Fx"=> Domain P B
variable(Vg: Palot.leaf (Site (Domain N B))→ℝ)(Vx:Palot.leaf (Site (Domain N B))→ℝ)(B₁: mSeal P B→ℝ)(B_:mSeal P B→ Toll (Single (mid N B)))
variable (dB:ℝ)(J_:ℕ)
variable (Qx:TailB→Support (Domain P B)→Toll (Iota G))(Qv: Grave→Support (Domain P B)→Toll (Iota G))
local notation "v'"=> ((H.post+90)*radiusB x)
local notation "R_"=> LuX (H:=H) (k:=k) (j:=j) (r:=r)
variable (Bη: Rust (mid P B) → Raid (LeanV (Single (mid P B))))
local notation "Θ"=> (vast (k:=(Z.N1*radiusB x)) H)
local notation "Λ"=> Yaw.railsB Θ (k+2) Z' Y' P_ Qx Qv
local notation "Λ'"=> (fun i=>gift_k i (Bη i) Q.dust.glam Q.dust.toil k)
variable (V_:ℝ)
local notation "Φ"=> F.hat R x
local notation "Z₂"=> (luceL R J_ x)
variable(Y1: Monk SU.group S)
include M
omit M
local notation "R_d"=> R_ Y1 I Vg Vx B₁ B_ J_ Φ Q
local notation "F₁"=> Folk S r (Words S)
local notation "WQ"=> (((H.loft+H.post+200)*radiusB x))
local notation "Xp"=> stake (n:=LeanV (Single (mid N B))) V_
-- Rflare independent of Y except Bravo, discounted pref before.All
local notation "Rz"=> frostG (H:=H) (k:=k) (j:=j) F Z I Q P_ Y' Z' Vg Vx B₁ B_ J_ Qx Qv Bη V_ Y1
-- Account Currency assignment pre fit and signs.Actual only finite contributions but forecast.Trial same for all β ancestors Norm.Strung.
local notation "Ω"=> Rust_ (H:=H) (k:=k) (j:=j) (r:=r) F Z I Vg Vx B₁ B_ Y1 J_
variable (ΛZ: Rust (mid P B)→ℝ)
local notation "Br"=> brink (k:=k) (j:=j) (H:=H) F Z I Q P_ Y' Z' Vg Vx B₁ B_ J_ Bη V_ Y1
-- per-axis. SAT sandwich.
abbrev capitalP(x T a:ℝ)(l j k:ℕ):ℝ:= (seatL R:ℝ)* (Real.exp (a*(((l+j+230)+(l+j+230)+1:ℕ)^4:ℕ)) * (T*mM F Z I Q x k))
local notation "Y₀"=> (BranchX (r:=r) S Θ v')
variable {a vX:ℝ}
lemma lodge(k:ℕ)(M:ℕ)(p: 0 ≤ a)(hz:0 ≤ mM F Z I Q x k)(u:0≤ v)(o:Site (Domain N B))(h:S.patch=R)(A₁:100≤radiusB x) : let N:=(H.loft+H.post+230); (∑ i:Sat S with roost i=o,Trees.currency (radiusB x) a (vast (k:=M) H (.inl i)).val * (v * mM F Z I Q x k))≤ capitalP F Z I Q x v a H.loft H.post k:=by
 intro K; let P':=univ.filter fun i:Sat S=>roost i=o; let V:= v*mM F Z I Q x k; let C:= Real.exp (a*((K+K+1:ℕ)^4:ℕ)); have hp:0≤ C*V:=mul_nonneg (Real.exp_pos _).le (mul_nonneg u hz)
 have hh(i:Sat S):Trees.currency (radiusB x) a (vast (k:=M) H (.inl i)).val≤ C:=by
    let V:= (vast (k:=M) H (.inl i)).val; have hg: coverNumber (radiusB x) V ≤ (K+K+1)^4:= (Corona.cover_mono ( (uprise i M).trans (Corona.halo_mono (show _≤ K*radiusB x from by unfold K; simp_rw [Nat.add_mul]; omega) (Subset.refl _))) _).trans (Corona.tile (roost i) K _ (by omega)); exact Real.exp_monotone (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hg) p)
 have ht:P'.card≤ seatL R:=by rw [←h]; let P:= pile (S:=S) {o}; simpa only [card_singleton,one_mul, mem_singleton] using P
 change (∑ i∈P', _) ≤ _; apply le_trans (sum_le_sum (s:=P') fun i _=> mul_le_mul_of_nonneg_right (hh i) (mul_nonneg u hz)); rw [sum_const,nsmul_eq_mul]; exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr ht) hp
-- compress brink.Breaks.
lemma endow(i:Kite S r)(a b:ℝ): Br t a b (.inl i)=loadH (facesH (k+2) Z' Y' P_ i) t*(Trees.currency (radiusB x) a (Jig S v' i).val* (joinV Xp (purpleP I (paidL I Q.K₁ Q.K₂ k x Φ) i.fst k j Q.book x F Z))):=by
 unfold brink; change loadH (PetalP.bud _) t *_=_; rw [bareS,one_mul]; rfl
lemma leavesQ(i: Rust (mid P B))(a b:ℝ): Br t a b (.inr (.inl i))=Trees.currency (radiusB x) a (pore S v' i).val *loadH (postY (camp (shaft i)) (Λ' i)) t:=by -- Λ' function apply
 unfold brink; change _*(loadH (PetalP.bud _) t* (_*joinV Xp (Pi.single ∅ 1)))=_; rw [bareS,one_mul,joined,show Xp ∅=1 from by simp [stake],one_mul,mul_one, mul_comm]; rfl
lemma unit_r (i: Words S)(a b:ℝ): Br t a b (.inr (.inr i))=Trees.currency (radiusB x) a (Θ i).val*(joinV Xp ((Ω b Q) (Sum.inr (Sum.inr i)))):=by
 unfold brink; change loadH (PetalP.bud _) t*(loadH (PetalP.bud _) t*_)=_; rw [bareS,one_mul,one_mul]; first|rfl|done -- Type darn draws same? second bud differ.
-- canonical anchors membership
variable {κ₀:ℕ}
def anchorK(i:Hos S r): Site (Domain N B):= Classical.choose (stem_p S i)
def root_l{c:Side}(i: Bit (Site c)):Site c:= Classical.choose i.property
abbrev awake (i: Folk S r (Words S)):Site (Domain N B):= match i with
| .inl i=> anchorK i.1
| .inr (.inl i)=> S.ratio.parent (angle i)
| .inr (.inr (.inl i))=> roost i
| .inr (.inr (.inr (.inl i)))=>i
| .inr (.inr (.inr (.inr i)))=>root_l i
lemma destiny(i:F₁) : awake i ∈ (Y₀ i).val:=by
 rcases i with i|i|i|i|i
 · exact halo_subset _ _ (mem_union_left _ (Classical.choose_spec (stem_p _ _)))
 · exact halo_subset _ _ (mem_image_of_mem S.ratio.parent (show angle i∈ inspected (shaft i) from mem_union_left _ (rustL _ i).property))
 · apply halo_subset 20 _; apply halo_subset 1 _; apply halo_subset WQ _; have hp:=Muster.hold_s i; cases i with | inl i => exact hp| inr i=>cases i<;>exact hp -- private exposed?
 · exact halo_subset 20 _ (halo_subset 1 _ (halo_subset _ _ (mem_singleton_self _)))
 exact halo_subset 20 _ (halo_subset 1 _ (Classical.choose_spec i.property))
end YM.CF.Wray
