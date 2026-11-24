import YM.CF.BProof.Digit.Fog
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Sour.Digit
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Skye Scree Cadre Palot
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tulip Fock Rush Scroll Paige Vault Phase Acorn Spire
open Pastry Vow Rue
attribute [local instance] opCStarAlgebra
variable {n:Side}
local notation "SA"=> Seat n
local notation "VX"=> Aura n
local notation "Hk"=> hook SA
open Hake Jet Sault Stax
attribute [local instance] loreM loreN
variable {P:BudgetPoint}{X Y Z:Aura n}{V W:Firing n}{D:Support (More n)}
open Branch Tenant Drapes Rill Sault
attribute [local instance] Rill.boreKSpace Rill.boreXN
local notation "JS"=> Single n
local notation "SO"=> Support (More n)
local notation "Γ"=> (FC (Dwell n))
open Exa Tap Dial
open Haro Ione Larch Glyph
section
variable {N:Side}
end
open Exa Tap Dial
open Push.AbsoluteSums Trees Mew Floral Axial
open scoped YM.CF.Mew YM.CF.Sour.Axial
variable {T S:BeatL n}{U:Scree.Loom n}{R t d a b c W z₀ z₁:ℝ}{q:ℕ} {m:Cash P}
variable (k:Arbor P U q t d W z₀ z₁) (F:BondL T S (body_Q (N:=n) 1) b c a d) {Q:SpaceM}
abbrev rotor (B:Cusp n)(Q:SpaceM):= Stax.lamp (P:=P) B (stack k F Q)
abbrev wave (B:Cusp n)(Q:SpaceM):= Nu P (Fine (rotor k F B Q)) (Fine B) (tuneZ k F Q)
variable (p:LoomPay P m R W a b c)[Nonempty (ΘS R)]
local notation "A₀"=> orchard F R p.fp.le
local notation "δ"=> cipherK q
variable {B G:Cusp n}{ε hd:ℝ}
namespace Court
local notation "J"=> stack k F
variable {Q₀ Q₁:ΘS R}(v:Court B G P (cipherK q) m R W ε hd Q₀ Q₁)
local notation "J₀"=> (J Q₀.val)
local notation "y"=> Q₁.val-Q₀.val
local notation "μ₀"=> (A₀).bead W P
include p v
local notation "δ'"=> (ε+hd)
local notation "L'"=> hallNR δ'
theorem glyph : let X' := rotor k F G Q₁.val-rotor k F B Q₀.val; Binder P W (ρL P) (Fine X') (δ'*m.Γr) ∧ Flaws P W (ρL P) X' (δ'*(m.κ⁻¹*m.Γr)) ∧ Binder P W (P.supportExponent+1+1) (wave k F G Q₁.val-wave k F B Q₀.val) (δ'*m.Nr):=by
 intro Z
 let A(z:ℂ):=B+z • (G-B); let X(z:ℂ):= J₀+z • J y; let Fv(z:ℂ):= tuneB k F Q₀.val+z • tuneB k F y; let M(z:ℂ):= μ₀+‖z‖ • (hd • μ₀); let H(z:ℂ):= tuneZ k F Q₀.val+z • tuneZ k F y
 let U':= disk L'
 choose A' Λ using fun z:ℂ=> show ∃ Q:blazeK n,z∈U'→ m.grapes Q (A z) δ W from (by by_cases g:z∈U'; exact ⟨_,fun _=> (heights_c k v z g).choose_spec⟩; exact ⟨0,fun u=> (g u).elim⟩)
 let h:=k.hw; let T:=p.toWarrant; have hx(z)(g:z∈U'): wire P W δ (X z) (M z) (Fv z):=(pursue k F p v z g).1
 have hi(z)(g:z∈U'): m.vines (A' z) (M z) 1:= Cash.clock T (Λ _ g) ((pursue k F p v z g).2.1) h (hx _ g).dice
 let Wb(z:ℂ):=lamp (P:=P) (A z) (X z); let w(z:ℂ):= Nu P (Fine (Wb z)) (Fine (A z)) (H z)
 have hB(i x' V):Hol U' fun z=>A z i x' V:= salute _ _
 have hM: PlayC U' X:= maze (hot_w k F Q₀.val) (hot_w k F y)
 have hZ(i:Aura n)(D')(u:D'⊆i.val)(V):Hol U' fun z=> Wb z i D' V:= Cash.lamp_hol (K:=X) (B:=A) hB hM _ _ _ Fv Λ hx hi h isOpen_ball u _
 have hz:= Cash.Φk P; have he:L'>1:= v.hl; have hp(c:ℝ): c/(L'-1)≤ δ' * c:=by have hx:=v.pos.ne'; rw [hallNR,add_sub_cancel_left,div_inv_eq_mul,mul_comm]
 let hv(z:ℂ)(g:z∈U'):= (Cash.heights T (Λ z g) k.hw (hx z g) (hi z g)).1
 have hv₀:= Binder.diff (F:=fun z=>Fine (Wb z)) he h (fun z g=> (hv z g).binder) (fun i v _=>hZ i ∅ (empty_subset _) v) hz (hp _)
 have hv₁:= Flaws.diff (F:=Wb) he h (fun z g=> (hv z g).cost) (fun i D u V _=>hZ i D (Flaws.full_mem.mp u).2 V) hz (hp _)
 have hq:0 ≤ P.supportExponent+1+1:= by linarith [P.exponent_pos]
 have hw:= Binder.diff (F:=w) he h (fun z g=>Cash.reload T (Λ z g) h (hx z g) (hi z g) ((pursue k F p v z g).2.2)) (fun i V _=> Cash.twist_hol (B:=A) (K:=X) (Z:=H) hB hM _ _ _ Fv T Λ hx hi h (fun _ _=>salute _ _) isOpen_ball ⟨0,d0 he⟩ i V) hq (hp _)
 have hy:X 1=stack k F Q₁.val:=by unfold X; rw [one_smul,map_sub,add_sub_cancel]
 have hY:H 1=tuneZ k F Q₁.val:=by unfold H; rw [one_smul,map_sub,add_sub_cancel]
 unfold w Wb at hw; unfold Wb at hv₀ hv₁; rw [hy] at hw hv₀ hv₁; rw [hY] at hw; unfold A H X at hw; unfold X A at hv₀ hv₁; simp only [one_smul,add_sub_cancel,zero_smul,add_zero] at hw hv₀ hv₁; exact ⟨hv₀,hv₁,hw⟩
end Court
end YM.CF.Sour.Digit
