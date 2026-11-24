import YM.SU5.Intrinsic.Coil.Call
import YM.CF.Ione.Rale
import YM.CF.Neon.Ten

/-! # Revenues for the layout (finest observing CCR price). -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 500000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Coil.Chart.Stoke
open Function Lattice Finset Filter Stilo Palot RG Scree Skye Fock Tulip Sour
open Cube Pastry Vow Rue Stax Sault
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator Mew
attribute [local instance] opCStarAlgebra
variable {I J:Type}[DecidableEq I][Fintype I]{n:Side} {F:ForceBudget n}{P:BudgetPoint} {H:ℝ} {δ:ℕ}
variable {b:Force n→ℝ}{V:I→ Firing n}{a:I→ℝ}{B:Chart I (Seat n)}
open Push.AbsoluteSums Push.AbsoluteSums.Trees
local notation "W"=> B.ledger
abbrev grantW (Q ψ γ:ℝ):= Q*(ψ*(1-γ)⁻¹)
variable {C:B.Stoke δ P H V a}
variable {Q s c m ψ θ γ:ℝ}
structure Revenue (C:B.Stoke δ P H V a)(F:ForceBudget n)(b:Force n→ℝ)
 (Q s c m ψ θ γ:ℝ) (f:I⊕ Force n→ℝ) (R:I→ Aura n→ℝ)(l:List I): Prop where
 blizzard:Blizzard F P H δ b
 bill:Heavy B f a b Q
 simple:l.Nodup
 complete:l.toFinset=univ
 ext:3 ≤ P.B
 peg:12≤δ
 font:1≤H
 bank:Ready B.ledger.seats P.B f m ψ θ γ
 price:0≤Q
 height:s>0
 roof : s ≤ m
 opt (i:I)(S:Aura n):Medal P S.val ∅ (C.firstAt S F l i) H (R i S)
 sum(o:Seat n):tallB (fun S:Aura n=> ∑ i:I,R i S) P.B m o≤ c
 charge:0<grantW Q ψ γ+c
 budget:degreePrice P.B (grantW Q ψ γ+c) s<1
abbrev gLease (Q s c ψ γ:ℝ)(B:ℕ):= degreePrice B (grantW Q ψ γ+c) s

namespace Revenue
-- preserve exact tonic under all Key operations independent of actual Pane.
variable {I J:Type}[DecidableEq I][Fintype I]{n:Side} {F:ForceBudget n}{P:BudgetPoint} {H:ℝ} {δ:ℕ}
variable {b:Force n→ℝ}{V:I→ Firing n}{a:I→ℝ}{B:Chart I (Seat n)}
variable {C:B.Stoke δ P H V a} {Q s c m ψ θ γ:ℝ}
variable {f:I⊕ Force n→ℝ} {R:I→ Aura n→ℝ}{l:List I} (r:Revenue C F b Q s c m ψ θ γ f R l)
include r
local notation "hs"=> sub_nonneg.mpr r.roof
local notation "hμ"=> (r.height.trans_le r.roof).le
local notation "Φ"=>glow B f Q R
local notation "γk"=> gLease Q s c ψ γ P.B
local notation "Bw"=> grantW Q ψ γ
local notation "uK"=> grantW Q ψ γ+c
lemma hue : Ready Palot.stern P.B Φ (m-s) (grantW Q ψ γ+c) s (gLease Q s c ψ γ P.B):= running C r.blizzard l (zero_le_one.trans r.font) r.ext r.simple r.complete f m Q r.bill r.bank R r.opt r.price (r.height.trans_le r.roof).le r.sum (by ring) r.height r.charge r.budget
variable [LinearOrder J][Fintype J](σ:J→Seat n)(ρ:I→J)(g:B.anchor=σ ∘ ρ)
local notation "Γ"=> Cipher n
open Mew Vow Rive
local notation "Ω₀"=> C.furnish l ρ F
local notation "αR" z:max=> kiosk (C.furnish l ρ F z)
def pathT (q:Key J):= FeeD P (kiosk (C.furnish l ρ F q))
-- implicit r? pathT not actually referenced r; include doesn't work defs. 
local notation "Υ"=> pathT (C:=C) (F:=F) (l:=l) ρ
local notation "uA" => pack B Q f
lemma places (z:Key J)(h:z∈hill J):∀ X:Aura n, Medal P X.val ∅ ((αR z) X) H (Φ X):= C.first_all r.blizzard l (zero_le_one.trans r.font) r.ext (z∘ρ) r.simple r.complete f m Q r.bill r.bank R r.opt r.price (r.height.trans_le r.roof).le (fun i=> hill_i.mp h (ρ i))
lemma blaze (z:Key J)(h:z∈hill J) : ArmsK P (C.furnish l ρ F z) (pack B Q f) H := C.full_arms r.blizzard l (zero_le_one.trans r.font) r.ext (z∘ρ) r.simple r.complete f Q r.bill (fun i=>hill_i.mp h (ρ i)) r.peg
lemma flagged (o:Seat n) : tallB (Vow.hymn uA) P.B (m-s) o ≤ grantW Q ψ γ:=by
 let t(k:Aura n):= Vow.hymn (pack B Q f) k; have hv:0≤t:= fun i=> sum_nonneg fun D _=> pack_nn f m Q r.bank r.price i D
 exact (Larch.tall_m t hv (sub_le_self m r.height.le) o).trans (degree_sums f m Q r.bank r.price (r.height.trans_le r.roof).le o|>.1)
lemma grow_zero (z:Key J)(hz:z∈hill J) (S:Aura n) : Medal P S.val ∅ (Υ z S) H (spanD S Φ 0):=glenP S r.font (places r ρ z hz) r.hue (sub_nonneg.mpr r.roof) 0
lemma size_zero (o:Seat n): tallB (fun i:Aura n=> spanD i Φ 0) P.B (m-s) o ≤ (grantW Q ψ γ+c)*(1-γk)⁻¹:=by simpa only [pow_zero,mul_one] using (thinX r.hue (sub_nonneg.mpr r.roof) o 0)
lemma looks (X:Aura n)(x:Orbit n): River (fun z:Key J=>Υ z X x):= lore_Y (fun z:Key J=> kiosk (C.furnish l ρ F z)) P r.font (fun X x=> C.operates X ∅ l x ρ) (fun _=>Φ) hs (fun _ _=>r.hue) (places r ρ) (ready_pos _ _ r.hue|>.le) r.budget X x -- maybe vertical order
include g
lemma fades (i:Aura n): Hush σ i.val (fun z=> (Υ z) i):= lore_H (fun z:Key J=>kiosk (Ω₀ z)) P σ (fun x=>C.hush_f x ∅ l σ ρ g) i
lemma at_first (i:Aura n)(j:J)(x:Orbit n):tipI (fun z:Key J=> (Υ z) i x) [j]= zenS P i.val ∅ (C.pin l ρ F j i) x:=by
 let X:=update (0:Key J) j 1
 have hX:X∈hill J:=fill_I roots j (mem_closedBall_zero_iff.mpr (by rw [norm_one])) -- tune
 let d:= (αR X); have hp: kiosk (C.furnish l ρ F X)=C.pin l ρ F j:=by rw [C.pin_single l σ ρ g 1 j,one_smul]
 have ht:= Carbon.token P i x r.hue hs (places r ρ _ hX) r.font
 have he:= mitt (looks r ρ i x) roots j
 rw [hp] at ht;
 change Mew.cutI (fun z:Key J=>Υ z i x) _ _= _; refine he.unique ((show HasDerivAt _ _ _ from ?_)); refine ht.congr_of_eventuallyEq (Eventually.of_forall fun x=>?_); unfold pathT; dsimp only; rw [C.pin_single l σ ρ g]
omit g
lemma ceramic (z:Key J):Bake.Turf (Υ z):= Bake.turfK _ (C.operatingT l ρ z)
lemma stowed : Υ 0=0:=by change FeeD P (kiosk (C.furnish l ρ F 0))=0; have hp:kiosk (C.furnish l ρ F 0)=0:= C.zeroLake r.blizzard ..; rw [hp,fog]
end Revenue
end YM.CF.Coil.Chart.Stoke
open YM.CF.Coil.Chart.Stoke
#print axioms Revenue.at_first
#print axioms Revenue.stowed
#print axioms Revenue.pathT
