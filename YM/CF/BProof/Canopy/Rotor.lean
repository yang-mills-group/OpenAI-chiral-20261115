import YM.CF.BProof.Digit.Future
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
open Levier Salt Ione Nacre BondL
open scoped YM.CF.Mew YM.CF.Sour.Axial
-- rank existential and difference plan. Real only
variable {T S:BeatL n}{U:Scree.Loom n}{R t d a b c W z₀ z₁:ℝ}{q:ℕ} {m:Cash P}
structure Trial (T S:BeatL n)(P:BudgetPoint)(U:Scree.Loom n)(q:ℕ)(t d W z₀ z₁ a b c Wk:ℝ) where
 k:Arbor P U q t d W z₀ z₁
 F:BondL T S (body_Q (N:=n) 1) b c a d
 pf:pureB F 1
 tag:∀ r:ℝ,0<r → TagT T S (body_Q (N:=n) r) d
 M:Male
 T₀:Finset (Scree.Hub n)
 j:ℕ
 ok:1≤j
 u:1≤P.power
 l:Haro.liveB T₀
 hl:∀ i:Scree.Hub n,coverNumber P.B i.val.2≤1→i∈ T₀
 z:Lens Wk
 Tp:Ids n
variable {Wk:ℝ}(Y:Trial T S P U q t d W z₀ z₁ a b c Wk)
structure Stream (n: Side) where
 B:Cusp n
 E:RegBudget n
 Q:Cusp n
 L:ℝ
 Υq:ℝ
structure Stream.Bears (B:Stream n)(P:BudgetPoint)(m:Cash P)(δ:ℕ)(W e:ℝ) : Prop where
 bark:Quir m B.B δ W
 mark:Bake.Turf (Fine B.B)
 prior:∀ (s:Sweep n)(i:Aura n)(V:Orbit n),Injective (priorP V.2)→∀ D⊆i.val,B.B (moldA s i) (actY s D) (yellA s V)=suit_Y s (B.B i D V)
 Ω: Sym_a (Fine B.B)
 core: PreR P B.B B.E B.Q B.L W B.Υq e
abbrev board (P:BudgetPoint)(R W a b c:ℝ):= φcape P a (knot R b) (knot R c) W
abbrev yard(P:BudgetPoint)(R W:ℝ):= cap1 P (øK (cQ*R)) W
abbrev due (m:Cash P)(e R W a b c:ℝ):= e+board P R W a b c+m.Tr+yard P R W
structure Reservoir (P:BudgetPoint)(m:Cash P)(R W a b c e Wk:ℝ) : Prop extends LoomPay P m R W a b c where
 pole:0<Wk
 pay:0<e
 year: R=8*tiltB Wk P*e/W^2
 port: board P R W a b c ≤ e/16
 post:m.Tr ≤ e/32
namespace Trial
local notation "F"=> Y.F
local notation "k"=> Y.k
abbrev flow (B:Stream n):SpaceM→Cusp n:= rotor Y.k Y.F B.B
abbrev cash (B:Stream n)(Q:SpaceM): RegBudget n:= B.E + tuneW k F Q+cast_E (wave k F B.B Q) Y.Tp
abbrev hz (B:Stream n)(Q:SpaceM): Op SU.Slot:= zeus Y.j Y.M (heroP (StackL (cash Y B Q) Y.T₀))
variable {e:ℝ}{B:Stream n}(h:B.Bears P m (cipherK q) W e)(p:Reservoir P m R W a b c e Wk)[Nonempty (ΘS R)]
local notation "A"=> orchard F R p.fp.le
local notation "φ"=> board P R W a b c
variable (i: ΘS R)
lemma flow_eq : (A).pivotS (k).tile (k).pos W B.B (k).hw (k).hv (k).y (k).hx (k).v (k).w (k).paid i= Y.flow B i.val:=by rw [pivotS,goalJ k F p.fp.le i]
lemma pre_c : (A).uDa (k).tile (k).pos W (k).hw B.B (k).paid (k).hv (k).y (k).hx (k).v (k).w i B.E Y.Tp= cash Y B i.val:=by unfold uDa; rw [goalW k F p.fp.le i,goalZ k F p.fp.le i,flow_eq Y p i]
-- axial arithmetic
include p
lemma expect_δ (h:1≤ W): tiltB Wk P / W^2*e=R/8:=by rw [p.year]; ring
lemma cost (h:1≤W): Wk*((4:ℝ)^P.power*((2:ℝ)^P.power*(16*(e+φ+m.Tr))/W^2))≤R:=by
 let C:=tiltB Wk P/W^2; have hc:0 ≤ C:=by unfold C tiltB; have h:=p.pole; positivity
 have hh: e+φ+m.Tr≤8*e:= by linarith only [p.port,p.post,p.pay]
 rw [show Wk*_ = C*(e+φ+m.Tr) from (show Wk*_ = _ from (by unfold C tiltB; ring))]; exact (mul_le_mul_of_nonneg_left hh hc).trans_eq (by unfold C; rw [p.year]; ring) -- rewriting dependent R? no
include h
lemma gamble :∃ j:ΘS R,Haro.riseV j=hz Y B i.val∧ BondL.PickZ P (flow Y B i.val) (cash Y B i.val+tuneL k F j.val) B.Q Y.T₀ Y.M Y.j B.L W B.Υq (due m e R W a b c) (m.κ⁻¹*m.Γr) m.γr wΨ (i=j) :=by
 let W':= (k).hw; let w':=zero_le_one.trans W'
 obtain ⟨v,w⟩:= h.bark.prices w'; have he:=(kernel_p k F p.fp.le i).dice; have z:= Cash.clock p.toWarrant w (cop F p.toLoomPay) W' he
 obtain ⟨l,v,e⟩:= (A).see_K (k).tile (k).pos W W' B.B (k).paid (k).hv (k).y (k).hx (k).v (k).w w.fr h.mark h.prior z (Cash.Φk P) Cash.Ψk (Cash.ΦΨ P) (cQ*R) (pureC F p.fp.le Y.pf) wΨ m.sh m.z m.γr Cash.Ψk le_rfl (Leaf.price w (Cash.uv P) w').lien p.s p.ht p.earn p.wings p.aa p.ny p.ab h.Ω Y.l Y.hl Y.M Y.ok Wk Y.z B.E B.Q h.core p.fp Y.u (cost p W') i Y.Tp
 rw [pre_c Y p i] at e v; rw [flow_eq Y p i,goalL k F p.fp.le l] at e; exact ⟨l,v,e⟩ -- tune name conflicts
lemma edge : EdgeC P (k).tile (k).pos T S B.B (flow Y B i.val) (riseV i):=by
 obtain ⟨v,w⟩:= h.bark.prices (zero_le_one.trans (k).hw); rw [←flow_eq Y p i]; let z:=Cash.clock p.toWarrant w (cop F p.toLoomPay) (k).hw (kernel_p k F p.fp.le i).dice
 constructor
 intro x hx X Y' V hy pX t a b
 exact startP (A) (k).tile (k).pos W (k).hw x i B.B (k).paid (k).hv (k).y (k).hx (k).v (k).w w.fr h.mark h.prior z (Cash.Φk P) Cash.Ψk (Cash.ΦΨ P) X Y' V hy pX t (Y.tag R p.fp) hx a b
noncomputable def onZ : ΘS R:= (gamble Y h p i).choose -- order duplicate
lemma on_tag : Haro.riseV (Y.onZ h p i)= hz Y B i.val:= (gamble Y h p i).choose_spec.1
end Trial
end YM.CF.Sour.Digit
