import YM.CF.Pso.Nibs
import YM.CF.BProof.Floral.Crest
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
open Push.AbsoluteSums Trees Mew Floral
open scoped YM.CF.Mew
structure Cash (P:BudgetPoint) where
 κ:ℝ
 sh:ℝ
 sf:ℝ
 d:ℝ
 z:ℝ
 Γr:ℝ
 γr:ℝ
namespace Cash
variable (m:Cash P)
abbrev rate : ℝ:= degreePrice P.B m.γr wΨ
def er:= rentΦ P m.Γr m.d
def Nr:= uk_b m.er m.z m.γr m.rate
def Tr:= tintK P m.er m.γr m.z
structure Warrant : Prop where
 l:1≤ m.κ
 s:0< m.z
 zen:0≤ m.d
 star:m.sh+m.κ*m.sf < m.Γr
 lean:0≤ m.Γr
 tap:spanV P.B*m.Γr ≤1
 endP: spanV P.B*m.d≤ wΨ
 car:m.d+spanV P.B*m.d*m.Γr-(wΨ-spanV P.B*m.d)*m.Γr<0
 wings:m.sh+m.Γr+m.z*(m.d+m.er)≤ m.γr
 ht:0< m.γr
 earn:m.rate<1
end Cash
abbrev Fine (B: Vow.Cusp n): Pax n:=fun i=> B i ∅
variable {B: Vow.Cusp n}{Q: blazeK n}{W l a b:ℝ}{δ:ℕ}
structure Leaf (P:BudgetPoint)(Q:Aura n→ Support (More n)→ℝ)(F:Vow.Cusp n)(δ:ℕ)(W l a b:ℝ):Prop where
 fr:∀ X:Aura n,∀ D⊆ X.val, Fray P W δ X D (F X D) (Q X D)
 lien:HiveQ (urnL Q) P l a
 rent:HiveQ (Vow.hymn Q) P l b
namespace Leaf
variable (v: Leaf P Q B δ W l a b)
include v
lemma lives : ∀ X:Aura n,∀ D⊆X.val,Lives P δ X D (B X D):=fun X D p=> (v.fr X D p).loaf
lemma binder:Binder P W l (Fine B) a:= beauty.mpr ⟨urnL Q,fun X=> (v.fr X _ (empty_subset _)).merit,v.lien⟩
lemma cost : Flaws P W l B b:= Flaws.give.mpr ⟨Q,fun i D p=>(v.fr _ _ (Flaws.full_mem.mp p).2).merit,v.rent⟩
lemma price {q':ℝ}(d:q'≤l)(t:0≤ W): Leaf P Q B δ W q' a b:= ⟨v.fr,fun i=>(tall_m _ (fun x=>(v.fr x ∅ (empty_subset _)).merit.wage t) d i).trans (v.lien i),fun i=>(tall_m _ (fun x=>sum_nonneg (fun j p=>(v.fr x j (Flaws.full_mem.mp p).2).merit.wage t)) d i).trans (v.rent i)⟩
omit v
lemma appointed (p:∀ X:Aura n,∀ D⊆ X.val,Lives P δ X D (B X D))(t:Binder P W l (Fine B) a)(h:Flaws P W l B b): ∃ Q, Leaf P Q B δ W l a b:=by
 obtain ⟨J,S,L⟩:=beauty.mp t; obtain ⟨Z,H,Y⟩:=Flaws.give.mp h; let Q:Aura n→ Support (More n)→ ℝ:= fun X D=> if D=∅ then J X else Z X D
 refine ⟨Q,fun X D u=>⟨?_,p X D u⟩,?_,?_⟩
 · by_cases v:D=∅; subst D; rw [show Q X ∅=J X from if_pos rfl]; exact S X
   rw [show Q X D=Z X D from if_neg v]; exact H X _ (Flaws.full_mem.mpr ⟨nonempty_iff_ne_empty.mpr v,u⟩)
 · rw [show urnL Q=J from funext fun i=> if_pos rfl]; exact L
 rw [show Vow.hymn Q=Vow.hymn Z from funext (fun i=> sum_congr rfl (fun x u=> if_neg (Flaws.full_mem.mp u).1.ne_empty))]; exact Y
end Leaf
namespace Cash
variable {m:Cash P}{μ:Aura n→ℝ}{F:Bag n}{K:Rinse (Seat n) (Copy n)}
abbrev grapes (w:Cash P)(Q:blazeK n)(F:Cusp n)(δ:ℕ)(W:ℝ): Prop := Leaf P Q F δ W (wu P) w.sh w.sf
abbrev vines (w:Cash P)(Q:blazeK n)(μ:Aura n→ℝ)(t:ℝ): Prop:= Timer (Cadre.chip (cribR μ) Q) μ w.κ (wu P) wΨ (widthK n P.B) (spanV P.B) w.Γr w.d (spanV P.B*w.d) w.d t μ
variable (p:m.Warrant)(u:m.grapes Q B δ W)(d:HiveQ μ P (wu P+2) m.d)(w:1≤W) (s:Pitch P W δ K μ fun i Y=> F Y i)
lemma uv (P: BudgetPoint):ρL P≤wu P:=by unfold ρL wu wΨ; linarith
lemma Φk (P:BudgetPoint): 0≤ρL P:=by unfold ρL wΨ; linarith [P.exponent_pos]
lemma Ψk :0<wΨ:=by norm_num [wΨ]
lemma ΦΨ (P: BudgetPoint):ρL P+wΨ≤ wu P-wΨ*1:=by unfold ρL wu wΨ; linarith
include p u w d
lemma clock (s:0 ≤ μ):m.vines Q μ 1:=by
 apply Cadre.stallK _ p.l (wu P) wΨ (widthK n P.B) (vigor ..) m.Γr m.d Ψk.le μ Q (fun i D q=> (u.fr i D q).merit.wage (zero_le_one.trans w)) s _ p.zen (Nat.cast_nonneg _) p.lean p.tap p.endP _ (by unfold wu wΨ; linarith [P.exponent_pos]) p.car
 · intro i; rw [←parse,mul_zero,sub_zero]; exact d i
 intro i; rw [←parse,mul_zero,sub_zero,age_t]; exact lt_of_le_of_lt (add_le_add (u.lien i) (mul_le_mul_of_nonneg_left (u.rent i) (zero_le_one.trans p.l))) p.star
omit p u w d
lemma clock₂ (v:m.vines Q μ 1):m.vines Q μ 2:= {v with ok:=by norm_num, boot:=by unfold wu wΨ; linarith [P.exponent_pos]}
lemma lank (κ C l:ℝ)(h:1≤κ)(v:∀ X:Aura n,∀ D⊆ X.val,Fray P W δ X D (B X D) (Q X D))(w:HiveQ (roofL Q κ) P l C)(p:0 ≤ W):Leaf P Q B δ W l C (κ⁻¹*C):= ⟨v,fun i=>(lam_H Q i κ _ _ (zero_lt_one.trans_le h) (fun _ _ p'=> (v _ _ p').merit.wage p) (w _)).1, fun i=> (lam_H Q i κ _ _ (zero_lt_one.trans_le h) (fun _ _ p'=> (v _ _ p').merit.wage p) (w _)).2⟩
include p u w s
lemma heights (T:m.vines Q μ 1): Leaf P (Sco Q μ) (lamp (P:=P) B K) δ W (ρL P) m.Γr (m.κ⁻¹*m.Γr) ∧ Leaf P (ScoL Q μ) (rem_X (P:=P) B K) δ W (ρL P) m.er (m.κ⁻¹*m.er):=by
 obtain ⟨h,e,x⟩:= rentK _ _ u.fr K _ s _ _ _ _ _ _ _ _ _ _ _ T Ψk (Φk P) (ΦΨ P) w; let W':= zero_le_one.trans w
 refine ⟨Leaf.price (lank _ _ (wu P-wΨ*1) p.l (fun X D p=>(h _ _ p).1) ?_ W') ((le_add_of_nonneg_right Ψk.le).trans (ΦΨ P)) W',lank _ _ _ p.l (fun X D p=>(h _ _ p).2) ?_ W'⟩
 · intro i; rw [parse]; exact e i
 intro i; rw [show ρL P=ρL P-0*1 from by ring,parse]; exact x i
end Cash
end YM.CF.Sour.Digit
