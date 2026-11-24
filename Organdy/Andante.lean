import Organdy.Moon
import Organdy.Lemon
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.flexible false
set_option synthInstance.maxSize 24000
set_option maxRecDepth 6000
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Organdy.Royal
open Buffered Buffered.Afterglow
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Pastry Tenant Tower

open VacuumSelection


open Lamour.Bridge.Celeste Lamour.Bridge.Celeste.Clock
open CF.Pannier.Chancel Hookah Tapestry

open Yoke Yoke.Bazaar
open Optic
open Larva (Chip Domaine dint)
open Hookah.Rake
open Pressure Worth BProof
open Papal


variable {P:Spine}{s:ℕ}{c:Cuts}
local notation "H" => (P.calibration)
local notation "gu" => guineas P s
local notation "w✽" => webX (gu)
local notation "g'" => (shaft P s+6)
local notation "A'" => premium argent c.γ
local notation "ℰ"=> meterC (gu)
local notation "h'"=> knock (gu)
local notation "S'"=> station P s

local notation "w✤" => walkF (gu)
local notation "ε₁" => yieldt (gu)


section
variable {i k:ℕ}
local notation "N'" => kitGap P s i
lemma Candies.sustained {W:Pane (N')→ℂ}{A:Treasure (N')}{z:Seat (N')}
 (q:Candies P c s i k W A)(m:AmberMood P c s)
 {a t:ℝ}(p:|a|≤h')
 (r:a*candles P s i k A z + Optic.toll gu + ε₁ ≤ t):
 Sustained H w✤ 0 (floral W z g' gu a) (take P s i k) (Real.exp t) (portrait gu):=by
 refine ⟨fun v h x=>Broach.early q.reassure m.port p h x,
    fun L b d=>?_⟩

 apply le_trans (q.grant z _ p _ ⟨b.core,b.annex⟩)
 rw [←Real.exp_nat_mul]; apply Real.exp_monotone
 have j: sites (N') ≤ (L.length:ℝ)*(4*((walkF gu:ℝ)+addgap H))^4:=by unfold sites; exact_mod_cast d.2
 have h:=m.fund
 refine le_trans (add_le_add_left (mul_le_mul_of_nonneg_left j (show 0≤14*ℰ from mul_nonneg (by norm_num) (coin_pos ..).le)) _) ?_ -- add_le_add_left notation?

 let y:=(L.length:ℝ)
 have q1:=(mul_le_mul_of_nonneg_left h (Nat.cast_nonneg (α:=ℝ) L.length))
 have q2:=(mul_le_mul_of_nonneg_left r (Nat.cast_nonneg (α:=ℝ) L.length))
 linarith only [q1,q2]
end


variable {I:Type}{u:Ultrafilter I}{d:Stores}{i k:I→ℕ}
 {X:Suits P s i}{F:PackE I P}{x:Lot P}
local notation "uf" => (↑u:Filter I)
local notation "W" => raw P s i k X
local notation "G'" => (∀v,Treasure (tunnel P s i v))


lemma Parade.review(p:Parade uf P c d s i k X F x):
  ∃ A:G', ∀v, aims P c s (i v) (k v) (W v) (A v):=by
 choose A h using fun v => ((p.vintage v).fil.classic _ _ _ _ (p.slot v).toSquid.toKit).1
 refine ⟨A, fun v=>⟨?_,(h v).tint⟩⟩
 have j:=(h v).plate
 rw [(p.vintage v).reef.clearing.radius,(p.vintage v).reef.clearing.sphere] at j
 exact j


abbrev lunar (P:Spine)(s:ℕ)(i k:I→ℕ)(B:∀ v, Treasure (tunnel P s i v)) (D:ℕ) (v:I) :=
 candles P s (i v) (k v) (B v) (ice _ D)


variable {A: ∀v,Treasure (tunnel P s i v)}
 (m:AmberMood P c s)
 (p:Parade (↑u:Filter I) P c d s i k X F x)
 (q:∀v, aims P c s (i v) (k v) (raw P s i k X v) (A v))

local notation "T"=>((c.cost*clipper gu)^2)
local notation "ℛ"=>lunar P s i k A


include q
lemma highs:
 ∃ J:ℕ→ℝ,∀D:ℕ,|J D|≤T∧Tendsto (ℛ D) uf (𝓝 (J D)):=by
 have h(D:ℕ)(v): |ℛ D v|≤T:=monetary_lid _ _ _ _ _ _ _ (q v).1.purse
 choose J a b using fun D=>(isCompact_Icc (a:=-T) (b:=T)).ultrafilter_le_nhds' (u.map (ℛ D)) (show ∀ᶠ v in uf,ℛ D v ∈ Set.Icc (-T) T from Eventually.of_forall fun v=> abs_le.mp (h D v))
 exact ⟨J,fun _=>⟨abs_le.mpr (a _),b _⟩⟩

include m p
lemma awardsSoon:
  ∀ᶠ z in uf, Candies P c s (i z) (k z) (W z) (A z):=by
   have t: ∀ᶠ z in uf,∀ w B,aims P c s (i z) (k z) w B→Candies P c s (i z) (k z) w B:=
      p.rate.both (B:=fun i k=>∀ w b, aims P c s i k w b→Candies P c s i k w b) m.bill
   exact t.mono fun i h=>h _ _ (q i)
variable {r:ℕ}{v:ℝ}
lemma hallmark (e:Plait w✽ r)(t:Tendsto (ℛ r) uf (𝓝 v)): A'≤(r:ℝ)^8*v:=
 ge_of_tendsto (t.const_mul _) ((awardsSoon m p q).mono fun z h=> h.proof _ e)

lemma torch {a:ℝ}(y:|a| ≤h')(t:Tendsto (ℛ r) uf (𝓝 v)):
 Rendered uf P s i k w✤ 0
   (fun j=>floral (W j) (ice _ r) g' gu a)
        (a*v + Optic.toll gu + 3*ε₁):=by
 have tt:= ((t.const_mul a).add_const (Optic.toll gu)).add_const ε₁
 have h:(a*v + Optic.toll gu + ε₁) < (a*v + Optic.toll gu + 3*ε₁):=
    add_lt_add_of_le_of_lt le_rfl (by linarith only [show 0<ε₁ from coin_pos ..]) -- add_lt_add
 refine ⟨_,portfolio gu,?_⟩
 filter_upwards [awardsSoon m p q, tt.eventually (ge_mem_nhds h)]
   with j l e
 exact l.sustained m y e
#print axioms torch
