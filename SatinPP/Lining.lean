import SatinPP.Octave
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3500
set_option maxHeartbeats 650000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open Lamour.Bridge.Celeste.Morn
namespace Spine
open Aria Casting Six MacroGrid

variable (P:Spine)
local notation "J"=>((hyperfilter ℕ):Filter ℕ)
local notation "c"=> P.sidesPerTick
local notation "F%" s:max=> P.pointEra s
private lemma coloring {α:Type} [Finite α](g:ℕ→α):∃ a,∀ᶠ n in J, g n=a:=by
 by_contra! h
 have t:∀ᶠ n in J,∀ a,g n≠a:= eventually_all.mpr h
 obtain ⟨n,e⟩:=t.exists; exact e _ rfl
private lemma thinning {p:ℕ→Prop}(q:∀ᶠ n in J,p n):
 ∃ s:ℕ→ℕ, StrictMono s ∧ ∀ n,p (s n):= by
 have hx(k):∃ n,k<n ∧ p n:= ((Filter.Eventually.filter_mono (f₁:=J) Nat.hyperfilter_le_atTop (eventually_gt_atTop k)).and q).exists
 choose g h t using hx
 let s:ℕ→ℕ:= Nat.rec (g 0) fun _ v=>g v
 exact ⟨s,strictMono_nat_of_lt_succ (fun n=>h _),fun n=>by cases n<;> exact t _⟩
def Synchrony(f g:ℕ):Prop:=∀ᶠ v in atTop,P.granule (P.megaK f v)=P.granule (P.megaK g v)
private def profileTint(s v:ℕ): Fin c:= ⟨(P.megaK (F% s) v) % c,Nat.mod_lt _ P.sides_pos⟩
private lemma tint_pay {i m:ℕ}(e:∀ᶠ v in J,P.profileTint i v=P.profileTint m v):P.Synchrony (F% i) (F% m):= by
 obtain ⟨v,g,h,q⟩:= ((Filter.Eventually.filter_mono Nat.hyperfilter_le_atTop (eventually_ge_atTop (F% i))).and ((Filter.Eventually.filter_mono Nat.hyperfilter_le_atTop (eventually_ge_atTop (F% m))).and e)).exists
 have he:Nat.ModEq c (P.megaK (F% i) v) (P.megaK (F% m) v):=congrArg Fin.val q
 filter_upwards [eventually_ge_atTop v] with r h'
 have u(f)(t:f≤v): P.megaK f r= (P.par.R.L.val)^(r-v)*P.megaK f v:= by unfold megaK;rw [show r-f=r-v+(v-f) from by omega,pow_add,mul_assoc]
 have y:Nat.ModEq c (P.megaK (F% i) r) (P.megaK (F% m) r):=by rw [u _ g,u _ h];exact he.mul_left _

 have z: Int.ModEq (c:ℤ) (P.megaK (F% i) r) (P.megaK (F% m) r):= by unfold Int.ModEq; rw [←Int.natCast_emod,←Int.natCast_emod];exact congrArg ((↑) :ℕ→ℤ) y
 have hv:= z.sub (Int.ModEq.refl (P.uniformFoot:ℤ))
 unfold Int.ModEq at hv;unfold granule persistN;rw [hv]
lemma calendar_tint: ∃ s:ℕ→ℕ, StrictMono s ∧ ∀ i m,P.Synchrony (F% (s i)) (F% (s m)):= by
 choose g h using fun s=>coloring (P.profileTint s)
 obtain ⟨a,v⟩:=coloring g
 obtain ⟨s,u,w⟩:=thinning v
 refine ⟨s,u, fun i m=>P.tint_pay ?_⟩
 filter_upwards [h (s i),h (s m)] with j p q; rw [p,q,w i,w m]


lemma calendar_fringes : ∀ᶠ i:ℕ in atTop,∃ᶠ m:ℕ in atTop, P.Synchrony (F% i) (F% m):= by
 choose g h using fun s=>coloring (P.profileTint s)
 have ht:∀ᶠ n:ℕ in atTop,∀ v:Fin c, g n=v → ∃ᶠ k:ℕ in atTop,g k=v:= by
    refine eventually_all.mpr fun v=>?_
    by_cases H': ∃ᶠ k:ℕ in atTop,g k=v
    · exact Eventually.of_forall fun i _=>H'
    push Not at H'
    exact H'.mono fun _ p q=>(p q).elim
 refine ht.mono fun i q=>(q _ rfl).mono fun m z=>P.tint_pay ?_
 filter_upwards [h i,h m] with v p r; rw [p,r,z]

