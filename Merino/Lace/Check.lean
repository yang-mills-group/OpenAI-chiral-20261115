import Merino.Garter.Pearl
import Merino.Lace.Wick
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
set_option synthInstance.maxSize 28000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Merino.Garter
open Function Lattice Finset RG Wilson Metric Exterior Work.F03
open Regis.Head MeasureTheory
open scoped Topology ContDiff InnerProductSpace Classical Matrix.Norms.Frobenius
variable {n:Side}{G:Gauge}

open Cuff Hem
variable {I:Type*}
open Tree Filter Precision Next.Rank.Spindle Pressure ProbabilityTheory
open Gleam Next.SectorChange Next.SectorChange.Gaussian
open Etch -- (includes river)
open StepIn
variable {c:Side}{r:Ratio c n}{H:Bed}{m:ℕ}{p:BudgetPoint}{q:Clip}{v η S C δ w β:ℝ}{A:Support c}{N:Finset (Cell n)}{Z:PathData G}

open clocks Py.Rate.LocalLimit Preparation Papal Lat Tulip Branch Cube Tenant Drapes Vale
variable {D:Preparation}{j₀:ℕ}(Y:Course D (VolumeCape.Dream.Nimbus j₀))
open Lace




lemma warmIdee(D:Preparation):0<D.K.C:=by
 let M:=D.V.L.H 0
 have f:=(D.V.L.roof 0)
 let a:=plaquette (show PlaqAxes from ⟨(0,1),by decide⟩)
 have u:= (M.metric.constant_strip f.1.2.1 a a).estimate
    0 (by intro i;simpa using D.K.width.le)
 change ‖M.metric.read 0 a a‖≤_ at u
 rw [(f.2.1 D.R.L).starts] at u
 simp only [Matrix.one_apply_eq,norm_one] at u
 exact zero_lt_one.trans_le u

local notation "N₅"=>SU.group
lemma bounty(L α:ℝ)(f:Stripe SU.group→ℝ)(h:0<α):
 ∀ᶠ t in atTop, ∀ (s i k:ℕ), let n:=More (count Y s i); ∀ {m},
 Steam n t → Reach t m→ ∀ T:Bundle SU.group n, α≤dripQ T (f∘ridge) (f∘ridge)→
 Sheath 0 m L T→leadCoin f α≤ miles t ^8 * chat Y s i k T (showtime n t):= by
 let W:=D.V.L
 filter_upwards [burning N₅ D.K.top.clip L D.V.W.parcel (warmIdee D) D.K.width _
      (shines f α h)] with t p
 intro s i k n m q r T A u
 have h₀:Even n.val:=⟨_,by change _*2=_;rw [Nat.mul_two]⟩
 have f':=W.roof (Y.uv k-s)
 exact illum_charge _ _ T _ _ _ h A (p r q h₀ f'.1 (f'.2.1 _) (f'.2.2 _) _ _ T u)
end YM.CF.Merino.Garter
