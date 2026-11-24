import Merino.Waist
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1200000
set_option synthInstance.maxSize 28000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Merino
open Filter Topology Lattice Lat Tulip Branch Cube Tenant Drapes Metric
open _root_.Zephyr.Chern
open scoped Matrix Matrix.Norms.L2Operator Classical
attribute [local instance] opCStarAlgebra
open Finset Swell

variable {n:Side}

open Py.Rate.LocalLimit Preparation Buffered.Afterglow.Tower.VacuumSelection
open Skye Scree Vale RG
open Py (hueW stemS pinpr)
variable (P:Spine)


variable (m:ℕ)(p:Bolts)(z:Cover)

variable (s i k:ℕ)
local notation "N"=> RegNum P s i
local notation "K"=> LoomM P s i
local notation "R"=> LedgerM P s i k


local notation "axes" => List.ofFn (id:Axis→Axis)
abbrev fullTest : ℝ→ℂ:=
  (hueM P s:ℂ) • stripFee m z axes P s i k

/-- Includes the factor for (129). Test the physical scalar-part
ALONE (pure gauge), the one used in the stencil whose price is paid. -/
abbrev dressTest (d:Dress P s i k p m (wrap N z)): ℝ→ℂ:=
  (hueM P s:ℂ) • display (stream N) (R).p K d.y.post d.y.color

def Glowing (δ E:ℝ)(d:Dress P s i k p m (wrap N z)):Prop:=
  Regalia (fullTest P m z s i k) (dressTest P m p z s i k d)
    (hueM P s * δ) (hueM P s * (E * (loseM P p.a s*p.c)))



private lemma dress_grade {δ E:ℝ}
    (h:Oily p.a P.par.d (breadth z) E)
    (hw:δ+ E*(loseM P p.a s*p.c) < (bud (stripFee m z axes P s i k) 2).re)
    (d:Dress P s i k p m (wrap N z)):
    Glowing P m p z s i k δ E d:=by
  have e:=d.ticket.hem.sip
  change Trunk (node d.y.origin) _ _ _ _ _ at e
  rw [d.here] at e
  have hh:=glaze_price
    (F:=fun U=> (funde P.par.K.j (R).J.M N U-Dial.tickA N)*windmill (wrap N z) m)
    d.hot.sky e h (deep_grace z) d.wane d.glaze_funds hw
  unfold Glowing dressTest Spool.post
  rw [d.here]
  exact hh.scale (hue_positive P s)

/-- All choices pass, not requiring even the `kick` bound
other than to claim d as a Dress. -/
lemma gleams (h:SprigFee P)(hm:0 < m) :
    ∃ δ E:ℝ,0<δ∧0<E∧∀ᶠ s:ℕ in atTop,∀ i k:ℕ,∀ d,Glowing P m p z s i k δ E d:=by
  obtain ⟨v,w,S⟩:=strip_fee h hm axes z
  obtain ⟨E,⟨e⟩⟩:=oily p.decay P.par.dpos (breadth z)
  have t: Tendsto (fun s=>E*(loseM P p.a s*p.c)) atTop (𝓝 0):=by
    simpa only [zero_mul,mul_zero] using (((lose_limit P p.a p.decay).mul_const p.c).const_mul E)

  refine ⟨v/2,E,half_pos w,e.bound,?_⟩
  filter_upwards [S,t.eventually (gt_mem_nhds (half_pos w))] with s g f i k
  exact dress_grade _ _ _ _ _ _ _ e (by linarith [(g i k).2])

def shines:Prop:=∀ z:Cover,∃ δ E:ℝ,0<δ∧0<E∧
   onReg P (fun u j l=>∃ d,Glowing P m p z u j l δ E d)
/-- Actual buyer for a witnessed fee. -/
lemma litUp (h:SprigFee P)(hm:0 < m)(l:woven P m p):shines P m p:=by
  intro z
  obtain ⟨δ,E,a,b,c⟩:=gleams P m p z h hm
  refine ⟨δ,E,a,b,?_⟩
  unfold onReg; unfold woven onReg at l
  filter_upwards [l,c] with s u v
  filter_upwards [u] with i g k r
  exact ⟨(g k r _).some,v ..⟩
end YM.CF.Merino
