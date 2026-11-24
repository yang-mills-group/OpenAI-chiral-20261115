
import Organdy.Thrill
import Organdy.Pond
import Organdy.Bandstand
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.flexible false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Organdy
open Function Filter Topology Lattice Wilson Fock Pastry Scree Sault Sour Stax Skye Jet NormedSpace Scroll Finset Palot Cadre Vow
open RG Mew Rive Nor Hake MeasureTheory Bake Rue Salt
open Metric Drapes Tulip Lat Branch Cube Tenant
open Rush SU Prism Nacre Laic Tap Levier Thera Moto Oath Font Haro Spire Dial Rill
open Kennel
open Swell StressExchange Buffered
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra


open Larva _root_.Zephyr.Chern

-- projection of actual mask. Flash includes det-odd CC.
variable {N:Side}{K:Scree.Loom N}{p:BudgetPoint}{X:SOp N}
def rayon (s:Signed)(K:Scree.Loom N)(p:BudgetPoint)(X:SOp N)
 (U:Pane N):= ebony s * chime K p (node 0) X (flashA (polestar N s) U)

def scint (K:Scree.Loom N)(p:BudgetPoint)(X:SOp N):= honeycomb (fun s:Signed=>rayon s K p X)

abbrev sch (s:Signed)(K:Scree.Loom N)(p:BudgetPoint)(X:SOp N):=fun U=>ebony s * audible s K p X U

variable {r d a b c D δ:ℝ}
-- P.n record
lemma gloss (s:Signed)
  (f:StageSet K p d)(u:Trunk (node 0) X (p.B/10) a b d)(e:0≤a)

  (A:Dye N)(g:Sidelight (p.B+6) r p.threshold c D δ (sch s K p X) A):
  ∃ B,Sidelight (p.B+6) r p.threshold c D δ (rayon s K p X) B:=by
 have h:rayon s K p X=cSignX (detX s) ∘ sch s K p X:=by
    funext x
    have h:=congrFun (cassette_reads f u e (polestar N s)) x
    change cSignX (detX s) (audible s K p X x)=chime K p _ X _ at h
    rw [rayon,←h]
    simp only [cSignX,sch,Function.comp_apply,ebony]
    cases detX s <;> simp
 rw [h]
 cases detX s
 · -- goal after cases sch still s
   exact ⟨_,g⟩
 exact ⟨_,g.charge⟩

open Next.Rank.Spindle in
lemma opal
  (z:4*(p.B/10+2)+1<N.val)
  {R:Rules SU.group}
  (t:Sky (More N) d r a D p.threshold (p.B/10) R)
  (f:StageSet K p d)(u:Trunk (node 0) X (p.B/10) a b d)
  (e:0≤a)
  (g:∀s,Audio p a c δ s (audible s K p X)):
  ∃ A, Sidelight (p.B+6) r p.threshold
    (c*Real.exp (-a*((p.B/10:ℕ):ℝ))) (D*(Tenant.quota^2*b)) δ
    (scint K p X) A:= by
   let v:=p.B/10
   let H:=c*Real.exp (-a*(v:ℝ))
   let d':=D*(Tenant.quota^2*b)

   have J(s):∃ A, Sidelight (p.B+6) r p.threshold H d' δ (rayon s K p X) A:=by
     let w:=polestar N s
     let o:=restL N s
     let Z:= julStep w X
     let hinge:=jul_trunk w u
     obtain ⟨A,y⟩:= pages hinge t
     have l:=trunks_canal hinge e
     let L:=dressing f
     have i:=rest_short (N:=N) s
     have v0:‖chime K p o Z 1‖≤H:=(g s).scale
     have h:=silken l L t.flow y i v0
     have st: ∀ x∈stains o (p.B/10),separation x.1.1 1 ≤ p.B/10+2:= by
        intro x j
        refine (separation_triangle x.1.1 o 1).trans ((Nat.add_le_add ((separation_comm ..).trans_le (wet_iff.mp j))
          ?_))
        exact (separation_triangle o 0 1).trans (Nat.add_le_add ((separation_comm ..).trans_le i) sep1)
     obtain ⟨a',u'⟩:=stanza l L y st z
     refine gloss s f u e (ebony s • A) ?_
     have U:=h.weighted (ebony s)
     rw [norm_ebony,one_mul,one_mul] at U

     let p':=a'.bloom.scale (ebony s)
     obtain ⟨-,-,-,l'⟩:=Ink.dye_ink (ebony s) A h.inside h.sym
     have k': bud (sch s K p X ∘ petals (stream N)) 2=Ink.gilt (ebony s•A) (Larva.decree ∘ dot):=by
        change bud (fun x=>ebony s*(chime K p o Z ∘ petals (stream N)) x) 2 = _
        rw [p'.bud_eq,Pi.smul_apply,u',l',smul_eq_mul]
     exact ⟨U,p'.1,k', by rw [dint,←k'];exact (g s).pitch.price⟩
   choose A a using J
   exact ⟨_,Sidelight.total a⟩
