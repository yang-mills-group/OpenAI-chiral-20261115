import Bay.D.Conifer
import YM.Next.RANK.Ray
import YM.Planned.ATOM_REGULAR_ESTIMATE.Pin
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 3000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Bay
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour Stax Skye Jet Scroll Finset Palot Cadre Vow
open RG MeasureTheory Rue
open Metric Drapes Tulip Lat Branch Cube Tenant
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Rush SU Tap Levier Thera Oath Font Spire Dial Rill
open Kennel Swell

namespace D
open Exterior Precision Nacre
open scoped ContDiff
variable {N:Side}{d D r:ℝ}{S:Sa N}{F:Plank N d}{C:Toll (Single N)}

lemma pic_eq (q:Essay S C F){x z:Pane N}
    (a:profile x ∈ GateR N d)(b:profile z ∈ GateR N d)(h:Agrees S x z):
    picP F x=picP F z:=by
 let y:↥(GateR N d):=⟨_,a⟩;let w:↥(GateR N d):=⟨_,b⟩
 have he : F y = F w := Matrix.ext fun i j=>sub_eq_zero.mp (norm_le_zero_iff.mp (
   ((q.expo i j).variation y w).trans_eq (by change C i j * (fare _ (profile x) (profile z) / |d|)=0;rw [fareNil h];simp)))
 change equalizer _ y.val=equalizer _ w.val
 rw[in_pic,in_pic,pic,he]; rfl

open Next.Rank.Spindle Extra.Iteration.Channel

def rule : Rules group:= Classical.choice (charts _)
noncomputable def iceR(r:ℝ):ℝ:=min r rule.c
lemma ice_pos(hr:0<r):0< iceR r:=lt_min hr rule.radius
lemma log_extend {v:Pane N}{b:ℝ}
    (hx:∀ i, i.1∈S → group.chord (v i) ≤ b)
    (hb:0≤b)(h:b≤rule.c):
    ∃ y:Lag N, ‖y‖≤2*b ∧ Agrees S v (represent y):=by
 let z: Planned.AtomRegular.Link (More N)→Øc:=fun i=> if i.1∈S then group.plog (group.mat (v i)) else 0
 refine ⟨z ∘ (bondBody _).symm,?_,fun i h₁ h₂=>?_⟩
 · have h₃:0≤2*b:=by linarith
   apply (pi_norm_le_iff_of_nonneg h₃).mpr
   intro i; let u:=(bondBody (More N)).symm i
   change ‖z u‖ ≤ _
   unfold z
   by_cases hs:u.1∈ S
   · rw[if_pos hs]; exact (rule.sleeve _ ((hx u hs).trans h)).trans (mul_le_mul_of_nonneg_left (hx _ hs) (by norm_num))
   rw[if_neg hs,norm_zero];exact h₃
 rw[Work.F03.represent_link, Function.comp_apply]
 change _ = group.lieExp (z ((bondBody _).symm (bondBody _ i)))
 rw[Equiv.symm_apply_apply]
 unfold z
 rw[if_pos (show _∈S from h₁)]
 exact (rule.records (v i) ((hx _ h₁).trans h)).symm

lemma credit_pos(q:Essay S C F) : 0≤ledgerV C:=sum_nonneg fun i _=>sum_nonneg fun j _=>q.nonn i j
lemma bad_pay(q:Essay S C F)(v:Pane N):
    ‖picP F v‖≤ ledgerV C:=by
 unfold picP Jet.equalizer
 split
 · exact (essay_looks q).2.2 _
 simpa using credit_pos q

open Planned.AtomRegular.Foliage
variable {o:Seat N}{k:ℕ}{t:ℝ}
def frosty(k:ℕ)(t:ℝ):ℝ:= 8*(1+(k:ℝ))*t
lemma frost_inc{j:ℕ}(h:k≤j)(p:0≤t): frosty k t ≤ frosty j t:=by unfold frosty;gcongr

-- Anchor smallness, including exact equality case. Agreement with lit original suffices,
-- even if the priced input carries gauge noise right outside support.
lemma bright(p:Twine 3 d D r)(q:Essay S C F)
    {x v:Pane N} (a:profile x ∈GateR N d)(h:Agrees S x v)
    (j:∀i∈S,separation o i≤k)
    (l:Healthy t (roost (k+1) o) v) (ht:0≤t)
    (hb:frosty k t≤ iceR r) (w:2*(k+1)<(More N).val):
    ‖picP F x-picL F 0‖ ≤ (D*ledgerV C)*(frosty k t)^2:=by
 obtain ⟨g,hg⟩:=Cube.anchored o l ht le_rfl w
 let b:=4*(t*(1+(k:ℝ)))
 have bn:0≤b:=by unfold b; positivity
 have be:frosty k t=2*b:=by unfold frosty b; ring
 have ha(i:Planned.AtomRegular.Link (More N))(e:i.1 ∈ S): group.chord (Lattice.gauge g v i)≤ b:=by
   have hd:(↑(separation o i.1):ℝ)≤k:=by exact_mod_cast j _ e
   apply (hg i (j _ e)).trans;unfold b;gcongr
 obtain ⟨y,hy,H⟩:=log_extend ha bn (show b≤rule.c from (by rw[be];linarith only [bn] : b ≤ frosty k t).trans (hb.trans (min_le_right ..)))
 have he:‖y‖≤ frosty k t:=hy.trans_eq be.symm
 have h₁:= he.trans (hb.trans (min_le_left ..))
 have hv : Agrees S (Lattice.gauge g x) (represent y):=by
    intro i m n
    rw [Lattice.gauge,h i m n]
    exact H i m n
 rw [←pic_gauge q g x,pic_eq q (by rw [profile_g];exact o_act g _ _ a)
     ((p.pay F q _ h₁).2) hv]
 have hg:0≤ D*ledgerV C:=mul_nonneg p.dp.le (credit_pos q)
 exact ((touch p q).step h₁).2.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) he 2) hg)

end YM.CF.Bay.D
#print axioms YM.CF.Bay.D.bright
