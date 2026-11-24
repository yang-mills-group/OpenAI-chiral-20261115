import YM.SU5.FiniteGaugeData.Signal.Spritzer
import YM.SU5.FiniteGaugeData.Signal.Primrose
/-! # Active probe assembly. On native torus:
 `chamber = maskT * (1 + r_i c_i) (1+r_j c_j) ...`
 windows as in Boot, chiral. Expand into terms of defined physical observable
 shapes at width for observations. Keep color charges and absolute size needed
 for limit transfer. `maskT` compact bill. -/
set_option autoImplicit false
set_option maxHeartbeats 420000
set_option synthInstance.maxSize 16000
noncomputable section
namespace YM.CF.Signal
open Function Filter NormedSpace MeasureTheory Finset Lattice RG Wilson Fock Lat Cube SU Scroll Spire Tulip
open Window Mir Skye Scree Rush Dial Laic Thera Nacre Drapes Paige Vault Peaks Cascade Hive
open Buffered Buffered.Afterglow Buffered.Advance Reef Hom Tenant Branch Buffered.Concord Buffered.Afterglow.Satin Lifted
open MeasureTheory Push.SectorMeasure Girt
open scoped Topology ContDiff InnerProductSpace BigOperators Matrix MatrixOrder ComplexOrder Kronecker Classical Matrix.Norms.L2Operator ComplexConjugate Pointwise
attribute [local instance] opCStarAlgebra
open Supplies Sparkle Sparkle.Condense Sparkle.Portage Sparkle.Circuit Pastel Momentum Furnace
open Scherzo Kinetic
namespace Play
variable {n:Side}{x y z a b c u v H γ D:ℝ}{i j k q d r:ℕ}
variable (o:Seat n)(f: SU.Slot)(l:List (Site n)) (W:Finset (Site n))
-- operative gauge patch in which all observers live
local notation "Φ"=> family f
private def upperSet (V:Support (More n))(T:Finset (Site n)):= (univ.filter fun x:Site n=> node x∈V ∧ x∉T)

def floors(o:Seat n)(W:Finset (Site n))(r:ℕ): Finset (Site n):=upperSet (bay (terr (More n)) o r) W
local notation "L'"=> W.biUnion
local notation "S'" i => bay (terr (More n)) o i
lemma flo (x:Site n) : x∈floors o W d ↔ node x∈(S' d)∧ x∉W:=by simp only [floors,upperSet,mem_filter,mem_univ,true_and]

def maskT (Q:Support (More n))(v:ℝ) (f: Evaluation n) : Evaluation n:= Set.indicator {x|Healthy v Q x} f

def Baby(w:Site n) : Ket (Single n):= basisKet ((w,2),f)
lemma baby_to {w:Site n} (p: w∈ W): acts (cutM (colorsOne W f)) (Baby f w)=Baby f w:=within_basis _ _ (by simp [colorsOne,p])
lemma baby_fee (w: Site n): ‖Baby f w‖=1:=by simp [Baby,basisKet]
lemma baby_upper (w: Site n): acts (cutM (Tset n)) (Baby f w)= 0:=by rw [Baby,cut_basis,if_neg (mt (mem_Tset ..).1 (by decide: (2:SpinIdx) ∉ plusHalf))]
lemma clip (w:Site n): withinM (tube {w} (family f) {2}) (Baby f w):=within_basis _ _ (by simp [tube])
variable {p:Ket (Single n)}

lemma behind (v:withinM (tube W (family f) {2}) p): acts (cutM (Tset n)) p=0:= within_compl.mp (closedCut (fun i q=> (by obtain ⟨⟨i,j⟩,k⟩:= i; simp [mem_Tset,tube] at q ⊢; exact q.2.1.symm ▸ (by decide : (2:SpinIdx)∉ plusHalf))) v)
lemma prize_lift {U:Finset SpinIdx} (v:withinM (tube W (family f) U) p)(t:U ⊆ plusHalf): acts (cutM (Tset n)) p=p:=closedCut (fun i h=> (mem_Tset ..).2 (t (mem_filter.mp h).2.2.1)) v
lemma blendOne (g:Plum.Troupe n) : twist (tradew n g) (cutM (Tset n))=cutM (Tset n):=by -- tune likely lemma
 apply Mir.twist_comm; ext ⟨i,u⟩ ⟨j,v⟩; rw [cutM,Matrix.mul_diagonal,Matrix.diagonal_mul]; by_cases t:i=j; · subst j; obtain ⟨i,r⟩:= i; by_cases l:r∈plusHalf<;> simp [mem_Tset,l]
 simp [tradew,jump_apply,t]
lemma below_blend (g:Plum.Troupe n)(p:Ket (Single n)): acts (cutM (Tset n)) (acts (star (tradew n g).val) p) = acts (star (tradew n g).val) (acts (cutM (Tset n)) p):=by
 let U:=cutM (Tset n); let T:=tradew n g
 have h:= Fock.swivel T U; rw [show twist T U= _ from blendOne g] at h -- fix arg
 apply (show Injective (acts T.val) from ?_); swap; · intro u v d; nth_rw 1 [← act_unit T u]; rw [d,act_unit]
 rw [show (acts (tradew n g).val) _= (acts U (acts T.val (acts (star (tradew n g).val) p))) from h _,act_starUnit,act_starUnit]
-- ready columns lift
local notation "x★"=> cutM (colorsOne W f)
variable {v:ℝ}{t:Aim n}{b₀:Male}
lemma liftTo {δ:Ket (Single n)}{w:Site n}(h:Column (bay (terr (More n)) o d) j b₀ f W H a c (Baby f w) δ) (γ:Plum.Troupe n):
    withinM (tube (floors o W d) (family f) plusHalf) (acts (cutM (Tset n)) (acts (star (tradew n γ).val) δ)):=by
 rw [below_blend]
 apply Scherzo.still (family f) (floors o W d) γ plusHalf
 refine closedCut_iff.mpr (fun i p=>?_); obtain ⟨⟨i,j⟩,x⟩:=i; rw [cut_apply]; split; rename_i v'
 · have he:j∈plusHalf:=(mem_Tset ..).1 v'; by_contra hz
   have hcol:x=f:=by by_contra! hu; apply hz (closedCut_iff.mp h.color _ (by simp [colorsOne,hu]))
   have hx: node i∈(S' d):= (locate_wall _ ((i,j),x)).1 (of_not_not (fun hp=> hz (closedCut_iff.mp h.supported _ hp)))
   have ht:i∉W:=by intro u; have hp: δ.ofLp ((i,j),x)=(Baby f w).ofLp ((i,j),x):=by rw [←h.anchor]; rw [cut_apply,if_pos (by simp [colorsOne,hcol,u])]; -- tune
                   apply hz; rw [hp]; exact empties_iff.mp (baby_upper f w) _ ((mem_Tset ..).mpr he)
   apply p; simp [tube,flo o W _, (bay_mem _).1 hx,ht,hcol,he]
 exact rfl
end Play
end YM.CF.Signal
