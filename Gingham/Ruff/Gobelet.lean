import YM.CF.Buffered.Probes
import YM.CF.Cascade.Velvet
import Gingham.Ruff.Terrace

set_option autoImplicit false
set_option maxHeartbeats 500000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Gingham.Ruff
open Function NormedSpace Finset Fock Scree Pastry
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
open Lattice Wilson Laurent Cube SU Lat Spire Scroll Peaks Drapes Rush Precision Tulip Jet
    Tap Laic Dial Paige Vault Pec Skye Branch
variable {N:Side}

open RG Vow Hake Tenant
set_option linter.unusedSimpArgs false

open Sour Rill
attribute [local instance] Rill.boreKSpace Rill.boreXN Sour.loreM Sour.loreN
open scoped Classical

open Nacre


open Buffered
open Reed (Fine think)
set_option synthInstance.maxSize 16000

def nectarQ (w:Bool)(M:OP N) : FC (Single N):=
 if w then 𝒿 (tickA N) M else (Matrix.trace M) • 1
lemma Nectar_zero (w:Bool): nectarQ (N:=N) w 0=0:=by simp [nectarQ,𝒿_zero]
lemma Nectar_sub (w:Bool)(A M:OP N): nectarQ w (A-M)=nectarQ w A-nectarQ w M:=by
  unfold nectarQ
  split
  · rw [𝒿_sub]
  rw [Matrix.trace_sub,sub_smul]
lemma Nectar_paid(w:Bool)(M:OP N): ‖nectarQ w M‖ ≤ 2*parce M:=by
 unfold nectarQ;split
 · rw [touchP];exact PE_serf _ M
 rw [norm_smul,norm_one,mul_one,two_mul]
 exact (PE_trace _).trans (le_add_of_nonneg_right (PE_nonneg _))

lemma Nectar_tint (w:Bool)(M:OP N)(t:Seat N→SU.E):
    nectarQ w (twist (tradew N t) M)=twist (quantU (tradew N t)) (nectarQ w M):=by
   unfold nectarQ; split
   · rw [←wind_𝒿,Cascade.tick_g]
   rw [twistTr,twist_scalar,map_one]
lemma Nectar_cont (w:Bool): Continuous (nectarQ (N:=N) w):=by
 unfold nectarQ 𝒿
 cases w <;> simp only [Bool.false_eq_true, if_true, if_false] <;> fun_prop

variable {I:Type*}[Fintype I][LinearOrder I]

lemma fine_pt(s t:Finset I){i j:I}(a:i∈t)(b:j∈t)(p:i∈s)(n:j∉s):
 Fine s t false (put i*takeF j):=by
 have h:= (Fine.seed (s:=s) i a)
 have k:=fine_neg (Fine.seed (s:=s) j b)
 rw [show (think s).term j= -takeF j from if_neg n,neg_neg] at k
 rw [show (think s).term i=put i from if_pos p] at h
 exact h.grow k

lemma fine_𝒿 {s t:Finset I}(M:Op I)(h:∀ i j, M i j ≠ 0 → i∈t ∧ j∈ t):
    Fine s t false (𝒿 (cutM s) M):=by
 rw [𝒿,dg,dyad,←dim_cut]
 refine Fine.add (Fine.one.scale _) (Fine.sumF _ _ fun i _=> Fine.sumF _ _ fun j _=>?_ )
 rw [cutM,cutM,Matrix.mul_diagonal,Matrix.diagonal_mul]
 by_cases p:i∈s ∧j∉s ∧ M i j ≠ 0
 · exact (fine_pt s t (h i j p.2.2).1 (h i j p.2.2).2 p.1 p.2.1).scale _
 have e : ((if i ∈ s then 1 else 0) * M i j * (if j∈sᶜ then 1 else 0))=0:=by
    simp only [mem_compl]; grind
 rw [e,zero_smul]
 exact Fine.empty _

variable {y:Site N}{a c e:ℝ}{p:BudgetPoint}
 {M:Orbit N→OP N}

abbrev dustId(N:Side): Ids N:= (badgeX N).choose
abbrev pitchK(x:Fields N):Orbit N:=(x.1,dustId N)
def cupN(w:Bool)(M:Orbit N→OP N):Mark N:= fun x=>nectarQ w (M (pitchK x))
def zone(y:Site N)(p:BudgetPoint):Set (Fields N):=
 {x|pingS p.threshold (hoop y p.B) x.1}
/-- First Pane information, discontinuous only at mask cuts. -/
structure Premier (F:Mark N)(y:Site N)(p:BudgetPoint)(C:ℝ): Prop where
  good : AtSupport false (beagle y p) F
  tint : covariant F
  pos : 0≤C
  fails(x): x∉zone y p→ F x=0
  paid(x): ‖F x‖ ≤ C
  varies(x z): x∈zone y p → z∈zone y p →
     ‖F x - F z‖ ≤ C* fare (belle y p.B) (profile x.1) (profile z.1)

variable (G:Matinee p y e c M)
def costGlass(e c:ℝ):= 2*c*(1+1/e)


include G
lemma wear3(w:Bool): Premier (cupN w M) y p (costGlass e c):=by
 have u:=G.pos
 have z : 0 ≤ c:=(PE_nonneg _).trans (G.pay (1,dustId N)) -- 1 profile?
 have val(x:Fields N): ‖cupN w M x‖≤2*c:=
     (Nectar_paid ..).trans (mul_le_mul_of_nonneg_left (G.pay (pitchK x)) zero_le_two)
 have h0:2*c ≤ costGlass e c:=le_mul_of_one_le_right (by positivity)
     (le_add_of_nonneg_right (by positivity))
 obtain ⟨v,s,l,j,r⟩:=G.fees
 refine ⟨⟨⟨?_,2*c,val⟩,fun x y t _=> congrArg (nectarQ w)
          (G.cyl (pitchK x) (pitchK y) t),?_⟩, ?_, (by unfold costGlass;positivity),
        fun x a=>?_,fun x=>(val x).trans h0, ?_⟩
 · exact (Nectar_cont w).measurable.comp (G.borel.comp (measurable_fst.prodMk measurable_const))
 · intro x; unfold cupN nectarQ; split
   · rw [touchP]
     have t:belle y p.B ⊆ beagle y p:=
      (innerlude y p.B).trans ((halo_subset ..).trans (innerbeagle y p))
     refine fine_𝒿 _ (fun i j' n=>?_ )
     have a:=norm_pos_iff.mpr n
     obtain ⟨b,c⟩:=l i j' (a.trans_le (j _ _ _)).ne'
     exact ⟨(modes_at _ _).mpr (t b), (modes_at _ _).mpr (t c)⟩
   exact Fine.one.scale _

 · intro t x
   let w':=(Lattice.gauge t x.1,threadG t (pitchK x).2)
   have h:M (pitchK (simultaneous t x))= twist (tradew N t) (M (pitchK x)):=
     (G.cyl (pitchK (simultaneous t x)) w' (fun _ _ _=>rfl)).trans (G.tint (pitchK x) t)
   unfold cupN; rw [h,Nectar_tint]
 · unfold cupN; rw [G.fails (pitchK x) a, Nectar_zero]
 intro x z' p₁ p₂
 unfold cupN
 rw [← Nectar_sub]
 let D:= fare (belle y p.B) (profile x.1) (profile z'.1)
 have hp:0≤D:=by unfold D fare; positivity
 have h:parce (M (pitchK x)-M (pitchK z')) ≤ c*(D/e):=by
    apply le_trans _ (mul_le_mul_of_nonneg_right s (by positivity:0≤D/e))
    rw [sum_mul];refine sum_le_sum fun i _=>?_
    rw [sum_mul];exact sum_le_sum fun j _=> r (pitchK x) (pitchK z') p₁ p₂ i j
 apply (Nectar_paid ..).trans
 apply (mul_le_mul_of_nonneg_left h zero_le_two).trans
 change _ ≤ costGlass e c * D
 rw [costGlass,mul_add,mul_one,add_mul]
 apply le_add_of_nonneg_of_le (by positivity)
 apply le_of_eq;ring

#print axioms wear3

