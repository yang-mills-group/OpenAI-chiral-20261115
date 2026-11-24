import YM.SU5.FiniteGaugeData.Tapestry.LiftMark
import Gingham.Ruff.Gobelet
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 500000
set_option maxRecDepth 4000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Gingham.Ruff
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder ENNReal Classical
open Buffered Afterglow Satin Tapestry
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock
attribute [local instance] opCStarAlgebra
open Pastry
variable {I:Type*}[Fintype I][LinearOrder I]
def nub (s:Finset I)(A:FC I):= tier 1 (twist (star (flake sᶜ)) A)

lemma nub_𝒿 (s:Finset I)(X:Op I): nub s (𝒿 (cutM s) X) ≤ 2*parce X:=by
 rw [nub,𝒿, dg,dyad,←dim_cut,map_add]
 refine (tier_plus zero_le_one ..).trans ?_
 rw [twist_scalar,map_one,whiteℂ,white1,mul_one,map_sum,two_mul]
 apply add_le_add
 · refine (PE_trace _).trans ?_; unfold parce; refine sum_le_sum fun i _=> sum_le_sum fun j _=>?_
   rw [cutM,Matrix.diagonal_mul]; split
   · rw [one_mul]
   rw [zero_mul,norm_zero]; exact norm_nonneg _
 apply (tier_sum zero_le_one ..).trans
 unfold parce; refine sum_le_sum fun i _=>?_
 rw [map_sum];apply (tier_sum zero_le_one ..).trans
 refine sum_le_sum fun j _=>?_
 unfold cutM; rw [Matrix.mul_diagonal,Matrix.diagonal_mul]
 by_cases p:i∈s ∧j∉s
 · rw [if_pos p.1,if_pos (mem_compl.mpr p.2), one_mul,mul_one,twist_scalar,whiteℂ,
        map_mul]
   apply mul_le_of_le_one_right (norm_nonneg _)
   have h:∀ k:I,poke {k}=put k:= fun k=>Poly.tag_once (cane I) k
   rw [←show drift sᶜ i=put i from if_neg (fun t=>(mem_compl.mp t) p.1),
       ←show drift sᶜ j=takeF j from if_pos (mem_compl.mpr p.2)]
   rw [flake_flip_p,flake_flip_p,←h,←h]
   simpa only [one_pow,mul_one] using white_mul 1 zero_le_one {i} {j}
 by_cases h:i∈s
 · rw [if_neg (fun k=>p ⟨h,mem_compl.mp k⟩),mul_zero,zero_smul,map_zero,Pastry.chaff]
   exact norm_nonneg _
 rw [if_neg h,zero_mul,zero_mul,zero_smul,map_zero,Pastry.chaff]
 exact norm_nonneg _

variable {N:Side}
lemma nub_nectar(w:Bool)(M:OP N):nub (Tset N) (nectarQ w M) ≤ 2*parce M:=by
 unfold nectarQ;split
 · rw [touchP]
   exact nub_𝒿 (Tset N) _
 rw [nub, twist_scalar,map_one,whiteℂ,white1,mul_one,two_mul]
 exact (PE_trace _).trans (le_add_of_nonneg_right (PE_nonneg _))

variable (K:Calibration)(S:Finset Cover)(m:Side)(p: Hosp S (K.c m))
lemma nub_eyes (M:FC (Single (K.c m))):
   ∑ i:Evens S, ‖eye S K m p i M‖ ≤ nub (Tset (K.c m)) M:=by
 unfold nub tier
 let j(i:Evens S):= i.val.map (occupy S (K.c m) p)
 let f(r):= ‖crumb (twist (star (flake (Tset (K.c m))ᶜ)) M) r‖
 simp_rw [one_pow,one_mul]; change _ ≤∑s, f s
 have hu:Injective j:=fun x y h=>Subtype.ext (map_injective _ h)
 refine le_trans ?_ (sum_le_sum_of_subset_of_nonneg
    (subset_univ (image j univ)) (f:=f) (fun _ _ _=>norm_nonneg _))
 rw [sum_image hu.injOn]
 refine sum_le_sum fun i _ =>?_
 let t:=museum S (K.c m) p i.val
 have h:= t.choose_spec.1
 change ‖crumb _ _/t.choose‖≤_
 rw [norm_div,h,div_one]

/- Stronger all-period from measured crumb bill, antipodal placements included.
Don't compare costs by spread. -/
include p in
lemma clean_spin (z:Swatch S)(M:Mark (K.c m))(C:ℝ)
   (h:appear S K m z=M)
   (w:∀ x, nub (Tset (K.c m)) (M x) ≤ C):
    ∀ m x, ‖render S K z m x‖ ≤ C:=by
 have g(x): ∑ i:Evens S, ‖daub S (z i) x‖ ≤ C:=by
    have he(i:Evens S): daub S (z i) x=eye S K m p i (M (replant S (K.c m) x)):= by
       rw [←h]; exact (eye_readCover ..).symm
    simp_rw [he]; exact (nub_eyes K S m p ..).trans (w _)
 intro b x;rw [render_eq,Finset.sum_apply,Finset.sum_apply];apply (norm_sum_le ..).trans
 exact (sum_le_sum (fun i _=> pitched (K:=K) (z:=x) ..)).trans (g _)

#print axioms clean_spin


/-- At Swatch level, only first pane. -/
def SatinSkin (K:Calibration)(F:Buffered.Family K): Prop :=
 ∀ (r:Side)(x y:Fields (K.c r)),x.1=y.1→F r x=F r y

def pearl(M:Mark N): Prop:=
    ∀ x,∃a:ℂ,M x=a • 1

include p in
lemma sleek {z:Swatch S}
   (t:∀ (x y:Fields (K.c m)),x.1=y.1→appear S K m z x=appear S K m z y):
     SatinSkin K (render S K z):=by
 have d(j:Evens S)(x y:PairsC)(w:x.1=y.1):daub S (z j) x=daub S (z j) y:=
  (eye_readCover S K m p z x j).symm.trans
   ((congrArg (eye S K m p j) (t _ _ (congrArg (graft S _) w))).trans (eye_readCover ..))
 intro r x y w
 rw [appearRender,appearSpool,appearSpool]
 exact sum_congr rfl fun j _=>congrArg (· • spool _ _) (d j _ _ (congrArg (onC _) w))

/- If pure at one roomy period, pure on all, including the landed gauge tests. -/
include p in
lemma silky {z:Swatch S} (t:pearl (appear S K m z)) (r:Side):
    pearl (render S K z r):=by
 have d(j:Evens S)(x:PairsC)(w:j.val≠∅):daub S (z j) x=0:=by
    rw [←eye_readCover S K m p]
    obtain ⟨c,h⟩:= t (replant S (K.c m) x)
    rw [h,map_smul]
    have ne : j.val.map (occupy S (K.c m) p) ≠ ∅ :=by simpa
    change _ • (crumb (twist _ 1) _/_ : ℂ)=_
    rw [map_one, ←show poke ∅=(1:FC (Single (K.c m))) from Poly.tag_void _, Pastry.chip,if_neg ne,zero_div,smul_zero]
 intro x
 let i:Evens S:= ⟨∅,by simp [tagWord];rfl⟩
 rw [appearRender,appearSpool,sum_eq_single i]
 · exact ⟨daub S (z i) (Prod.map (onC (K.c r)) (onC (K.c r)) x), by change _ • spool _ (tagWord S ∅)=_;simp [spool,tagWord]⟩
 · intro j _ h; rw [d j _ (fun e=>h (Subtype.ext e)),zero_smul]
 simp

