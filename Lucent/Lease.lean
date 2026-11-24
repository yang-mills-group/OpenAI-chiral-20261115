import Lucent.Op
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option linter.unusedSectionVars false
set_option maxHeartbeats 300000
noncomputable section
namespace YM.CF.Py.Rate.LocalLimit.Preparation.Yoke.Lucent
open Function Filter Metric Fock Finset Fir Jill Lat Lattice Laurent Next.Free Bloch Cube Sods Tulip Scroll Spire Pastry RP Branch Wilson Phase SU Rush Mir Reflect Buffered Buffered.Lifted Skye MeasureTheory NormedSpace
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace Topology
attribute [local instance] opCStarAlgebra
open Ballad EmberWind Window Lamour.Bridge Celeste
open WakeInvestment

variable {I : Type}
-- uniform real box price.
lemma glint_c [Fintype I] (L:List (Tint I)): ContDiff ℝ 1 (fun x: Tint I→ℝ=>glint x L):=by
 -- if no Fintype I? norms? add
 induction L with
 | nil=> exact contDiff_const
 | cons i L ih=> simp_rw [glint_cons]; change ContDiff ℝ 1 (fun x=>Complex.ofRealCLM ((x:Tint I→ℝ) i) * glint x L); fun_prop

variable {x y : Tint I→ℝ}{B Z:ℝ}
def Covers (x : Tint I→ℝ)(B:ℝ):Prop:=∀ i, |x i| ≤ B
def Adjoins (x y : Tint I→ℝ)(B:ℝ):Prop:=Covers (x-y) B
variable (p:Covers x B)(h:1≤ B)
lemma glint_le (B:ℝ)(v:0≤B) (x:Tint I→ℝ)(p:Covers x B)(L:List (Tint I)): ‖glint x L‖≤ B^L.length := by
 induction L with
 | nil=> rw [glint_nil,norm_one,List.length_nil,pow_zero]
 | cons i T ih=> rw [glint_cons,norm_mul,Complex.norm_real,Real.norm_eq_abs,List.length_cons,pow_succ']; exact mul_le_mul (p i) ih (norm_nonneg _) v

include p h in
lemma glint_sub (q:Covers y B)(v:Adjoins x y Z)(w:0≤Z)(L:List (Tint I)) : ‖glint x L - glint y L‖≤ L.length*B^L.length*Z := by
 have hb:= zero_le_one.trans h
 induction L with
 | nil=> simp [glint_nil]
 | cons i L ih=>
   rw [glint_cons,glint_cons,show (x i:ℂ)*glint x L - (y i:ℂ)*glint y L= (x i:ℂ)*(glint x L-glint y L)+ ((x i:ℂ)-(y i:ℂ))*glint y L from by ring, List.length_cons,pow_succ]
   apply (norm_add_le ..).trans; rw [norm_mul,norm_mul, ←Complex.ofReal_sub, Complex.norm_real,Complex.norm_real,Real.norm_eq_abs,Real.norm_eq_abs]; refine (add_le_add (mul_le_mul (p i) ih (norm_nonneg _) hb) (mul_le_mul (show |x i-y i|≤ Z from v i) (glint_le _ hb _ q _) (norm_nonneg _) w)).trans ?_
   push_cast; nlinarith only [mul_le_mul_of_nonneg_left h (show 0≤ Z * B^L.length from by positivity)]

/- Explicit diameter, clearance, staffing and tenancy approvals for all slots. -/
variable {n:Side}
open Pannier.Chancel Rous Pressure
open Lamour.Bridge Cliplet
open Corona
def rail (W:I→Staff) (r w:ℕ)(n:Side)(o:Skye.Seat n)(e:ℕ):Prop:=∀ i,(W i).Pays r w ∧ (W i).tenancy n r Staff.clearance e o
variable (W:I→Staff) {r w e d:ℕ}{o:Seat n}
lemma rail_seat (p:rail W r w n o e) (i:I) : (W i).scope n ∈ BlockP e o:=by

 obtain ⟨f,g⟩:=p i; refine g (Corona.halo_mono (show r ≤ r+Staff.clearance+8 from by omega) (Subset.refl _) ((f.withinP (W i) n).2.1))
lemma rail_rent (p:rail W r w n o e) (i:I) : ((W i).skyRent r).image (wrap (More n))⊆ BlockP e o:=by
 obtain ⟨f,g⟩:=p i; rw [← (f.withinP (W i) n).1]; exact (Corona.halo_mono (show r+8 ≤ r+Staff.clearance+8 from by omega) (Subset.refl _)).trans g
variable [Fintype I]
abbrev district (W:I→Staff)(r:ℕ):=univ.biUnion fun i=> (W i).skyRent r
lemma Chartered (f:∀ i,(W i).Pays r w): Charter W (district W r) r w:=fun i=>⟨f i, Finset.subset_biUnion_of_mem (s:=univ) (fun i=>(W i).skyRent r) (mem_univ i)⟩ -- syntax


lemma rail_owner (p:rail W r w n o e) (K:Calibration)(m:Side)(l:n=K.c m)(ρ t:ℝ)(S:Stencil I):
    AtSupport false (BlockP e o) (kite r ρ t W S n):= by
 subst n; refine ((charter_price W S K ρ t (Chartered W fun i=> (p i).1)).support m).mono ?_
 intro y h; obtain ⟨x,v,rfl⟩:= mem_image.mp h; obtain ⟨i,_,k⟩:=mem_biUnion.mp v; exact rail_rent W p i (mem_image_of_mem _ k)

/-- A smaller tariff for ink terms, also used for noble's coefficients. -/
abbrev rooks (W:I→Staff)(n:Side):Finset (Seat n):=univ.image fun i=>(W i).scope n
lemma rooks_card: (rooks W n).card ≤ Fintype.card I:= card_image_le
lemma spind_cost (L:List (Loop I)): Cadre (modesIn _ (rooks W n)) (2*L.length) 1 (spind n W L):= by
 have hv(i:I) (x)(h:x∈dBook n {nodeC (seat W i)}): x∈ rooks W n:=by
   have he:x=(W i).scope n:= by simpa [dBook] using h
   rw [he]; exact mem_image_of_mem _ (mem_univ _)
 let mk (i : I) (s:SpinIdx)(c:SU.Slot)(b:Bool):=
    (Cadre.leaf b _ (SitSpin.basisRent n (seat W i) s c).2 (SitSpin.basisRent ..|>.1.le)).cover (modes_monotone (show (dBook n {nodeC (seat W i)})⊆rooks W n from fun x h=>hv i x h))

 induction L with
 | nil=> exact Cadre.unit
 | cons i L ih=>
   obtain ⟨i,x,y⟩:=i
   unfold spind weave; rw [List.length_cons,mul_add,mul_one,List.map_cons,List.prod_cons]
   rw [add_comm]
   exact (((mk i (upSpin (body W i).1) x false).and_ (mk i (dnSpin (body W i).2) y true)).and_ ih).buy le_rfl (by norm_num)

def dues (S:Stencil I):ℝ:= (S.out.map fun q=> ‖q.k‖).sum
lemma dues_cons (q:Bill I)(L:List (Bill I)): dues ⟨q::L⟩= ‖q.k‖+ dues ⟨L⟩:=rfl

variable {m:ℕ}
lemma dream_cost (B:ℝ)(u:0≤B) (G:I→SU.group.Color)(l:Covers (hues G) B)(S:Stencil I)(h:S.degree m d): Cadre (modesIn _ (rooks W n)) (2*d) (dues S * B^m) (dream n W S G):=by
 cases S with|mk L=>
 induction L with
 | nil=> unfold dream; rw [show dues (⟨[]⟩:Stencil I)=0 from rfl,zero_mul]; exact Cadre.zero ..
 | cons q L ih=>
    obtain ⟨a,b⟩:=h q List.mem_cons_self; specialize ih (fun j h'=>h j (List.mem_cons_of_mem _ h'))
    rw [dues_cons,add_mul]; apply Cadre.add _ ih
    have Y:= ((spind_cost (n:=n) W q.loom).scale (glint (hues G) q.flash)).scale q.k
    rw [show q.loom.length=d from b] at Y
    exact Y.buy le_rfl (mul_le_mul_of_nonneg_left ((mul_one _).le.trans ((show q.flash.length=m from a) ▸ glint_le B u _ l q.flash)) (norm_nonneg _))
