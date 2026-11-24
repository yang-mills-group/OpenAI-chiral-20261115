import Gingham.Ruff.Muffet
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
open Nacre

def staves (N:Side) (d:Shape) (x: Lattice.Edge (Seat N)):Lattice.Edge (Seat N):=
   (((posDir x.2).rotate d.s).used (d.anon N x.1))
def stavesBit (d:Shape)(x:Lattice.Edge (Seat N))(b:Bool):=
   b^^((Lattice.posDir x.2).rotate d.s).neg
def perchLink (d:Shape)(x:Chin N):Chin N :=
   fun j b=> x (staves N d j) (stavesBit d j b)
lemma perchProfile (d:Shape)(p:Pane N):
   perchLink d (profile p) = profile (Yg d p):=by
  funext ⟨x,i⟩ b
  have h: Yg d p (x,i) = ((Lattice.posDir i).rotate d.s).read p (d.anon N x):= rfl
  change profile p (((Lattice.posDir i).rotate d.s).used (d.anon N x)) (b^^_) = _
  simp only [profile,h]
  obtain ⟨u,g⟩:=((Lattice.posDir i).rotate d.s)
  cases b <;> cases g <;> simp [Step.read, Step.used,brand_inv]


lemma perchG (d:Shape)(x:Chin N)(t:Seat N→E):
   perchLink d (relayg t x) = relayg (t∘d.anon N) (perchLink d x):=by
  funext ⟨y,i⟩ b
  let z:= d.anon N y
  let w:Step:= (Lattice.posDir i).rotate d.s
  have h:d.anon N (y+Lattice.step i)= (z+w.vec):=salt d (Lattice.posDir i) y
  unfold perchLink
  unfold relayg
  simp only [Function.comp_def,h]
  change _=_ -- other occurrence?
  simp only [staves,stavesBit]
  unfold w -- beta? 
  obtain ⟨a,g⟩:=((Lattice.posDir i).rotate d.s)
  cases b <;> cases g <;> simp [Step.vec,Step.used,z,sub_eq_add_neg]

lemma perchNorm (d:Shape)(x y:Chin N):
   ‖perchLink d x-perchLink d y‖ ≤ ‖x-y‖:=
  (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun _=>
     (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun _=>
       (norm_le_pi_norm ((x-y) _) _).trans (norm_le_pi_norm (x-y) _)


lemma staves_inj (d:Shape):Injective (staves N d):=by
  rintro ⟨x,i⟩ ⟨y,j⟩ t
  have e:i=j:=by
    apply d.s.perm.injective
    simpa [staves, Step.used, Step.rotate,posDir, apply_ite Prod.snd] using congrArg Prod.snd t
  subst j; unfold staves Step.used at t;split at t
  · congr 1;apply d.anon_b.1
    exact sub_left_inj.mp (Prod.mk.inj t).1
  congr 1;exact d.anon_b.1 (Prod.mk.inj t).1

abbrev sheet (d:Shape)(S:Seal (Seat N)):=S.image (d.anon N)


open Tenant
lemma staves_leaks (d:Shape)(S:Seal (Seat N)) :
    (leaks S).image (staves N d) ⊆ leaks (sheet d S):=by
  intro q v
  obtain ⟨⟨x,i⟩,w,rfl⟩:= mem_image.mp v
  obtain ⟨r,m⟩:=(mem_filter.mp w).2
  let y:= d.anon N x
  let a:Step:= (posDir i).rotate d.s
  have h:d.anon N (x+Lattice.step i)= y+a.vec:= salt d (posDir i) x
  have p:y∈sheet d S:=mem_image_of_mem _ r
  have e:y+a.vec∈sheet d S:=h ▸ mem_image_of_mem (d.anon N) m
  refine mem_filter.mpr ⟨mem_univ _,?_⟩
  change (a.used y).1∈sheet d S ∧ ((a.used y).1+Lattice.step (a.used y).2)∈sheet d S
  revert e; generalize a=u
  obtain ⟨i,b|b⟩:=u
  all_goals simp [Step.vec, Step.used, p, sub_eq_add_neg]

lemma perchFare (d:Shape)(S:Seal (Seat N))(x y:Chin N):
   fare S (perchLink d x) (perchLink d y) ≤ fare (sheet d S) x y:=by


  unfold fare
  apply le_trans _ (sum_le_sum_of_subset_of_nonneg (staves_leaks d S) (fun _ _ _=>norm_nonneg _))
  rw [sum_image (staves_inj d).injOn]
  exact sum_le_sum fun i _=> (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun _=>
     norm_le_pi_norm (x _-y _) _

variable {e:ℝ}{S: Seal (Seat N)}
abbrev Coif(N: Side)(e:ℝ):=Openc (More N) e
def aviator (d:Shape)(x:Coif N e): Coif N e :=
 ⟨perchLink d x.val,
    let ⟨p,q,t⟩:=x.property
    ⟨Yg d p,keepC _ _ _ _ q,by rw [←perchProfile];exact (perchNorm d _ _).trans_lt t⟩⟩

lemma aviator_cont (d:Shape): Continuous (@aviator N e d):=by
  refine Continuous.subtype_mk (continuous_pi fun j=>continuous_pi fun b=>?_) _
  change Continuous (fun x:Coif N e=> x.val (staves N d j) (stavesBit d j b))
  exact (continuous_apply _).comp ((continuous_apply _).comp continuous_subtype_val)

lemma aviates (d:Shape){f:Coif N e→ℂ}(h: Looks _ f):
    Looks _ (f∘aviator d) :=by
  intro V p γ t
  exact h V p (aviator d∘γ)
    (differentiableOn_pi.mpr fun j=> differentiableOn_pi.mpr fun b=>
      differentiableOn_pi.mp (differentiableOn_pi.mp t _) _)


lemma sheet_grove (d:Shape)(h:Grove (terr (More N)) S): Grove (terr (More N)) (sheet d S):=by
  induction h with
  | single x=>simp only [sheet,image_singleton];exact Grove.single _
  | @join S x y _ hx v ih =>
    simp only [sheet,image_insert]
    apply Grove.join ih (mem_image_of_mem _ hx)
    change separation (affine _ _ _) (affine _ _ _)≤1
    rw [Lattice.affine,Lattice.affine,separation_translate,separation_signed];exact v

abbrev Fob(N:Side)(e:ℝ):=Raw (Coif N e) (Single N)
abbrev Jubilee (e:ℝ)(S:Seal (Seat N)) :=
  Suite (badge _) (bail N e) (bail N e) S
abbrev Tawny (e:ℝ)(S:Seal (Seat N)) :=
  Expo (forum N e) S

variable {w:ℝ}{f:Coif N e→ℂ} {i j:Single N}

lemma migrate (d:Shape)(h:Tawny e S i j w f)
    (u v:Single N)(a:cabin u=d.mills N (cabin i))(b:cabin v=d.mills N (cabin j)):
    Tawny e (sheet d S) u v w (f ∘ aviator d):=by
  refine ⟨h.positive,?_,fun _=>h.bounded _,fun x y=> (h.variation (aviator d x) (aviator d y)).trans ?_,
     h.connected.comp (aviator_cont _)⟩


  · intro g
    obtain ⟨t,h,k⟩:=h.triggered g
    refine ⟨sheet_grove d t,?_,?_⟩
    · change node (cabin u)∈_;rw [a,d.nodex]; exact mem_image_of_mem _ h
    change node (cabin v)∈_;rw [b,d.nodex]; exact mem_image_of_mem _ k
  exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right (perchFare d _ _ _) (abs_nonneg _)) h.positive

