import YM.CF.Buffered.Laws
import YM.CF.Buffered.PreSupport

/-! # Preserve support; preserve PRODUCTS in genuine order on separated supports

An unconditional product theorem on arbitrary **same-level** chiral insertions
once loomloc(1) holds, under the stated step size and FiniteGaugeData branch hypotheses.
Forest, tags, V: conditional independences / marginalizations proved at these
actual fields, not assumptions of mark-factorization. Admissible probes do not
include arbitrary tag functions.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 16000
set_option maxHeartbeats 400000
noncomputable section
namespace YM.CF.Buffered.Advance
open Function Fock NormedSpace SU Lat Lattice Cube Finset MeasureTheory Branch Reflect Window Wilson Rush Peaks Scroll
open Phase Skye Pastry Tulip Dial Paige Push.SectorMeasure Scree RG Vault Fir Tree Next.SectorChange Girt Spire Stencil
open Reed (Fine think)
open scoped Topology BigOperators InnerProductSpace ComplexConjugate Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {N P : Side} (G : Ratio N P) (A : RG.StepData (More N) (More P))
variable (j : ℕ) (Q : Op SU.Slot) (M : Male) (ho : Odd G.count.val) (q : Chi) (d β : ℝ) (l : Loom N)
local notation "L" => G.count.val
local notation "pre" => before G j Q M ho q d
def gathered (f : Mark N) (W : Fields P) (V : Fields N) := avgF fun F=> pre f F W V
def drawn (l : Loom N) (U : Orbit N) : Fields N := (U.1,l U)
def assembled (f : Mark N) (W : Fields P) (V : Pane N) := ∫ i, gathered G j Q M ho q d f W (drawn l (V,i)) ∂depot N
-- actual advance to functions of arbitrary link/refined data
local notation "run" => gathered G j Q M ho q d
local notation "asm" => assembled G j Q M ho q d l
def pushMark (f : Mark N) : Mark P := fun W => linkLaw A β (asm f W) W.1
local notation "pushed" => pushMark G A j Q M ho q d β l
section steps
variable {R w : ℕ} (p : LaurentRadius j G.count R) (t : Measurable l) (B : A.patch.Branches A.kernel SU.group)
   (hx : 0<d) (hg : 2*d<firstRadius SU.group)
lemma env_avg {I X : Type*} [NormedRing X] [NormedAlgebra ℝ X] [MeasurableSpace I] [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X] (f : Forest (ratio G)→ I→ X) (h : ∀ i, Envelope (f i)) : Envelope (fun i=> avgF fun y=> f y i) := Env.scale (Envelope.const _) (Env.total _ h)
include p hx hg
variable (f : Mark N) (e : Envelope f)
include e
lemma env_gathered : Envelope (uncurry (run f)) := env_avg G _ (before_env G j Q M ho p q d hx hg f e)
omit p hx hg e
include t
lemma drawn_m : Measurable (drawn l) := measurable_fst.prodMk t
include p hx hg e
lemma env_assembled : Envelope (uncurry (asm f)) := by
  let Y(x :(Fields P × Pane N) × Ids N):= (x.1.1,drawn l (x.1.2,x.2))
  have ht:Measurable Y:= (measurable_fst.comp measurable_fst).prodMk ((drawn_m l t).comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd))
  exact env_marginal (Env.along (g:=Y) (env_gathered G j Q M ho q d p hx hg f e) ht) _
lemma env_fixed (x : Fields P) : Envelope (asm f x) := Env.along (g:=Prod.mk x) (env_assembled G j Q M ho q d l p t hx hg f e) (measurable_const.prodMk measurable_id)
include B
lemma env_pushed : Envelope (pushed f) := by
  let u(x : Fields P × Pane N):=(x.1.1,x.2)
  exact env_marginal (Env.scale (Env.along (g:=u) (kernel_env A β B) ((measurable_fst.comp measurable_fst).prodMk measurable_snd)) (env_assembled G j Q M ho q d l p t hx hg f e)) _
-- useful equivalent uncurried single-city version
lemma outright (x : Fields P) : pushed f x = ∫ y, A.density β x.1 y.1 • run f x (drawn l y) ∂city N := by
  let V(y:Orbit N):=run f x (drawn l y); have hv:Envelope V:= Env.along (g:=fun y=>(x,drawn l y)) (env_gathered G j Q M ho q d p hx hg f e) (measurable_const.prodMk (drawn_m l t)); have he: Integrable (fun y:Orbit N=> A.density β x.1 y.1 • V y) (city N):= Env.integrableX (Env.scale (Env.along (slice_env A β B x.1) measurable_fst) hv) _
  rw [show (∫ y,A.density β x.1 y.1 • run f x (drawn l y) ∂city N)=_ from integral_prod _ he]
  simp_rw [integral_smul]; rfl
omit e B t hx hg
-- Fine for arbitrary Fock b, arbitrary band or box S.
theorem carrier_fine {S : Support (More N)} {b : Bool} (h : AtSupport b S f) (X : Fields P) : Fine (Tset P) (modesIn P (padded G S (clothRadius G.count R))) b (pushed f X) := by
  unfold pushMark linkLaw; apply fine_integral; apply Filter.Eventually.of_forall
  intro V; apply fine_rsmul; unfold assembled; apply fine_integral; apply Filter.Eventually.of_forall
  intro k; refine fine_rsmul _ (Fine.sumF _ _ (fun i _=> subFine G j Q M ho S p _ (h.allV (drawn l (V,k)))))
section locality
variable {S : Support (More N)} {b : Bool} (h : AtSupport b S f)
local notation "D" => halo (nearZero R) S
local notation "DC" => halo w (halo (nearZero R) S)
local notation "P₁" => padded G S (L * beforePad R)
include h
lemma gather_dep (X Y : Fields P) (a : Agrees P₁ X.2 Y.2) (x y : Fields N) (u : Agrees S x.1 y.1) (v : Agrees D x.2 y.2) : run f X x=run f Y y := by
  unfold gathered avgF; apply congrArg; apply sum_congr rfl; intro i _; exact before_local G j Q M ho S p q d h u v a (fun _ _=>rfl)
variable (T : LoomLaw l w)
include T t hx hg
lemma asm_dep (X Y : Fields P) (a : Agrees P₁ X.2 Y.2) (x y : Pane N) (u : Agrees DC x y) : asm f X x=asm f Y y := by
  let K(x' : Pane N) := run f X (x,x')
  have hp : LocalOn D K := fun v r w => gather_dep G j Q M ho q d p _ h X X (fun _ _ _=> rfl) (x,v) (x,r) (fun _ _ _=>rfl) w
  have hV := (env_gathered G j Q M ho q d p hx hg f h.env).meas.comp (show Measurable (fun z:Pane N=>(X,(x,z))) from (measurable_const.prodMk (measurable_const.prodMk measurable_id)))
  have hv : Measurable K := hV
  have he : Agrees S x y := agrees_mono u ((halo_subset (nearZero R) S).trans (halo_subset ..))
  change (∫ i, K (l (x,i)) ∂depot N)=(∫ i, run f Y (y,l (y,i)) ∂depot N); rw [loom_integral T t x y D u K hv hp]
  exact integral_congr_ae (Filter.Eventually.of_forall fun i=> gather_dep G j Q M ho q d p _ h X Y a (x,l (y,i)) (y,l (y,i)) he (fun _ _ _=> rfl))
omit h T t hx hg p
open Push
def gross (R w J : ℕ) := beforePad R + w + 10*(J+3)
lemma within_laws {x : Seat N} (e : x ∈ DC) (k : A.ratio=ratio G) : GridApprox.window (A.ratio.embed x) (GridApprox.reach A.patch) ⊆ (padded G S (L * gross R w A.patch.J) : Set (Seat P)) := by
  obtain ⟨z,hz,v⟩:= halo_spec.mp e; obtain ⟨y,u,hu⟩:= halo_spec.mp hz
  rw [k]; rintro a ⟨r,s,rfl⟩; refine halo_spec.mpr ⟨(ratio G).embed y, mem_image_of_mem _ u,?_⟩
  have ht : separation ((ratio G).embed x) (wrap (More P) r+(ratio G).embed x) ≤ GridApprox.reach A.patch := by rw [separation_comm,separation,add_sub_cancel_right]; exact Work.E01.pdist_wrap_le s
  have he : separation ((ratio G).embed y) ((ratio G).embed x) ≤ G.count.val* (beforePad R+w) := (Next.Free.scaled_root (ratio G) y x).trans (Nat.mul_le_mul_left L ((separation_triangle y z _).trans ((Nat.add_le_add (hu.trans (by unfold nearZero beforePad; omega)) v))))
  apply (separation_triangle _ _ _).trans; apply (Nat.add_le_add he ht).trans_eq
  unfold GridApprox.reach RG.Patch.radius gross; rw [show A.patch.L.val= L from (by change A.ratio.count.val= G.count.val; rw [k]; rfl)]; ring
include t T h hx hg p B
theorem surround (k : A.ratio=ratio G) : AtSupport b (padded G S (L*gross R w A.patch.J)) (pushed f) := by
  have hz : P₁ ⊆ padded G S (L*gross R w A.patch.J) := Corona.halo_mono (Nat.mul_le_mul_left _ (by unfold gross; omega)) (Subset.refl _)
  refine ⟨env_pushed G A j Q M ho q d β l p t B hx hg f h.env,fun x y w1 w2=> ?_, fun X=> fine_enlarge (modes_monotone (le_trans ((halo_subset _ _).trans (before_zone G S R)) hz)) (carrier_fine G A j Q M ho q d β l p f h X)⟩
  have a:= agrees_mono w2 hz
  have he : asm f x=asm f y := funext fun z=> asm_dep G j Q M ho q d l p t hx hg f h T x y a z z (fun _ _ _=> rfl)
  have hk : LocalOn DC (asm f y) := fun u v e=> asm_dep G j Q M ho q d l p t hx hg f h T y y (fun _ _ _=>rfl) u v e
  unfold pushMark; rw [he]; exact link_local A β B DC hk (env_fixed G j Q M ho q d l p t hx hg f h.env _) _ (fun _ v=> within_laws G A v k) _ _ w1
end locality

section product
variable {S U : Support (More N)} {b c : Bool} (g : Mark N) (u : AtSupport b S f) (v : AtSupport c U g)
local notation "D" => halo (nearZero R) S
local notation "E" => halo (nearZero R) U
local notation "dc" => halo w (halo (nearZero R) S)
local notation "ec" => halo w (halo (nearZero R) U)
include p u v
lemma gather_times (J : Disjoint D E) (X : Fields P) (W : Fields N) : run (f*g) X W = run f X W * run g X W := by
  let A' := fun (Y:Mark N) (F : Forest (ratio G))=> pre Y F X W
  have he : A' (f*g) = A' f * A' g := funext fun F=> sub_mul _ _ _ _ _ _ (u.allV W) (v.allV W)
  unfold gathered; change avgF (A' (f*g)) = _; rw [he]; exact forest_product J (fun _ _ e=> before_local G j Q M ho S p q d u (fun _ _ _=>rfl) (fun _ _ _=>rfl) (fun _ _ _=>rfl) e) (fun _ _ e=> before_local G j Q M ho U p q d v (fun _ _ _=>rfl) (fun _ _ _=>rfl) (fun _ _ _=>rfl) e)
variable (T : LoomLaw l w) (K : ∀ x∈S,∀ y∈U,2*(nearZero R+w)<separation x y)
omit p u v
include K
lemma halo_disjoint : Disjoint dc ec := by
  apply Finset.disjoint_left.mpr; rintro x p z; obtain ⟨y,p,h⟩:= halo_spec.mp p; obtain ⟨z,z',a⟩:= halo_spec.mp z; obtain ⟨i,u,v⟩:= halo_spec.mp p; obtain ⟨k,k',t⟩:= halo_spec.mp z'; have hx:= K i u k k'; have hp:=separation_triangle i x k; have he:=separation_triangle i y x; have ht:=separation_triangle k z x; rw [separation_comm k x] at ht; omega
include p u v t hx hg T
lemma asm_times (x : Fields P) (y : Pane N) : asm (f*g) x y = asm f x y * asm g x y := by
  have he : Disjoint D E := Disjoint.mono (halo_subset ..) (halo_subset ..) (halo_disjoint K); unfold assembled; simp_rw [gather_times G j Q M ho q d p _ _ u v he]; let H (f:Mark N) (z : Pane N):= run f x (y,z)
  have ht(f:Mark N)(p1:Envelope f):Envelope (H f) := Env.along (g:=fun z : Pane N=>(x,(y,z))) (env_gathered G j Q M ho q d p hx hg f p1) (by fun_prop)
  apply loom_mult (I:=Finset (Single P)) T t y D E _ (H f) (H g) (ht _ u.env) (ht _ v.env) (fun X Y k=> gather_dep G j Q M ho q d p _ u x x (fun _ _ _=>rfl) _ _ (fun _ _ _=>rfl) k) (fun X Y k=> gather_dep G j Q M ho q d p _ v x x (fun _ _ _=>rfl) _ _ (fun _ _ _=>rfl) k) -- `exact`?
  rintro i u k v; obtain ⟨x,h,hx⟩:= halo_spec.mp u; obtain ⟨y,h',hy⟩:=halo_spec.mp v; have H:= K x h y h'; have hp:= separation_triangle x i y; have ht:=separation_triangle i k y; rw [separation_comm k y] at ht; omega
include B
theorem separated_mult : pushed (f*g)=pushed f * pushed g := by
  funext x; have he : asm (f*g) x= asm f x * asm g x:= funext fun y=> asm_times G j Q M ho q d l p t hx hg f g u v T K x y
  rw [pushMark,he]; exact link_mult A β B x.1 dc ec (halo_disjoint K) _ _ (env_fixed G j Q M ho q d l p t hx hg f u.env x) (env_fixed G j Q M ho q d l p t hx hg g v.env x) (fun X Y k=> asm_dep G j Q M ho q d l p t hx hg _ u T x x (fun _ _ _=>rfl) X Y k) (fun X Y k=> asm_dep G j Q M ho q d l p t hx hg _ v T x x (fun _ _ _=>rfl) X Y k)
end product
end steps
end YM.CF.Buffered.Advance
