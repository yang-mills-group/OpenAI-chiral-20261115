import YM.SU5.FiniteGaugeData.Concord.StageNet
import YM.SU5.FiniteGaugeData.Concord.TransferGauge
/-!
# Singlet algebras on the covers and actual periods

Not the conditional `Singlet` of Buffered (with `K.takes`); here can tell gauge invariance on any
one roomy period, then get EVERY size. Show gauge invariant stencils progress as such, even with
full native `simultaneous`, with the comparison and actual auxiliary draws kept compatible.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 510000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Concord
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker
  Topology ComplexOrder Classical
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent
  Next.Free Bloch Drapes Spire Lifted Skye Precision Tree Push.SectorMeasure Next.SectorChange Fock
open Afterglow Afterglow.Common Afterglow.Sound Afterglow.Satin
attribute [local instance] opCStarAlgebra
open Py Py.Rate LocalLimit Preparation Journey Vale
section localAction
variable {K:Calibration}{m:Side}{S:Finset Cover}

def Gaugeable (f:junior K):= ∀ n:Side,covariant (f.val n)
def singlets (K:Calibration) : Subalgebra ℂ (junior K) where
  carrier := {f| Gaugeable f}
  add_mem' := fun {x y} a b j g v=> by
    change x.val _ _+ y.val _ _=twist _ (x.val _ _+y.val _ _)
    rw [(show Gaugeable x from a) j g v,(show Gaugeable y from b) j g v,map_add]
  mul_mem' := fun {x y} a b j g v=> by
    change x.val _ _* y.val _ _=twist _ (x.val _ _*y.val _ _)
    rw [(show Gaugeable x from a) j g v,(show Gaugeable y from b) j g v,map_mul]
  algebraMap_mem' c:=by
    rw [Algebra.algebraMap_eq_smul_one]; intro j g x
    change c • (1:FC (Single (K.c j)))= twist _ (c • 1); rw [twist_scalar,map_one]

lemma drawing {N:Side}(g:Seat N→SU.E)(x:Fields N) : simultaneous g⁻¹ (simultaneous g x)=x:=by
  have h(y:Pane N) : gauge g⁻¹ (gauge g y)=y:= by funext i; dsimp [Lattice.gauge]; group
  exact Prod.ext (h _) (h _)

def moving {N:Side}(g:Seat N→SU.E)(f:Mark N) : Mark N:= fun x => twist (quantU (tradew N g)) (f (simultaneous g⁻¹ x))

lemma is_fixed {N:Side}(f: Mark N) : covariant f ↔ ∀ g,moving g f=f:=by
  constructor
  · intro p g; funext x
    change twist (quantU (tradew N g)) (f (simultaneous g⁻¹ x))=_
    rw [← p g]; conv_rhs=>skip
    rw [show simultaneous g (simultaneous g⁻¹ x)=x by simpa using (drawing g⁻¹ x)]
  intro p g x; conv_lhs=>rw [← p g]
  change twist (quantU _) (f (simultaneous g⁻¹ (simultaneous g x)))=_; rw [drawing]

variable (g: Cover→SU.E)
local notation "Vip" m:max => Seat (K.c m)

def Matches {N:Side} (g:Cover→SU.E)(S: Finset Cover) (t: Seat N→SU.E) := ∀ i∈S,t (wrap (More N) i)=g i

lemma canMatch {N:Side}(S:Finset Cover)(p: Hosp S N): ∃ t: Seat N→ SU.E, Matches g S t:=by
  let f: ↥S→SU.E:=fun i=>g i.val
  let s: ↥S ↪ Seat N:= ⟨pole S N,fun x y h=> Subtype.ext (p.seat_ x.property y.property h)⟩
  exact ⟨occupyFn s f,fun x h=> congrFun (occupyFn_comp s f) (⟨x,h⟩:↥S)⟩

private lemma cover_frame {N:Side} (t: Seat N→SU.E)(U:Pane N)(h:Matches g S t) :
    Agrees S (onC N (gauge t⁻¹ U)) (gauge g⁻¹ (onC N U)):= by
  rintro ⟨x,i⟩ a b
  rw [onC_spec]; unfold Lattice.gauge; rw [onC_spec]; change (t _ )⁻¹*U _*((t (_+step i))⁻¹)⁻¹=(g x)⁻¹*U _*((g (x+step i))⁻¹)⁻¹; rw [←h x a, ←h (x+step i) b,map_add,wrap_step]

private lemma color_basis (N:Side)(x:Cover)(i:SpinIdx)(b:SU.Slot) (g: Seat N→ SU.E) : acts (tradew N g).val (basisC N x i b) = ∑ v:SU.Slot,
    (matter (g (wrap (More N) (nodeC x)))).val v b • basisC N x i v:=by
  unfold basisC; let y: Site N × SpinIdx := (wrap N x,i); let C:= matter (g (node (wrap N x))); rw [map_smul,←node_of]; simp_rw [show ∀ t:ℂ, ∀ x':Ket (Single N), t • (Lifted.winding N x • x')=Lifted.winding N x • (t • x') from fun t x'=> smul_comm ..] -- tune
  rw [←Finset.smul_sum]; congr 1; apply PiLp.ext; rintro ⟨⟨a,s⟩,t⟩
  simp only [basis_act, WithLp.ofLp_sum,Finset.sum_apply, WithLp.ofLp_smul, Pi.smul_apply,basis_apply]
  by_cases p:a=wrap N x<;> by_cases v:s=i <;> simp [p,v,tradew, jump_apply, Lifted.index]

variable {f:Family K}
lemma turns_cover {b wide:Bool}(p:InTest K wide S b f) : ∃ F: Family K, InTest K wide S b F ∧
    ∀ m (u:Seat (K.c m)→ SU.E), Matches g S u → F m=moving u (f m):=by
  have hf:Continuous (gauge g⁻¹ (R:=ℤ)):=by unfold Lattice.gauge; fun_prop
  induction p using @InTest.rec with
  | @seed t q=>
    let T:= Prod.map (gauge g⁻¹) (gauge g⁻¹); let v:=t ∘ T
    have hv:Coeff wide S v:=by
      refine ⟨fun l=>?_, Env.along q.env (hf.prodMap hf).measurable, fun x y a b=>?_⟩
      · obtain ⟨f,h,rfl⟩:=q.narrow l; exact ⟨_,h.comp hf,rfl⟩
      exact q.locus (T x) (T y) (fun i x y=> by dsimp [T,Lattice.gauge]; rw [a i x y]) (fun i x y=> by dsimp [T,Lattice.gauge]; rw [b i x y])
    refine ⟨scalar K v, .seed hv,fun m k t₀=>?_⟩
    funext x; unfold moving scalar; rw [twist_scalar,map_one]; apply congrArg (fun c:ℂ=> c • (1:FC (Single (K.c m)))); symm; exact q.locus _ _ (cover_frame g k x.1 t₀) (cover_frame g k x.2 t₀)
  | @creator x i b u v=>
    let f:= (matter (g (nodeC x))).val; refine ⟨∑ t:SU.Slot, (f t b) • creation K x i t,InTest.sum _ _ fun i _=> .smul _ (.creator i u v),fun m t p=>?_⟩
    funext y; simp_rw [Finset.sum_apply, Pi.smul_apply]; unfold moving creation; rw [twist_create,color_basis,p _ v, map_sum]; simp_rw [map_smul]; rfl
  | @remover x i b u v=>
    let f:= (matter (g (nodeC x))).val; refine ⟨∑ t:SU.Slot, star (f t b) • removal K x i t,InTest.sum _ _ fun i _=> .smul _ (.remover i u v),fun m t p=>?_⟩
    funext y; simp_rw [Finset.sum_apply, Pi.smul_apply]; unfold moving removal; rw [twist_remove,color_basis,p _ v]; unfold Fock.remove; simp_rw [map_sum,map_smul,star_sum,star_smul]; rfl
  | add _ _ a b=>
    obtain ⟨f,t,v⟩:=a; obtain ⟨g,B,h⟩:=b
    refine ⟨f+g,.add t B,fun m k p=>?_⟩; rw [Pi.add_apply,Pi.add_apply,v m k p,h m k p]; exact funext fun x=> (map_add (twist (quantU (tradew _ k))) _ _).symm
  | mul _ _ a b=>
    obtain ⟨f,t,v⟩:=a; obtain ⟨g,B,h⟩:=b
    refine ⟨f*g,.mul t B,fun m k p=>?_⟩; rw [Pi.mul_apply,Pi.mul_apply,v m k p,h m k p]; exact funext fun x=> (map_mul (twist (quantU (tradew _ k))) _ _).symm
  | smul a _ b=>
    obtain ⟨f,t,v⟩:=b; refine ⟨a • f, .smul a t,fun m u b=>?_⟩; rw [Pi.smul_apply,Pi.smul_apply,v m u b]; exact funext fun x=> (twist_scalar ..).symm
  | zero=> exact ⟨0,.zero,fun m t _=>funext fun x=> (map_zero (twist (quantU (tradew _ t)))).symm⟩
  | one=> exact ⟨1,.one,fun m t _=>funext fun x=> (map_one (twist (quantU (tradew _ t)))).symm⟩

lemma gauge_all {f:junior K}(t:f∈ club K S)(h: Hosp S (K.c m))(v:covariant (f.val m)): f∈ singlets K:=by
  intro n; apply (is_fixed _).2; intro G; let g:=G ∘ wrap (More (K.c n)); obtain ⟨x,p,u⟩:= turns_cover g (show InTest K true S false f.val from t)
  have he:x n=moving G (f.val n):= u n G fun _ _=>rfl
  obtain ⟨t,a⟩:= canMatch g S h
  rw [←he]; exact congrFun (native_ext S K h p (by assumption) ((u m t a).trans ((is_fixed _).1 v t))) n

lemma gauge_closed (K:Calibration)(S:Finset Cover) : IsClosed {v:Palette S | music K S v∈singlets K}:=by
  apply IsSeqClosed.isClosed; intro u x b t m g v
  let G:=native S K m; let V:= simultaneous g v; let W:=quantU (tradew _ g); let Tx (x:Palette S):= twist W (G x v)
  have he(v): Continuous (fun x: Palette S=> G x v):=by
    let A:Palette S→ₗ[ℂ] FC (Single (K.c m)):= (LinearMap.proj v).comp G; exact (A.mkContinuous (count S) (fun x=> native_bound ..)).continuous
  apply tendsto_nhds_unique_of_eventuallyEq (f:=fun i:ℕ=> G (u i) V) (g:=fun i:ℕ=> Tx (u i)) ((he V).continuousAt.tendsto.comp t) (((Fock.breeze W).comp (he v)).continuousAt.tendsto.comp t) -- name
  exact Eventually.of_forall fun i=> (show Gaugeable (music K S (u i)) from b i) m g v
end localAction

variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1 ≤ Λ.x)
variable (S:Finset Cover)(s:ℕ) {i k p u v:ℕ→ℕ}
variable {F:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}{P:Playhouse Λ l}
local notation "K"=> tent Y H
local notation "U"=> swept Λ l
local notation "Ω"=> ConeFilter Y i k
variable (W:Traced Y H i k F E P)

lemma haul_gauge (i k:ℕ)(t:PairIdx Y s i k)(f:Mark (side Y i s)) (a:AtSupport false univ f)(u:covariant f): covariant (haul Y s i k f) :=
  push_gauge (apt (Y.ir i) Λ.block Λ.R.L s) (steps Λ.V (Y.ir i) Λ.block (Y.uv k) s) Λ.K.j (aliasLaw Λ) (((Y.voyage i).X (Y.uv k)).wave s) (((Y.voyage i).X (Y.uv k)).gram (s+1)).J.M Λ.R.odd_side Chi.canonical Λ.J.d (((Y.voyage i).X (Y.uv k)).gram (s+1)).beta ((Y.voyage i).CapeT s) ((fullness Y i k t.1).cap_grant.branch s t.2) (Journey.legal Λ) (can_cane Y s t).1 (can_cane Y s t).2 a u ((Y.voyage i).ownership s).paid ((fullness Y i k t.1).cap_grant.aligned s t.2) -- native implicitly? add typed if issues
lemma Copies.in_frame {N P:Side}(h:N=P)(f:Mark N) : covariant (transport h f) ↔ covariant f:=by subst P; rfl
lemma observe_gauge (i:ℕ)(f:Family (tent Y H)): covariant (observe Y H i s f) ↔ covariant (f (momentm Y i s)):=by rw [observe_formula,Copies.in_frame]
lemma gauge_observed (i:ℕ)(f:junior (tent Y H))(t:f∈singlets K): covariant (observe Y H i s f.val):= (observe_gauge ..).2 ((show Gaugeable f from t) _)
include W
lemma curtain (f:junior (tent Y H))(p:f∈ singlets K) : courseAdvance Y H s W f∈singlets K := by
  letI := ConeFilter.uses (Y:=Y) (i:=i) W.own.pick.grow_k
  obtain ⟨S,t⟩:= supported K f; obtain ⟨x,rfl⟩:= music_rep K S f t
  rw [courseAdvance_on]
  refine (gauge_closed (tent Y H) (U S)).mem_of_tendsto (pair_eval (cone_trace Y H S s W.own P W.receipts) (tendsto_const_nhds (x:=x))) ?_
  filter_upwards [box_visit W.own.pick (S:=S) (s:=s)] with y h; let F:= music K S x
  have he:=haul_gauge Y s (i y.1) (k y.2) h.timely (observe Y H (i y.1) s F.val) ((observe_support Y H _ _ (pigment_test S K x)).mono (subset_univ _)) (gauge_observed Y H s (i y.1) F p)
  rw [←step_on Y H W h x] at he; exact gauge_all (cleft ..) (roomy h.main.bigger) ((observe_gauge Y H (s+1) _ _).1 he)
end YM.CF.Buffered.Concord
#print axioms YM.CF.Buffered.Concord.gauge_all
#print axioms YM.CF.Buffered.Concord.curtain
