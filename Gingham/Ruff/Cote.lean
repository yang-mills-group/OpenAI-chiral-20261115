import YM.Lattice.Support
set_option autoImplicit false
noncomputable section
namespace YM.CF.Gingham.Ruff
open Function Finset Lattice

/-- [-u,u)^4 -/
def apron (u:Side):Finset Cover:=
 Icc (fun _=> -(u.val:ℤ)) (fun _=> (u.val:ℤ)-1)
def flap (u:Side)(i:Axis):Finset Cover :=
  (apron u).filter (fun x=> x i=0)
lemma apron_spec {u:Side}{x:Cover} :
   x∈apron u ↔ ∀ i,-(u.val:ℤ) ≤ x i∧x i<(u.val:ℤ):=by
  rw [apron, mem_Icc]
  constructor
  · rintro ⟨b,e⟩ i
    have ha: x i ≤ (u.val:ℤ)-1:=e i
    exact ⟨b i, by omega⟩
  intro h
  refine ⟨fun i=>(h i).1,fun i=>?_⟩
  change x i ≤ (u.val:ℤ)-1; have := (h i).2; omega

def hem (i:Axis)(d:ℤ):Cover:=
 d • (step i:Cover)
@[simp]
lemma hem_apply (i j:Axis)(d:ℤ):
 hem i d j= if j=i then d else 0:=by simp [hem,Pi.smul_apply]
lemma hem_add (i:Axis)(d e:ℤ):hem i d+hem i e=hem i (d+e):=(add_smul ..).symm


def hemEnd (u:Side)(k:ℕ):ℤ := k - (u.val:ℤ)
def hemHome (u:Side)(r:ℤ):= (r+ (u.val:ℤ)).toNat

lemma hemWidth (u:Side)(k:ℕ)(h:k<2*u.val):
  -(u.val:ℤ)≤ hemEnd u k ∧ hemEnd u k < u.val ∧ hemHome u (hemEnd u k)=k:=by
  unfold hemEnd hemHome; omega
lemma hemLoc {u:Side}{x:Cover}(i:Axis)(h:x∈apron u):
  let k:=hemHome u (x i)
  k<2*u.val ∧ hemEnd u k=x i ∧ (x- hem i (x i))∈ flap u i:=by
  have e:= apron_spec.mp h
  dsimp only
  have z:=e i
  unfold hemEnd hemHome
  refine ⟨by omega,by omega,mem_filter.mpr ⟨apron_spec.mpr (fun j=>?_), by simp⟩⟩
  by_cases g:j=i
  · subst j; simp
  simpa [g] using e j
variable {M: Type*}[AddCommGroup M]
lemma apronSum (u:Side)(i:Axis)(f:Cover→M):
    ∑ x∈apron u, f x =
     ∑ v∈flap u i, ∑ k∈range (2*u.val), f (v+hem i (hemEnd u k)) :=by
  rw [←sum_product']
  symm
  refine sum_bij (fun p _=> p.1+hem i (hemEnd u p.2)) ?_ ?_ ?_ (fun p h=>rfl)


  · rintro ⟨x,d⟩ h; obtain ⟨a,w⟩:=mem_product.mp h; dsimp at *
    obtain ⟨f,g⟩:=mem_filter.mp a
    apply apron_spec.mpr; intro j
    by_cases e:j=i
    · subst j
      obtain ⟨p,q,_⟩:=hemWidth u _ (mem_range.mp w)
      simpa [g] using And.intro p q
    simpa [e] using apron_spec.mp f j
  · rintro ⟨x,d⟩ f ⟨y,e⟩ g h
    change x+hem i (hemEnd u d)= y+hem i (hemEnd u e) at h
    have k := congr_fun h i
    have s:x i=0:=(mem_filter.mp (mem_product.mp f).1).2
    have t:y i=0:=(mem_filter.mp (mem_product.mp g).1).2
    simp [s,t] at k
    unfold hemEnd at k; have w:d=e:=by omega
    rw [w] at h ⊢;rw [add_right_cancel h]
  intro x b
  obtain ⟨h,w,g⟩:=hemLoc i b
  refine ⟨(_, _),mem_product.mpr ⟨g,mem_range.mpr h⟩,?_⟩
  change x - hem i (x i) + hem i (hemEnd u (hemHome u (x i)))=_
  rw [w]; simp

variable {N:Side}
def pleat (u:Side)(i:Axis):Site N:= wrap N (hem i u.val)
def purl (u:Side)(f:Site N→M)(i:Axis)(t:Site N):M:=
  ∑ v∈flap u i, f (t+wrap N v - step i)
lemma tuck (u:Side)(f: Site N→M)(i:Axis)(y:Site N):
  ∑ x∈apron u, (f (y+wrap N x)-f (y+wrap N x-step i)) =
  purl u f i (y+pleat u i)-purl u f i (y-pleat u i):=by
  rw [apronSum u i,purl,purl,←sum_sub_distrib]; apply sum_congr rfl; intro v _
  let F d:= f (y+wrap N (v+hem i (hemEnd u d))-step i)
  have x1:F (2*u.val)=f (y+pleat u i+wrap N v-step i):=by
    simp only [F,pleat,map_add]
    rw [show hemEnd u (2*u.val)=(u.val:ℤ) from by unfold hemEnd; omega]
    congr 1; abel


  have x0:F 0=f (y-pleat u i+wrap N v-step i):=by
    simp only [F,pleat,map_add]
    rw [show hem i (hemEnd u 0)= -hem i u.val from by simp [hem, hemEnd], map_neg]
    congr 1; abel
  rw [←x1,←x0,←sum_range_sub]
  refine sum_congr rfl (fun d _=>congrArg (·- F d) ?_)
  simp only [F,map_add]
  rw [show hemEnd u (d+1)=hemEnd u d+1 from by unfold hemEnd; omega,←hem_add, show hem i 1 = step i from by simp [hem],map_add,wrap_step]
  congr 1; abel

lemma tucks (u:Side)(f:Axis→Site N→M)(y:Site N):
    ∑ x∈apron u, ∑ i, (f i (y+wrap N x)-f i (y+wrap N x-step i)) =
    ∑ i, (purl u (f i) i (y+pleat u i)-purl u (f i) i (y-pleat u i)):= by
  rw [sum_comm];simp_rw [tuck]

lemma bottled {u:Side}{x:Cover}(v:x∈apron u): x∈Lattice.box u.val:=
  box_test.mpr ⟨fun i=> (apron_spec.mp v i).1,fun i=>(apron_spec.mp v i).2.le⟩

