import GaugeFieldConstruction.Helikon
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 6500
set_option maxHeartbeats 320000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.SlabMark
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Heat
open Etch
namespace Weir
structure Raft (K:Calibration)(I:Type*) where
  posC : Cover
  ink : I
  folio : Family K
section sat
variable {K:Calibration}{I:Type*}
def Raft.bow (a:Raft K I)(n:Side): Site (More n):= atDeck n a.posC
variable {σ:Cover}{W:ℤ}{F:I→Family K}{o:I → Cover}{L J: List (Raft K I)}{n:Side}{S:I→Finset Cover}
def Vibro (F:I→Family K)(o:I→ Cover)(σ:Cover)(W:ℤ)(n:Side)(L:List (Raft K I)):Prop:= (∀ a∈L,Sloop K W σ (o a.ink) (F a.ink) a.posC a.folio)∧ (L.map (fun a=>a.bow n)).Nodup
local notation "V"=> Vibro F o σ W n
def Raft.foliation (K:Calibration)(W:ℤ)(σ:Cover)(j:Axis)(b:ℤ)(a:Raft K I):Raft K I:=⟨bent j (2*b) a.posC,a.ink,mirror K j (bank σ W b j) a.folio⟩
local notation "B" j:max b:max=> Raft.foliation K W σ j b
@[simp] lemma Raft.foliate_ink (a:Raft K I)(j:Axis)(b:ℤ):((B j b) a).ink=a.ink:=rfl
lemma raft_ne_iff (a b:Raft K I)(j:Axis)(p:ℤ): (((B j p) a).bow n = ((B j p) b).bow n) ↔ a.bow n=b.bow n:=bank_bent_iff ..
lemma Vibro.haul (u:V L)(j:Axis)(b:ℤ): V (L.map (B j b)) :=by
 constructor
 · intro y t; obtain ⟨x,T,rfl⟩:=List.mem_map.mp t; exact Sloop.rift j b (u.1 _ T)
 change List.Pairwise (·≠·) _; refine List.pairwise_map.mpr (List.pairwise_map.mpr ((List.pairwise_map.mp u.2).imp ?_)); intro a a' h t
 exact h ((raft_ne_iff _ _ j b).mp t)
lemma Vibro.append (u:V L)(t:V J)(p:∀ a∈L,∀ b∈J,a.bow n ≠ b.bow n):V (L++J):=by
 refine ⟨fun x e=>Or.elim (List.mem_append.mp e) (u.1 x) (t.1 x),?_⟩
 apply List.pairwise_map.mpr; exact List.pairwise_append.mpr ⟨List.pairwise_map.mp u.2,List.pairwise_map.mp t.2,p⟩
lemma Vibro.half (u:V L)(p:Raft K I→ Bool): V (L.filter p):=
 ⟨fun a t=> u.1 a (List.mem_filter.mp t).1,List.Nodup.sublist ((List.filter_sublist).map _) u.2⟩

def wharf (L:List (Raft K I)):Family K:=(L.map Raft.folio).prod
def buoy (G:I→ℝ)(L:List (Raft K I)):ℝ:=(L.map (G∘ Raft.ink)).prod
@[simp] lemma wharf_nil : wharf ([]:List (Raft K I))=1:=rfl
@[simp] lemma wharf_append : wharf (L++J) = wharf L * wharf J:=by unfold wharf; rw [List.map_append,List.prod_append]
lemma wharf_haul (j:Axis)(b:ℤ):wharf (L.map (B j b))=mirror K j (bank σ W b j) (wharf L):=by
 induction L with
 | nil=> exact (mirror_unit ..).symm
 | cons a L ih=> change (mirror K j (bank σ W b j) a.folio)*wharf _=mirror K _ _ (a.folio*wharf L); rw[ih,mirror_times]
variable {G:I→ℝ}
@[simp] lemma buoy_nil : buoy G ([]:List (Raft K I))=1:=rfl
lemma buoy_append: buoy G (L++J)=buoy G L*buoy G J:=by unfold buoy; rw[List.map_append,List.prod_append]
lemma buoy_haul (j:Axis)(b:ℤ):buoy G (L.map (B j b))= buoy G L:=by unfold buoy; rw[List.map_map]; rfl
lemma buoy_pos (p:∀ i,0<G i): 0<buoy G L :=by
 induction L with
 | nil=> exact one_pos
 | cons a L ih=> exact mul_pos (p a.ink) ih

lemma tow_test (p:∀ i,InTest K true (S i) false (F i))(h:∀ i,Barn K W σ (o i) (S i))(v:V L):TestFamily K true (wharf L):=by
 induction L with
 | nil=>exact aux_test (S:=∅) InTest.one
 | cons a L ih=>
    obtain ⟨T,hT,_⟩:=(v.1 a (by simp)).granted (p _) (h _)
    have hL:V L:=⟨fun b t=>v.1 b (List.mem_cons_of_mem _ t),List.nodup_cons.mp v.2|>.2⟩
    exact TestFamily.mul (aux_test hT) (ih hL)
lemma tow_paid {A:ℝ}(u:∀ i,pay (F i) A)(v:V L):pay (wharf L) (A^(L.length)):=by
 induction L with
 | nil=> simp only [wharf_nil,List.length_nil,pow_zero]; exact pay_unit
 | cons a L ih=>
    have hT:pay a.folio A:= (v.1 a (by simp)).toll (u _)
    have hL:V L:=⟨fun b t=>v.1 b (List.mem_cons_of_mem _ t),List.nodup_cons.mp v.2|>.2⟩
    rw[List.length_cons,pow_succ']; exact pay_mul hT (ih hL)
private lemma dock_comm {x y:Family K}(p:TestFamily K true x)(t:TestFamily K true y):Commute x y:=by
 obtain ⟨a,h⟩:=p.paid; obtain ⟨b,g⟩:=t.paid
 change x*y=y*x; funext m z; change (x m z)*(y m z)= _*_
 have h₁:=(((h.support m).mono (subset_univ _)).allV z); have h₂:=(((g.support m).mono (subset_univ _)).allV z)
 rw[show x m z*y m z=_ from h₁.sign_com h₂]; simp [Sector.grainB]
lemma wharf_split (p:∀ i,InTest K true (S i) false (F i))(h:∀ i,Barn K W σ (o i) (S i))(v:V L)(k:Raft K I → Bool): wharf L = wharf (L.filter k) * wharf (L.filter (fun x=>!(k x))):=by
 induction L with
 | nil=> simp
 | cons a L ih=>
    obtain ⟨T,hT,_⟩:=(v.1 a (by simp)).granted (p _) (h _)
    have hL:V L:=⟨fun b t=>v.1 b (List.mem_cons_of_mem _ t),List.nodup_cons.mp v.2|>.2⟩
    by_cases d:k a
    · simp only [List.filter_cons,d,Bool.not_true,Bool.false_eq_true,↓reduceIte]; change a.folio * wharf L = (a.folio*_)*_; rw[ih hL]; exact (mul_assoc ..).symm
    simp only [List.filter_cons,d,Bool.not_eq_true',↓reduceIte,Bool.false_eq,Bool.true_eq_false]
    change a.folio * wharf L=_*(a.folio* _); rw [ih hL]; exact (dock_comm (aux_test hT) (tow_test p h (hL.half k))).left_comm ..
lemma buoy_split (k:Raft K I→ Bool):buoy G L = buoy G (L.filter k)*buoy G (L.filter (fun x=>!(k x))):=by
 induction L with
 | nil=> simp
 | cons a L ih=>
    by_cases d:k a
    · simp only [List.filter_cons,d,Bool.not_true,Bool.false_eq_true,↓reduceIte]; change _*buoy G L=(_ * buoy G _)*_; rw [ih,mul_assoc]
    simp only [List.filter_cons,d,Bool.not_eq_true',↓reduceIte,Bool.false_eq,Bool.true_eq_false]
    change _*buoy G L=_*(_*buoy G _); rw [ih]; ring

variable (n)
def upstream (j:Axis)(b:ℤ)(L:List (Raft K I)):= L.filter (fun x=> decide (Creek n j b x.posC))
def downstream (j:Axis)(b:ℤ)(L:List (Raft K I)):=L.filter (fun x=> !(decide (Creek n j b x.posC)))
variable {n}{j:Axis}{b:ℤ}
@[simp] lemma keep_up {a:Raft K I}: a∈upstream n j b L↔a∈L∧Creek n j b a.posC:=by unfold upstream; rw[List.mem_filter,decide_eq_true_eq]
@[simp] lemma keep_down {a:Raft K I}: a∈downstream n j b L↔a∈L∧¬ Creek n j b a.posC:=by unfold downstream; simp
variable (σ W n j b)
def Backrift (L:List (Raft K I)):=backL++(backL.map (B j b))
where backL := downstream n j b L
-- `where` may require args

def Forerift (L:List (Raft K I)):= (upstream n j b L).map (B j b)++ upstream n j b L
variable {σ W n}
lemma Vibro.fore (v:V L): V (Forerift σ W n j b L):=by
 have h:V (upstream n j b L):=v.half _
 apply (h.haul j b).append h; intro x t y g e
 obtain ⟨a,h,rfl⟩:=List.mem_map.mp t
 have z:= (creek_bank j b (show atDeck n (bent j (2*b) a.posC)= atDeck n y.posC from e)).2 (keep_up.mp g).2
 exact ((creek_flip j b).mp z) (keep_up.mp h).2
lemma Vibro.back (v:V L):V (Backrift σ W n j b L):=by
 have h:V (downstream n j b L):=v.half _
 apply h.append (h.haul j b); intro x t y g e
 obtain ⟨a,w,rfl⟩:=List.mem_map.mp g
 have z:= (creek_bank j b (show atDeck n x.posC= atDeck n (bent j (2*b) a.posC) from e)).2 ((creek_flip j b).2 (keep_down.mp w).2)
 exact (keep_down.mp t).2 z

variable {m: Side}{D:ℝ}{X:Mark (K.c m)→ℂ}{L':Loom (K.c m)}
local notation "N"=> K.c m
lemma tow_creek (w:LatticeFare K m n W σ)(p:∀ i,InTest K true (S i) false (F i))(h:∀ i,Barn K W σ (o i) (S i))(v:V L)(u:∀ a∈L,Creek n j b a.posC):∃ T:Finset Cover,InTest K true T false (wharf L) ∧ Satin.region T N⊆ band N j (bank σ W b j) K.ℓ :=by
 induction L with
 | nil=> exact ⟨∅,InTest.one,by simp [Satin.region]⟩
 | cons a L ih=>
    obtain ⟨T,hT,g⟩:=(v.1 a (by simp)).granted (p _) (h _)
    have hL:V L:=⟨fun b t=>v.1 b (List.mem_cons_of_mem _ t),List.nodup_cons.mp v.2|>.2⟩
    obtain ⟨T',e,e'⟩:= ih hL (fun b t=> u b (List.mem_cons_of_mem _ t))
    refine ⟨T∪T',(hT.mono subset_union_left).mul (e.mono subset_union_right),?_⟩
    unfold Satin.region; rw[Finset.image_union,Finset.union_subset_iff]; exact ⟨(u a (by simp)).inside w g,e'⟩
lemma tow_back (w:LatticeFare K m n W σ)(p:∀ i,InTest K true (S i) false (F i))(h:∀ i,Barn K W σ (o i) (S i))(v:V L)(u:∀ a∈L,¬Creek n j b a.posC):∃ T:Finset Cover,InTest K true T false (wharf L) ∧ Satin.region (reflectedBox j (bank σ W b j) T) N⊆ band N j (bank σ W b j) K.ℓ :=by
 induction L with
 | nil=>exact ⟨∅,InTest.one,by simp [reflectedBox,Satin.region]⟩
 | cons a L ih=>
    obtain ⟨T,hT,g⟩:=(v.1 a (by simp)).granted (p _) (h _)
    have hL:V L:=⟨fun b t=>v.1 b (List.mem_cons_of_mem _ t),List.nodup_cons.mp v.2|>.2⟩
    obtain ⟨T',e,e'⟩:= ih hL (fun b t=> u b (List.mem_cons_of_mem _ t))
    refine ⟨T∪T',(hT.mono subset_union_left).mul (e.mono subset_union_right),?_⟩
    unfold reflectedBox Satin.region; rw[Finset.image_union,Finset.image_union,Finset.union_subset_iff]
    exact ⟨((creek_flip j b).2 (u a (by simp))).inside w (g.rift j b),e'⟩
variable (X G)
def MatX (L:List (Raft K I)):= ‖X (wharf L m)‖
def Wplus (L:List (Raft K I)):= MatX X L/buoy G L
variable {X G}
lemma tow_rift (w:LatticeFare K m n W σ)(p:∀ i,InTest K true (S i) false (F i))(h:∀ i,Barn K W σ (o i) (S i))(v:V L)(e:Metered K m L' X D){s:ℤ}(k:bank σ W b j=gaugeShift K.B s)(q:∀ i,0<G i):
 Wplus G X L ^2 ≤ Wplus G X (Backrift σ W n j b L)*Wplus G X (Forerift σ W n j b L):=by
 let A:=upstream n j b L; let U:=downstream n j b L
 have ul:V U:=v.half _; have al:V A:=v.half _
 have z:wharf L=wharf U*wharf A:= (wharf_split p h v (fun a=> decide (Creek n j b a.posC))).trans (dock_comm (tow_test p h al) (tow_test p h ul))
 have x: buoy G L=buoy G A*buoy G U:=buoy_split _
 obtain ⟨T,t,u⟩:=tow_creek j b w p h al (fun a v=> (keep_up.mp v).2)
 obtain ⟨T',t',u'⟩:=tow_back j b w p h ul (fun a v=>(keep_down.mp v).2)
 have y:MatX X L ^2 ≤ MatX X (U++U.map (B j b))*MatX X (A.map (B j b)++A):=by
    unfold MatX; rw[z,wharf_append,wharf_append,wharf_haul,wharf_haul,k]; rw[k] at u u'; exact seam_cut e j s t' t u' u
 change (MatX X L/buoy G L)^2≤ (MatX X _/buoy G (U++U.map _))*(MatX X _/buoy G (A.map _++A))
 rw[div_pow,div_mul_div_comm,buoy_append,buoy_append,buoy_haul,buoy_haul,show _*_=(buoy G L)^2 from (by rw[x]; ring : buoy G U*buoy G U*(buoy G A*buoy G A)=(buoy G L)^2)]
 exact div_le_div_of_nonneg_right y (by positivity)
end sat
end Weir
end YM.CF.Buffered.Afterglow.Tower.SlabMark
