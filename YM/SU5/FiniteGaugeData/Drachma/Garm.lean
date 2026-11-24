import YM.SU5.FiniteGaugeData.Drachma.TauM
import YM.Next.RANK.Axial
import YM.PREC.FrameResponse

set_option autoImplicit false
set_option maxHeartbeats 500000
set_option synthInstance.maxSize 15000
set_option linter.flexible false
noncomputable section
namespace YM.SU5.FiniteGaugeData.Drachma
open Function Finset Matrix Lattice Wilson RG Precision Exterior Tree Laurent Bloch
open SectorNext.Vacuum.FlatTree Next.Rank.Axial
open scoped Topology BigOperators Matrix Classical

abbrev LT (n:Side):=Body 1 n
abbrev AfterT(n:Side):=Forest (whole n)
variable {c f:Side}{r:Ratio c f}
variable {k:Type}[AddCommGroup k]
abbrev stem(F:Forest r):=↥F.trunks
variable (F : Forest r)
abbrev portfolio(n:Side):Edge (Site n) ≃ LT n:= Equiv.prodCongr (Equiv.refl _) axisEquiv
abbrev markZ(n:Side) (x:Edge (Site n)) : LT n := portfolio n x
abbrev tag(F:Forest r)(i:stem F):= markZ f i
abbrev ηT(F:Forest r)(i:F.Free):= markZ f i
lemma mark_ins{i j: Edge (Site f)} (h:markZ f i=markZ f j) : i=j:= (portfolio f).injective h

-- trunk fees. Works even for even lattice size
lemma size_stamp:Fintype.card (stem F)+Fintype.card (Site c)=Fintype.card (Site f):=by
 have he:= count_clear F; have ht:Fintype.card F.Free = Fintype.card (Edge (Site f)) - Fintype.card (stem F) := Fintype.card_subtype_compl _
 have hl: Fintype.card (stem F) ≤ Fintype.card (Edge (Site f)) := Fintype.card_subtype_le _; omega

abbrev η_t (x:LT f→k)(j:stem F):=x (tag F j)
def tickets(F:Forest r): Matrix (stem F) (LT f) ℝ:= (1:sp (LT f)).submatrix (tag F) id
lemma tickets_bill(x:coin (LT f)): tickets F *ᵥ x=η_t F x:=funext fun i=> congr_fun (one_mulVec x) (tag F i)

-- gauge. sign convention d (opposite climb)
def ant (t: Site f → k)(b : LT f):k:= -climb t ((portfolio f).symm b)
omit F in
lemma ant_z (x: Edge (Site f))(t:Site f→k): ant t (markZ f x)= -climb t x:=by unfold ant markZ; rw [Equiv.symm_apply_apply]
lemma ant_d(t:Site f→ℝ): ant t=d 0 f *ᵥ (fun p=> t p.1):=by
 ext i; obtain ⟨x,rfl⟩:= (portfolio f).surjective i
 rw [show ant t _=_ from ant_z x t]; rw [show portfolio f x=(x.1,coord x.2) from rfl, d_sites]; unfold climb; abel
lemma ant_sub(t v:Site f→k): ant (t-v) = ant t-ant v:=by ext i; simp only [ant,climb,Pi.sub_apply]; abel
-- lift trunks to SITE gauges anchored along roots
def ftpl(A:stem F→k) (x:Edge (Site f)):= if h:x∈F.trunks then A ⟨x,h⟩ else 0
def descend(A:stem F→k): Site f→k:= leafWard F (ftpl F A)
lemma descend_anchor(A:stem F→k)(i:Site c): descend F A (r.embed i)=0:=root_clear ..
lemma onTab(A:stem F→k): η_t F (ant (descend F A))=A:=by
 ext i; have he := trunk_clear F (ftpl F A) i i.2; simp only [SectorNext.Vacuum.FlatTree.erase,Pi.add_apply,show leafWard F (ftpl F A)= descend F A from rfl] at he; rw [show ftpl F A i.val=A i from dif_pos i.2] at he -- tune
 exact (ant_z _ _).trans (eq_neg_of_add_eq_zero_left he).symm -- η defeq
lemma climb_anchor(t:Site f→k)(h:η_t F (ant t)=0) (i:Site f):t i=t (r.embed (r.parent i)):=by
 induction i using Forest.hike.induct F with
 | case1 i hi ih =>
    have hp := F.stays i hi; rw [hp] at ih
    let x:Edge (Site f):=(F.up i).used i; let j:stem F:=⟨x,(F.trunk_mem_iff _).mpr ⟨i,hi,rfl⟩⟩; have he:ant t (markZ f x)=0:=congr_fun h j; rw [ant_z, neg_eq_zero] at he; have hl:=sub_eq_zero.mp he -- tune
    refine Eq.trans ?_ ih; unfold x at *; cases h: F.up i with
    | mk a b=>
       rw [h] at hl
       cases b
       · exact hl
       simp only [Step.used,↓reduceIte, neg_add_cancel_right, sub_eq_add_neg] at hl; exact hl.symm
 | case2 i hi => exact congr_arg t (Classical.not_not.mp hi)
lemma clock_eq(t v:Site f→k)(h:η_t F (ant t)=η_t F (ant v))(p:∀ i:Site c,t (r.embed i)=v (r.embed i))(i:Site f): t i=v i:= by
 apply sub_eq_zero.mp; change (t-v) i=0; rw [climb_anchor F (t-v) ?_ i]; exact sub_eq_zero.mpr (p _); rw [ant_sub]; exact sub_eq_zero.mpr h -- tune
lemma ranks_1(A:AfterT f): Fintype.card (stem A)+1=Fintype.card (Site f):=by simpa [site_card] using size_stamp A
lemma all_anchor(A:AfterT f)(t:Site f→k)(h:η_t A (ant t)=0) (i:Site f):t i=t 0:=by
 have he:=climb_anchor A t h i; rw [he,show (whole f).parent i=0 from ?_, show (whole f).embed 0=0 from (whole f).root.map_zero]
 exact @Subsingleton.elim _ (inferInstanceAs (Subsingleton (Axis→ZMod 1))) _ _

variable {P:Type}[Ring P][Module P k]
lemma descend_add(x y:stem F→k): descend F (x+y)=descend F x+descend F y:=by
 have he:ftpl F (x+y)=ftpl F x+ftpl F y:=by ext i; simp only [ftpl,Pi.add_apply]; split <;> simp
 ext i; simp only [descend,leafWard,he,cab_add,Pi.add_apply,neg_add]
lemma descend_smul(x:stem F→k)(a:P): descend F (a•x)=a•descend F x:=by
 have he:ftpl F (a•x)=a•ftpl F x:=by ext i; simp only [ftpl,Pi.smul_apply]; split <;> simp
 ext i; simp only [descend,leafWard,he,cab_scalar,Pi.smul_apply,smul_neg]
lemma ant_linear(x y:Site f→k): ant (x+y)=ant x + ant y:=by ext i; simp only [ant,climb,Pi.add_apply]; abel
lemma ant_scale(x:Site f→k)(a:P): ant (a•x)=a•ant x:=by ext i; simp only [ant,climb,Pi.smul_apply,smul_neg,smul_sub]

def propeller(F:Forest r): (stem F→k)→ₗ[P](Site f→k):={toFun:= descend F,map_smul':=fun a x=>descend_smul F x a,map_add':=descend_add F}
def atlas(n:Side): (Site n→k)→ₗ[P](LT n→k):={toFun:=ant, map_add':=ant_linear,map_smul':=fun a x=>ant_scale x a}

def toRealX {I:Type}(x:I→ℤ):coin I:=fun i=> x i
private lemma cRe(w: Links (Per f) ℤ) (u:Site f)(p:Walk): toRealX (fun _ : Unit =>cab w u p) ()=cab (toRealX w) u p:=by
 induction p generalizing u with
 | nil=> simp [cab,toRealX]
 | cons i p ih => unfold toRealX; rw [cab,cab]; simp only [Int.cast_add]; rw [show (↑(cab w (u+i.vec) p):ℝ)=_ from ih (u+i.vec)]; unfold beam; split <;> (simp; rfl)
lemma descend_real(x:stem F→ℤ): descend F (toRealX x)=toRealX (descend F x):=by
 ext i; have he: ftpl F (toRealX x)=toRealX (ftpl F x):=by ext i; simp only [ftpl,toRealX]; split <;> simp
 unfold descend leafWard; rw [he,←cRe]; unfold toRealX; simp
lemma ant_real(t:Site f→ℤ):ant (toRealX t)=toRealX (ant t):=by ext i; simp [ant, climb,toRealX]
lemma down_card(n:Side): Fintype.card (LT n)=Fintype.card (Site n)*4:=(Fintype.card_congr (portfolio n).symm).trans (by simp [Edge,Axis])
end YM.SU5.FiniteGaugeData.Drachma
