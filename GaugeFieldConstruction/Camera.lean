import GaugeFieldConstruction.ProductData
import GaugeFieldConstruction.Stubs
/-!
# Reproducible camera for product columns. Values are evaluated in `J`,
 whose links to the chart tests are in ProductData.
-/
set_option autoImplicit false
namespace YM.GaugeFieldConstruction.Vouchers.Camera
open Finset Function Cauchy Row Raw Bill
open scoped BigOperators
variable {α β : Type*}


def cart (x : Bill α) (y : Bill β) : Bill (α × β) := prep x fun i => prep y fun j=> flash (i,j)
lemma give (x : Bill α) (y : Bill β) : total (cart x y)=times' (total x) (total y) := by
  refine earn x _ ((times').flip (total y)) fun i=>?_
  exact earn y _ (times' (ket i)) (fun j => by rw [take_one,takes])

def K : Axis → Spin → Spin → Credit :=
  ![![![0,-Credit.ii], ![-Credit.ii,0]],![![0,-1],![1,0]],
    ![![-Credit.ii,0],![0,Credit.ii]],![![1,0],![0,1]]]
lemma kij (i : Axis) (a b : Spin) : (K i a b).money=Hij i a b := by
  fin_cases i <;> fin_cases a <;> fin_cases b <;>
    norm_num [K,Hij]
lemma pay_spin {M : Type*} [AddCommMonoid M] (f : Spin → M) : ([0,1].map f).sum=∑ i:Spin,f i := by
  simp [Fin.sum_univ_succ]
lemma pay_sp {M : Type*} [AddCommMonoid M] (f : S3 → M) : ([0,1,2].map f).sum=∑ i:S3,f i := by
  simp [Fin.sum_univ_succ]

def SFS (b : Bool) (i : Axis) (j : FIndex) : Bill FIndex :=
  if h : i.val<3 then flash (j.1,bump ⟨i.val,h⟩ j.2)
  else spend (-1) (Bill.join [0,1,2] (fun k : S3 => Bill.join [0,1] fun a : Spin =>
    flash (a,bump k j.2) (if b then K k.castSucc j.1 a else K k.castSucc a j.1)))
lemma sfs (b : Bool) (i : Axis) (j : FIndex) : total (SFS b i j)=Cder b i (ket j) := by
  refine Fin.lastCases (i:=i) ?_ fun i=>?_
  · rw [SFS,dif_neg (by decide),cost,take_join,pay_sp]
    change _=Cder b τ (ket j)
    simp only [comp_apply,take_join,pay_spin,take_flash,Clast,Ctime,on_ket,
      Credit.opposite,Credit.one_c,neg_smul,one_smul,C,coeffCR]
    cases b <;> simp only [Bool.false_eq_true,↓reduceIte,kij]
  rw [SFS,dif_pos (show i.castSucc.val<3 from i.isLt),take_flash,Cspace,Cshift,on_ket]; simp only [Credit.one_c,one_smul]; rfl

def SPH (ex : Bool) (k : Axis) (i : f) : Bill f :=
  let X:=cart (SFS false k i.1) (flash i.2)
  let Y:=cart (flash i.1) (SFS true k i.2)
  (if ex then spend (-1) X else X) ++ Y
lemma sph_turn (ex : Bool) (k : Axis) (i : f) :
    total (SPH ex k i)=(if ex then L k else P_f k) (ket i) := by
  rw [SPH]
  cases ex
  · rw [total_append]; simp only [Bool.false_eq_true,↓reduceIte,P_f]; simp only [give,sfs,take_one]
    rw [← takes i.1 i.2,split_legs]
  rw [total_append]; simp only [↓reduceIte,L]; rw [cost]
  simp only [give,sfs,take_one]; rw [← takes i.1 i.2,split_legs]; simp

def dp (ex : Bool) (k : Axis) (x : Bill f) := prep x (SPH ex k)
lemma look (ex : Bool) (k : Axis) (x : Bill f) : total (dp ex k x)=(if ex then L k else P_f k) (total x) := earn x _ _ (sph_turn ex k)

def blue (i : Axis) : Bill f := Bill.join [0,1] fun a : Spin => Bill.join [0,1] fun b : Spin =>
  flash (((a,0),(b,0)):f) (K i a b)
lemma screenB (i : Axis) : total (blue i)=B i := by
  rw [blue,take_join,pay_spin]
  simp only [Function.comp_apply,pay_spin,take_join,take_flash,kij,B,C,takes]

def f4Cost (a : F4) := a.2.elim (fun k=>dp true k (blue a.1)) (fun k=>dp false k (blue a.1))
lemma face4 (a : F4) : total (f4Cost a)=evalTf a := by
  rcases a with ⟨i,j|j⟩ <;> simp only [evalTf,f4Cost,Sum.elim_inl,Sum.elim_inr,look,screenB,
    ↓reduceIte,Bool.false_eq_true]

def f5Cost (a : F5) := a.2.elim
  (fun t=>dp true t.val.1 (dp true t.val.2 (blue a.1))) <| fun s=>
    s.elim (fun t=>dp false t.val.1 (dp false t.val.2 (blue a.1)))
           (fun t=>dp false t.1 (dp true t.2 (blue a.1)))
lemma face5 (a : F5) : total (f5Cost a)=evalF a := by
  rcases a with ⟨i,j|t|⟨x,y⟩⟩ <;> simp [f5Cost,evalF,look,screenB]

def bar (m : Bool) (a : S3) (z : MI) : Bill GIndex :=
  if h : a≠2 ∨ z.2.2=0 then flash (m,⟨(a,z),fun u=> h.resolve_left (by simp_all)⟩) else
    let w := strip z
    flash (m,⟨(0,bump 0 w),fun h=>(show False from (by decide : (0:S3)≠2) h).elim⟩) (-1) ++
    flash (m,⟨(1,bump 1 w),fun h=>(show False from (by decide : (1:S3)≠2) h).elim⟩) (-1)
lemma see (m : Bool) (a : S3) (z : MI) : total (bar m a z)=G m a z := by
  unfold bar G; split_ifs
  · rw [take_one]
  · grind
  · grind
  simp only [total_append,take_flash,Credit.opposite,Credit.one_c,neg_smul,one_smul]; abel

def GT (k : Axis) (i : GIndex) : Bill GIndex :=
  let m := i.1; let a := i.2.val.1; let z := i.2.val.2
  if h : k.val<3 then bar m a (bump ⟨k.val,h⟩ z) else
    bar (!m) (ccw a) (bump (cw a) z) ++ spend (-1) (bar (!m) (cw a) (bump (ccw a) z))
lemma vise (k : Axis) (i : GIndex) : total (GT k i)=Gder k (ket i) := by
  refine Fin.lastCases (i:=k) ?_ fun j => ?_
  · unfold GT; dsimp only; rw [dif_neg (by decide), total_append,cost,see,see,show Fin.last 3=τ from rfl,
      Glast,Gtime,on_ket]; simp [sub_eq_add_neg]
  unfold GT; dsimp only; rw [dif_pos (show (Fin.castSucc j).val<3 from j.isLt),see,Gspace,Gshift,on_ket]; rfl

def DG (k : Axis) (x : Bill GIndex) := prep x (GT k)
def pixel (w : Wed) : Bill GIndex :=
  let i:=w.toBlade.val.1; let j:=w.toBlade.val.2
  if hi:i.val<3 then
    let a : S3 := ⟨i.val,hi⟩
    if hj:j.val<3 then
      let b : S3 := ⟨j.val,hj⟩
      if b=cw a then bar true (ccw a) 0 else spend (-1) (bar true (ccw b) 0)
    else spend (-1) (bar false a 0)
  else []
lemma pixel_cost (w : Wed) : total (pixel w)=arc w := by
  unfold pixel arc; generalize H:w.toBlade=T
  obtain ⟨⟨i,j⟩,hp⟩:=T; change i<j at hp; dsimp only
  obtain ⟨a,rfl⟩ : ∃ a : S3,i=a.castSucc := ⟨⟨i.val,Nat.lt_of_lt_of_le (show i.val<j.val from hp)
    (Nat.le_of_lt_succ j.isLt)⟩, Fin.ext rfl⟩
  rw [dif_pos (show (Fin.castSucc a).val<3 from a.isLt)]
  by_cases h : j=Fin.last 3
  · subst j; rw [dif_neg (by decide),cost,see]
    simp only [F,Fin.lastCases_castSucc,Fin.lastCases_last,Credit.opposite,Credit.one_c,neg_smul,one_smul]; rfl
  obtain ⟨b,rfl⟩ := Fin.eq_castSucc_of_ne_last h; rw [dif_pos (show (Fin.castSucc b).val<3 from b.isLt)]
  simp only [F,Fin.lastCases_castSucc, if_neg (show a≠b from fun h=>hp.ne (by rw [h]))]
  split_ifs
  · rw [see]; rfl
  all_goals first | grind | (rw [cost,see]; simp)

def twice (x y : Bill GIndex) : Bill g := cart x y ++ cart y x
def g4Cost (x : G4) := twice (pixel x.val.1) (pixel x.val.2)
lemma polar4 (x : G4) : total (g4Cost x)=evalTg x := by rw [g4Cost,twice,total_append,give,give,pixel_cost,pixel_cost]; rfl

def g5Cost (x : G5) := twice (pixel x.1) (DG x.2.2 (pixel x.2.1))
lemma polar5 (x : G5) : total (g5Cost x)=evalG x := by
  rw [g5Cost,twice,total_append,give,give,DG,earn (z:=Gder _) _ _ (vise _),pixel_cost,pixel_cost]; rfl

def xCost (x : X5) := cart (blue x.1) (pixel x.2)
lemma mixed (x : X5) : total (xCost x)=evalX x := by rw [xCost,give,screenB,pixel_cost]; rfl

def linePair (d : α→ Bill α) (e : β→ Bill β) (i : α×β) := cart (d i.1) (flash i.2) ++ cart (flash i.1) (e i.2)
lemma line_paid (d : α → Bill α) (e : β → Bill β) (D : Module.End ℂ (J α)) (E : Module.End ℂ (J β))
    (h : ∀ i,total (d i)=D (ket i)) (p : ∀ i,total (e i)=E (ket i)) (s : Bill (α×β)) :
    total (prep s (linePair d e))=splitD D E (total s) := earn _ _ _ fun i=>by
      rw [linePair,total_append,give,give,take_one,take_one,h,p,← takes i.1 i.2,split_legs]

def dg (k : Axis) (x : Bill g) := prep x (linePair (GT k) (GT k))
def dx (k : Axis) (x : Bill Row.x) := prep x (linePair (SPH false k) (GT k))
lemma dg_c (k : Axis) (x : Bill g) : total (dg k x)=P_g k (total x) := line_paid _ _ _ _ (vise k) (vise k) _
lemma dp_c (k : Axis) (x : Bill f) : total (dp false k x)=P_f k (total x) := look false k x
lemma dx_c (k : Axis) (x : Bill Row.x) : total (dx k x)=P_x k (total x) := line_paid _ _ _ _ (sph_turn false k) (vise k) _
end YM.GaugeFieldConstruction.Vouchers.Camera
