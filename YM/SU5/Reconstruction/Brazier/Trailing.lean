import YM.SU5.Reconstruction.Brazier.Fare
/-! Later insertion exact multipliers on supported polynomial budgets. -/
set_option autoImplicit false
set_option synthInstance.maxSize 31000
set_option maxRecDepth 6200
set_option maxHeartbeats 400000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.FirstWindows.Brazier
open Function Set Filter NormedSpace Lattice Wilson Cube MeasureTheory Reflect Advance
  Scroll Skye Window Journey Satin Tapestry Altitude Exhibition Vacancy Selected SatinVerification Py Py.Rate LocalLimit Preparation SlabMark MeshClock
open scoped Topology BigOperators ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l))
namespace Note
section
variable {J:Type*}[CommRing J][Algebra ℂ J] {n:ℕ}
open PiTensorProduct (tprod)
lemma move_stone {f:ℕ→J}(p:Altitude.Enough n f)(x:J){i:ℕ}(h:n < i): tprod ℂ f * pinhole J i x=tprod ℂ (Function.update f i x):=by
 rw [pinhole_apply, PiTensorProduct.tprod_mul_tprod]; refine congrArg (PiTensorProduct.tprod ℂ) (funext fun j=>?_); by_cases h':j=i
 · rw [h']; change f i*_=_; rw [update_self,update_self,p i h,one_mul]
 change f j*_= _; rw [update_of_ne h',update_of_ne h', mul_one]
lemma move_read {S:ℕ→Type*} [∀ i,CommRing (S i)] [∀ i,Algebra ℂ (S i)] (D':Decking J S)(v:Pad J)
 {x:Altitude.Cloud J}(p:x∈shorter J n){i:ℕ}(h:n < i)(y:J) : D'.crown v i (x*pinhole J i y)=D'.crown v i x* D'.perceive i y:=by
 apply Altitude.boarded (P:={f|Altitude.Enough n f}) (M:=fun x=> D'.crown v i (x*pinhole J i y)=D'.crown v i x*D'.perceive i y) ?_ ?_ ?_ ?_ p
 · intro f (p:Altitude.Enough n f); have hn:= p.taller h.le; have h':Altitude.Enough i (update f i y):= Altitude.Enough.replace i i f y hn le_rfl
   rw [move_stone p y h,Decking.reckon_paid _ _ _ hn,Decking.reckon_paid _ _ _ h']; cases i with
   | zero=> omega
   | succ k=> simp only [Decking.finish]; rw [D'.finish_pass k (k+1) y (by omega),update_self,p (k+1) h,map_one,mul_one]
 · simp
 · intro f g _ _ a b; rw [add_mul,map_add,map_add,add_mul,a,b]
 intro a f _ q; rw [Algebra.smul_mul_assoc,map_smul,map_smul,Algebra.smul_mul_assoc,q]
end
-- pay one suffix.Mark up at later stage
variable (a:Tarmac)(J:Calibration){s:ℕ} (p:a.roof<s) {S:Finset Cover} (y:Dome J) (q:y∈bay J S true)
local notation "Wx"=> update a.book s S
-- cost independent of x and its requested budget
noncomputable def brace (W:BillOfWork)(y:Employee W)(m:ℕ): ℕ→ℝ
 | 0=> 1
 | k+1 => if m ≤ k then brace W y m k * ‖y (k+1)‖ else 1
private theorem braceSource (W:BillOfWork)(y:Employee W)(m:ℕ): brace W y m m=1:= by cases m with| zero=> rfl| succ m=> simp [brace]
lemma brace_nonneg {W:BillOfWork}{y:Employee W}{m k:ℕ} : 0≤brace W y m k:=by
 induction k with
 | zero=> exact zero_le_one
 | succ n ih=> 
   unfold brace; split
   · exact mul_nonneg ih (norm_nonneg _)
   · exact zero_le_one
private lemma nectar_norm_eq {S T: Finset Cover}(h:S=T)(u:Swatch S)(v:Swatch T)(p: badge J S u= badge J T v): ‖u‖=‖v‖:=by
 subst T; rw [badge_inj J _ p] -- syntax
private lemma nectar_ext {S T:BillOfWork}(u:Employee S)(v:Employee T)(m:ℕ)(h:∀ i,i ≤ m→ S i=T i)(p:∀ i,i≤ m→employ J S u i=employ J T v i): nectar m u=nectar m v:= by
 rw [nectar_eq,nectar_eq]; exact Finset.prod_congr rfl fun i v'=> nectar_norm_eq J (h i (Finset.mem_Iic.mp v')) (u i) (v i) (p i (Finset.mem_Iic.mp v'))
include p q
open PiTensorProduct (tprod)
private lemma bigger_proposal {x:Employee a.book} (h:Clocked (K:=J) a.book a.roof x)(v:Employee (update a.book s S))(u:employ J (update a.book s S) v=update (fun _=>1) s y):
 Pocket J (update a.book s S) s (nectar a.roof x*brace (update a.book s S) v a.roof s)
 (motif J a.book x*pinhole (Dome J) s y):=by
 let F:=employ J a.book x; let G:= update F s y; let W:= update a.book s S
 have hG:Altitude.Enough s G:= Altitude.Enough.replace s s F y (Altitude.Enough.taller h p.le) le_rfl
 rw [show motif J a.book x*pinhole _ s y=tprod ℂ G from move_stone h y p]
 have hp(i:ℕ): G i∈bay J (W i) true:=by
    by_cases a:i=s; · simpa [G,W,a] using q
    unfold G W; rw [update_of_ne a,update_of_ne a]; exact locatesBadge ..
 obtain ⟨z,e⟩:= motif_represents J W G hp
 have Hz:= Pocket.stone z (K:=J) (S:=W) (n:=s) (show Clocked (K:=J) W s z from (e.symm ▸ hG : Altitude.Enough s (employ J W z)))
 rw [←e]; suffices nectar a.roof x* brace W v a.roof s=nectar s z by rw [show brace (update a.book s S) v a.roof s=brace W v a.roof s from rfl,this]; exact Hz
 have he(j:ℕ)(b:a.roof ≤ j): nectar j z=nectar a.roof x* brace W v a.roof j:=by
    induction j,b using Nat.le_induction with
    | base=>
      rw [braceSource,mul_one]; apply nectar_ext J
      · intro i h; unfold W; rw [update_of_ne (show i≠s by omega)]
      intro i h; rw [e]; unfold G; exact update_of_ne (show i≠s by omega) _ _
    | succ j b ih=>
      rw [brace,nectar,if_pos b,ih]
      have hz:z (j+1)=v (j+1):= by
        apply badge_inj J; change employ J W z (j+1)=employ J W v (j+1)
        rw [e, u]; unfold G; by_cases a:j+1=s
        · simp [a]
        rw [update_of_ne a,update_of_ne a]; exact h (j+1) (by omega)
      rw [hz,mul_assoc]
 exact (he s p.le).symm
lemma promotion : ∃ r:ℝ,0≤r∧∀ (A':ℝ) (x:Cloud (Dome J)),Pocket J a.book a.roof A' x→ Pocket J (update a.book s S) s (A'*r) (x*pinhole (Dome J) s y):=by
 let W:= update a.book s S
 let G:= update (fun _:ℕ=>(1:Dome J)) s y
 obtain ⟨v,u⟩:= motif_represents J W G (fun i=> by
   by_cases e:i=s; · simpa [G,W,e] using q
   unfold W G; rw [update_of_ne e,update_of_ne e]; exact (bay J (a.book i) true).one_mem)
 let r:= brace W v a.roof s; have he:0≤r:= brace_nonneg
 refine ⟨r,he,fun _ x h=>?_⟩
 induction h with
 | stone x w=> exact bigger_proposal a J p y q w v u
 | no=> rw [zero_mul,zero_mul]; exact .no
 | blend _ _ p q=> rw [add_mul,add_mul]; exact .blend p q
 | shade z _ p=> rw [Algebra.smul_mul_assoc,mul_assoc]; exact .shade z p
 | fully t _ q=> exact .fully (mul_le_mul_of_nonneg_right t he) q
end Note
end YM.CF.Buffered.Afterglow.Tower.FirstWindows.Brazier
