import YM.CF.Emu.Peon
import YM.CF.Nova.Alum
set_option autoImplicit false
noncomputable section
namespace YM.CF.Emu
open YM.CF.Onyx
open Function Filter Metric Fir Lattice Laurent Next.Free Bloch Finset Lat Ember Jill Kea Flare Rush Tulip Cube Fock SU Dial Thera
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix Matrix.Norms.L2Operator Kronecker
attribute [local instance] opCStarAlgebra
open Sods Pic
variable {N:Side}{j:ℕ}{A B C v r D b c:ℝ}{d:Candle}
lemma frost_k {U V:Bkg N} (e:lawnK U V A)(w:Walk)(o:Site N):Cube.cmp firstF (travel U o w) (travel V o w)≤ w.length*A:=by
 have ht(x y:E): Cube.cmp firstF x⁻¹ y⁻¹=Cube.cmp firstF x y:=by
    rw [cmp_sym]; nth_rw 1 [← cmp_left firstF _ _ y]; rw [mul_inv_cancel,←cmp_right _ _ _ x]; simp only [one_mul,inv_mul_cancel_right]
 induction w generalizing o with
 | nil=> simp [travel,Cube.cmp]
 | cons d w ih=>
   let a:= d.read U o; let b:= d.read V o; let u:=travel U (o+d.vec) w; let v:=travel V (o+d.vec) w
   rw [List.length_cons,Nat.cast_add_one,add_mul,one_mul]; refine (cmp_triangle firstF (a*u) (a*v) (b*v)).trans (add_le_add ?_ ?_); rw [cmp_left]; exact ih _
   rw [cmp_right]; cases d with| mk x y=> cases y; exact e _; unfold a b; simp only [Step.read,Bool.true_eq,ite_true]; rw [ht]; exact e _
-- Pays. path nearF
lemma tide0 (o:Site N)(z:Cover)(a:Wing)(U V:Bkg (More N))(p:E): let u:= stemF o z a U p; let v:= stemF o z a V p; ‖hint o z a U p-hint o z a V p‖≤ Cube.cmp matter (travel U (node o) (leap z a.ord)) (travel V (node o) (leap z a.ord)) :=by
 intro u v
 have ht(A B:E):Cube.cmp matter A⁻¹ B⁻¹=Cube.cmp matter A B:=by unfold Cube.cmp; rw [map_inv,map_inv]; change ‖star ((matter A).val)-star ((matter B).val)‖=_; rw [←star_sub,norm_star]
 let x: Op (Single N):=(cote (matter u)).val; let y:Op (Single N):=(cote (matter v)).val
 let w:= Cube.cmp matter u v
 have he:‖x-y‖≤ w:=by
    change ‖jump (Equiv.refl (Site N×SpinIdx)) (fun _=>_) - jump _ (fun _=>_)‖ ≤_; rw [← jump_sub]; exact jump_bound _ _ (norm_nonneg _) (fun i=>le_rfl) -- tune
 let T:= basisKet (hub a o z)
 unfold hint; rw [←smul_sub,norm_smul, show ‖wind o z‖=1 from fee_norm _,one_mul]; change ‖acts x T-acts y T‖ ≤ _; rw [←act_sub]; have hp :‖T‖=1:=by simp [T,basisKet]; -- tune
 exact (opy ..).trans ((by rw [hp,mul_one]; exact he : ‖x-y‖*‖T‖≤ w).trans_eq (by unfold w u v stemF; rw [cmp_right,ht]))
lemma flo(o:Site N)(U:Bkg (More N))(p:E)(R:ℝ)(w:TagT): ‖(nac o U p R w).2‖=‖gain R‖:=by unfold nac; dsimp only; split_ifs <;> simp only [norm_neg,norm_smul,hail,mul_one]
lemma out_t :∃ C:ℝ,0<C∧∀ {N:Side} {U V:Bkg (More N)} {A:ℝ}, lawnK U V A → 0≤A→ ∀ (o:Site N)(p:E)(R:ℝ)(w:TagT),‖(nac o U p R w).2-(nac o V p R w).2‖ ≤ ‖gain R‖*(A*C*Laurent.size w.1):=by
 obtain ⟨c,g,K⟩:= gulf; refine ⟨8*c,by positivity,fun {N} {U V} {A} h e o p R w=>?_⟩
 rcases w with ⟨x,b⟩; unfold nac; dsimp only; let W:= leap x b.ord; have he := le_trans (tide0 o x b U V p) ((K _ _).trans (mul_le_mul_of_nonneg_left (frost_k h W (node o)) (show 0≤ c by positivity)))
 have hv:c*(W.length*A)≤ A*(8*c)* Laurent.size x:= ((mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (show (W.length:ℝ)≤((8*Laurent.size x:ℕ):ℝ) by exact_mod_cast leap_dim x b.ord) e) (show 0≤c by positivity)).trans_eq (by push_cast; ring))
 split_ifs
 · rw [neg_sub_neg,norm_sub_rev,←smul_sub,norm_smul]; exact mul_le_mul_of_nonneg_left (he.trans hv) (norm_nonneg _)
 rw [←smul_sub,norm_smul]; exact mul_le_mul_of_nonneg_left (he.trans hv) (norm_nonneg _)
section
variable {α n:Type*}[LinearOrder n][Fintype n]
def train(F:α→ Reader0 n)(L:List α):= rollC ton (L.map F)
lemma cash_f (F:α→Reader0 n)(L:List α)(p:∀ i∈ L,‖(F i).2‖≤b)(g:0≤r): Pays r (train F L) ((r*b)^L.length):=by
 induction L with
 | nil=> simpa [train,rollC] using Pays.uno
 | cons i j H=> rw [train, List.map_cons,rollC,List.map_cons,List.prod_cons,List.length_cons,pow_succ']; exact ((Pays.tone (F i) g).weigh (mul_le_mul_of_nonneg_left (p i (by simp)) g) g).mul (H fun l u=>p l (by simp [u]))
lemma cash_t (F G:α→ Reader0 n)(h:∀ x,(F x).1=(G x).1)(L:List α)(p:∀ i∈L,‖(F i).2‖≤ b)(u:∀ i∈L,‖(G i).2‖≤ b)(e:∀ i∈L,‖(F i).2-(G i).2‖≤ b * c)(l:0≤ r): Pays r (train F L-train G L) (L.length*(r*b)^L.length*c):=by
 induction L with
 | nil=> simp only [train,rollC,List.map_nil,List.prod_nil,List.length_nil,Nat.cast_zero,zero_mul,sub_self]; exact Pays.nil
 | cons i j H=>
    let C:=b*c; change Pays r (ton (F i)* train F j- ton (G i) * train G j) _
    have ht: Pays r (ton (F i)-ton (G i)) (r*C):=by
       let z:Reader0 n:= ((F i).1,(F i).2-(G i).2)
       have hx: ton z=ton (F i)- ton (G i):=eq_sub_of_add_eq (by unfold z ton; dsimp only; rw [← h i,← creed_a, sub_add_cancel])
       rw [←hx]; exact (Pays.tone z l).weigh (mul_le_mul_of_nonneg_left (e i (by simp)) l) l
    rw [show ton (F i)* train F j- ton (G i) * train G j=(ton (F i)-ton (G i))*train G j+ton (F i)*(train F j-train G j) by rw [sub_mul,mul_sub]; abel]
    have hp : Pays r (ton (F i)) (r*b):= (Pays.tone _ l).weigh (mul_le_mul_of_nonneg_left (p i (by simp)) l) l
    convert (ht.mul (cash_f _ j (fun i h=>u i (by simp [h])) l)).add (hp.mul (H (fun i h=>p i (by simp [h])) (fun i h=>u i (by simp [h])) (fun i h=>e i (by simp [h])))) using 1; unfold C; rw [List.length_cons,pow_succ]; push_cast; ring
end
end YM.CF.Emu
