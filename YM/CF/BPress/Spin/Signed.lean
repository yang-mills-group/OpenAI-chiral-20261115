import YM.CF.BPress.Spin.Sifting
import YM.ProjectorNext.PROJECTOR_EQUIVARIANCE.Links
/-! Equivariance/transposition for interest costs. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress.Spin
set_option linter.unusedSimpArgs false
open Function Filter NormedSpace Finset Lattice Wilson Fock SU Lat Cube Tenant Branch Tulip Scroll Dial Nacre Laic Thera Pledge Sifting Spire
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators
attribute [local instance] opCStarAlgebra
namespace SpinSign
variable {N:Side}{P:Pledge}{a:ℝ}
open ProjectorNext.Equivariance in
lemma pays (v:Signed)(f g:Bkg (More N))(t: Site (More N))(S:Support (More N)) : invitation S (pull v t f) (pull v t g)=invitation (S.image (affine v t)) f g:=by
 refine Finset.sum_equiv (RG.StepData.sendBonds v t) ?_ (fun x hx=>?_); swap
 · rw [pull_formula,pull_formula]; split <;> simp [bonds]
 intro x; simp only [leaks,mem_filter,mem_univ,true_and]; exact (send_mem ..).symm
variable (v:Signed)
def ξ0 (N:Side):Equiv.Perm (Site (More N)):= v.actEquiv.toEquiv
-- choose map to output so `invα` below
def names (N:Side): Equiv.Perm (Single N):= Equiv.prodCongr (Equiv.prodCongr (Tofu (incX v) N) (Equiv.refl _)) (Equiv.refl _)
lemma home_names (i:Single N): home N (names v N i)= ξ0 v N (home N i) := by
 change node ((incX v).mills N i.1.1)= v.act _; rw [Shape.nodex]; unfold Shape.anon incX affine; simp
lemma fees (S: Support (More N))(f g : Bkg (More N)) : invitation S (Yg (incX v⁻¹) f) (Yg (incX v⁻¹) g)= invitation (S.image (ξ0 v N).symm) f g:= by
 rw [Ywin,Ywin,pays]; have he(x:Site (More N)) : affine v⁻¹ 0 x=(ξ0 v N).symm x:=by rw [affine, add_zero]; rfl
 rw [funext he] -- ?

lemma inverse_g (S:Support (More N))(h:Grove (terr _) S) : Grove (terr _) (S.image (ξ0 v N).symm) := by
 let X:= ξ0 v N; induction h with
 | single => rw [image_singleton]; apply Grove.single
 | @join t x y z p u ih=> rw [image_insert]; apply Grove.join (y:=X.symm y) ih (mem_image_of_mem _ p); change separation ((v⁻¹).act x) ((v⁻¹).act y) ≤ _; rw [separation_signed]; exact u
lemma reindexing {f:Raw (Bkg (More N)) (Single N)}(h:(outlook N).Comes P f) : let W:=names v N; (outlook N).Comes P (fun x=> (f (Yg (incX v⁻¹) x)).submatrix W W) := by
 intro W; let U(x:Bkg (More N)):= Yg (incX v⁻¹) x; obtain ⟨F,C,t,H,q⟩:= h; let X := ξ0 v N
 have he : Continuous U:=by unfold U; simp_rw [Ywin]; exact continuous_pull ..
 have hi (S:Support (More N)) (i : Single N) (f: home N (W i)∈ S): home N i ∈ S.image X.symm:=by rw [← X.symm_apply_apply (home N i)]; rw [show X _= _ from (home_names v i).symm]; exact mem_image_of_mem _ f
 have ht(S: Support (More N)) (i j : Single N): Expo (outlook N).stage (S.image X.symm) i j (C S (W i) (W j)) fun x=> F S (U x) (W i) (W j):=by
    let T:= (t S).expo (W i) (W j)
    exact ⟨T.positive,fun k=> ⟨inverse_g v S (T.triggered k).1,hi S i (T.triggered k).2.1,hi S j (T.triggered k).2.2⟩,fun x=>T.bounded (U x),fun x y=> (T.variation (U x) (U y)).trans_eq (congrArg (C S (W i) (W j) * ·) (fees ..)),T.connected.comp he⟩
 have hm(S:Support (More N)): rent P.rate (S.image X.symm)=rent P.rate S:=by rw [rent,card_image_of_injective _ X.symm.injective]; rfl
 refine funds (J:=Seal (Site (More N))) (fun i j S=> ht S i j) (fun i=>?_) (fun i=>?_) (fun x i j=>?_)
 · simp_rw [hm]; exact (Equiv.sum_comp W (fun j=>saleM P.rate C (W i) j)).le.trans (H.rows (W i))
 · simp_rw [hm]; exact (Equiv.sum_comp W (fun i=>saleM P.rate C i (W _))).le.trans (H.cols (W _)) -- tune
 · change f (U x) (W i) (W j)=_; rw [q,Matrix.sum_apply]

-- unitary relabelling and residual onsite unitary before weave of covariance
lemma attached (f:Equiv.Perm (Site N)) (X: Site N→ UNI (SpinIdx×Slot)): love N (jump f (fun i=>(X i).val)) ∈ unitary (Op (Single N)):=by
 let A:= jump f (fun i=>(X i).val); let h: A∈unitary _:= jump_unitary _ _ fun i=>(X i).property; refine ⟨?_,?_⟩
 · rw [←map_star,←map_mul, h.1,map_one]
 rw [←map_star, ←map_mul,h.2,map_one]
def π0 (N:Side): UNI (Single N):= ⟨love N (jump (Tofu (incX v) N) (fun _=>1)), attached _ fun _=>1⟩
def ω0 (N:Side): UNI (Single N):= ⟨love N (jump (Equiv.refl _) (fun i=>(milU (incX v) (spinX v) inert i).val)), attached _ _⟩ -- tune
lemma bond : prepU (incX v) (spinX v) inert N=ω0 v N*π0 v N:=by
 apply Subtype.ext; change love N (jump (Tofu (incX v) N) (fun i=>(milU (incX v) (spinX v) inert i).val))=love N _*love N _; symm; rw [←map_mul,jump_mul]; simp
lemma π0_eq (i j: Single N): (π0 v N).val i j=if names v N i=j then 1 else 0:=by
 rcases i with ⟨⟨x,i⟩,b⟩; rcases j with ⟨⟨y,j⟩,c⟩; change jump (Tofu (incX v) N) (fun _=>1) (x,i,b) (y,j,c)= if (((Tofu (incX v) N x,i),b):Single N)=((y,j),c) then 1 else 0; simp [jump_apply,and_assoc,Matrix.one_apply]; grind
lemma π0_twist (A: Op (Single N)): twist (π0 v N) A=A.submatrix (names v N) (names v N):=by
 let W:=π0 v N; ext i j; rw [twist_formula, Matrix.mul_apply]; simp only [Matrix.mul_apply,Matrix.star_apply,π0_eq,ite_mul,one_mul,zero_mul,apply_ite,map_one,map_zero,mul_ite,mul_zero,mul_one]; simp
private def Wprice :Pledge:=⟨1,max 1 (quota *(((0:ℕ):ℝ)+1)^4 * Real.exp (1*(quota*(((0:ℕ):ℝ)+1)^4))*1),one_pos,lt_max_of_lt_left one_pos⟩
lemma ω0_price : Form.Comes (outlook N) Wprice (fun _=> (ω0 v N).val):=by
 let b:=(outlook N).stage; refine (row_earn (outlook N).full Form.paid (show 0≤(1:ℝ) by norm_num) (fun i _=> Empty.elim i) continuous_const (show (0:ℝ)≤1 by norm_num) 0 ?_ ?_ ?_).books (le_max_right ..)
 · intro _ i j t; rcases i with ⟨⟨i,q⟩,x⟩; rcases j with ⟨⟨j,w⟩,y⟩; have h:i≠j:= by intro h; subst j; exact ne_of_gt t (separation_self (node i))
   change jump (Equiv.refl (Site N)) (fun i=>(milU (incX v) (spinX v) inert i).val) (i,q,x) (j,w,y)=0; rw [jump_apply]; exact if_neg h
 · exact fun i j x=> (norm_entry ..).trans (CStarRing.norm_of_mem_unitary (ω0 v N).property).le
 · exact fun i j x y=>by rw [sub_self,norm_zero,one_mul]; exact b.pos ..

def foilPrice (P:Pledge) := (Wprice.times P).times Wprice
lemma foil_cost {f:Raw (Bkg (More N)) (Single N)}(p:Form.Comes (outlook N) P f): Form.Comes (outlook N) (foilPrice P) (foil v f):=by
 let A:= names v N; let B := incX v; let W:=ω0 v N; have he x: foil v f x=jazz (detX v) (W.val*(f (Yg (incX v⁻¹) x)).submatrix A A*star W.val):=by
    rw [foil,zone_c,← π0_twist]; change jazz (detX v) (twist (prepU _ _ _ _) _)=_; rw [show spinX (incX v).s=spinX v from rfl,bond,twin, twist_formula] -- tune
 have ht := Costs.mul (Costs.mul (ω0_price (N:=N) v) (reindexing v p)) (Costs.stalk (ω0_price (N:=N) v)); rw [funext he]; unfold jazz; split; exact Costs.neg (Costs.stalk ht); exact ht
lemma one (x: Op (Single N)): foil v (fun _=>0) (1:Bkg (More N))=0:= map_zero _
lemma in_one:Yg (incX v) (1:Bkg (More N))=1:=by rw [Ywin]; ext1 i; change (Step.read _ _ _)=1; simp [Step.read]
end SpinSign
end YM.CF.BPress.Spin
