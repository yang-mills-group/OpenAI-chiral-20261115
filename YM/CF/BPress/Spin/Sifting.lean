import YM.CF.BPress.Spin.Docket
import YM.CF.BPress.Wealth.Groves
import YM.CF.BPress.Spin.Rows
import YM.CF.Laic.Inch
/-! Cavil entry cost. All are columns on actual native paths, no smearing curvature legs to distant loops. Combine spin rows into complete pledges for unreflected before buying Signed. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
namespace YM.CF.BPress.Spin
open Function Finset Filter NormedSpace Fock Lattice Wilson SU Lat Cube Tenant Branch Tulip Scroll Dial Nacre Laic Font Push.AbsoluteSums.Paths
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators
attribute [local instance] opCStarAlgebra
variable {N:Side} {m:ℕ} (i j: Single N) (t: Trip m N)
namespace Sifting
private lemma last (u:Walk)(x:Site N):stop x u∈native x u:=by induction u generalizing x with|nil=> simp [native,stop,visits] |cons i u ih=>unfold native; rw [visits,List.toFinset_cons]; exact mem_insert_of_mem (ih (x+i.vec))
def walkHere:= native (home N i) (shiftH (home N i) (home N j))
def sift:= walkHere i j ∪ univ.biUnion (fun a:Fin m=> native (home N i) (boot (home N i) (t a)))
lemma sift_spec : Grove (terr _) (sift i j t) ∧ home N i∈ sift i j t ∧ home N j∈sift i j t ∧ (sift i j t).card ≤ (8 * notx m i j t + 1+9*m:ℝ):=by
 let l:=home N i; let r:=home N j; let A:=separation l r; let f(k:Fin m):= dial l (t k)
 let S:=walkHere i j; let F(k:Fin m):= native l (boot l (t k)); have hp:l∈S:= Wealth.walks_first ..
 have h:∀ k,Grove (terr _) (F k):=fun i=> Wealth.walks_g ..
 obtain ⟨H,g⟩:= Grid.many (terr _) S (show Grove (terr _) _ from Wealth.walks_g ..) univ F (fun i _=>h i) (fun i _=>⟨l,hp,Wealth.walks_first ..⟩)
 refine ⟨H,mem_union_left _ hp,mem_union_left _ (show r∈ native l (shiftH l r) by simpa only [stopH] using last (shiftH l r) l),?_⟩
 have he (k:Fin m):(F k).card≤8*(f k+1)+1:= (Wealth.walks_n ..).trans (Nat.add_le_add_right (leanB l (t k)) _)
 have ht : (sift i j t).card ≤ 8*(A+∑ k:Fin m,f k)+1+9*m:=by
   refine le_trans g ((add_le_add ((Wealth.walks_n l (shiftH l r)).trans (Nat.add_le_add_right (short l r) _)) (sum_le_sum (fun i _=> he i))).trans ?_)
   simp_rw [mul_add,sum_add_distrib,sum_const,nsmul_eq_mul,← mul_sum,card_univ,Fintype.card_fin]; change (4*A+1)+ _≤ _; simp only [Nat.cast_id]; omega -- tune ty
 have hx : notx m i j t=↑(A+∑ k:Fin m,f k):= by unfold notx gear; push_cast; rfl
 rw [hx]; exact_mod_cast ht
lemma sift_walk (x y : Slot):sift (i.1,x) (j.1,y) t=sift i j t:=rfl

lemma walk_comp {S:Support (More N)} (u v : Bkg (More N))(p:walkHere i j⊆ S) : ‖walkB i.1 j.1 u-walkB i.1 j.1 v‖≤ sphereRate * (4*gear i j) * invitation S u v:=by
 have ht:=invitation.follows (U:=u) (V:=v) p; let x:=invitation S u v; exact (sphereRate_cost.bot ..).trans ((mul_le_mul_of_nonneg_left ((chord.path u v (shiftH (home N i) (home N j)) (home N i) x ht).trans (mul_le_mul_of_nonneg_right (by unfold gear; exact_mod_cast (short (home N i) (home N j))) invitation.positive)) sphereRate_cost.positive.le).trans_eq ((mul_assoc ..).symm))
lemma sifter {S:Support (More N)} (u v:Bkg (More N))(k : Wind (More N))(p:native (home N i) (boot (home N i) k)⊆ S) : ‖silt (home N i) k u-silt (home N i) k v‖ ≤ 8*((dial (home N i) k:ℝ)+1)* invitation S u v:=by
 exact (curv_diff ..).trans ((chord.path u v _ _ _ (invitation.follows p)).trans (mul_le_mul_of_nonneg_right (by exact_mod_cast leanB (home N i) k) invitation.positive)) -- infer
lemma walk_cont : Continuous (walkB i.1 j.1):= matter_cont.comp (continuous_travel _ _)

-- group raw entries. factor using no decay loss except converting exponent from support size.
def st (U:Bkg (More N)):Fin m→ group.Color:= fun k=> silt (home N i) (t k) U
lemma st_comp (u v:Bkg (More N)) : ‖st i t u-st i t v‖≤8*(1+notx m i j t)*invitation (sift i j t) u v:=by
 let x:=invitation (sift i j t) u v; have hx : 0≤x:=invitation.positive; have he:=notx_zero m i j t; let z:=notx m i j t; apply (pi_norm_le_iff_of_nonneg (show 0≤8*(1+z)*x from mul_nonneg (by unfold z; positivity) hx)).2; intro k
 refine (sifter i u v (t k) (subset_trans (subset_biUnion_of_mem (fun a:Fin m=> native (home N i) (boot (home N i) (t a))) (mem_univ k)) subset_union_right)).trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ (by norm_num)) hx) -- subset tune
 let f(h:Fin m):ℝ:= dial (home N i) (t h); rw [add_comm 1]; unfold z notx; apply add_le_add_left -- orientation?
 exact (single_le_sum (f:=f) (fun i' _=> Nat.cast_nonneg _) (mem_univ k)).trans (le_add_of_nonneg_left (by unfold gear; positivity))
lemma st_cap (u:Bkg (More N)): ‖st i t u‖≤ 2:=(pi_norm_le_iff_of_nonneg (by norm_num)).2 fun k=> (group.curvature_norm _).trans (group.chord_le_two _)
lemma st_cont:Continuous (st i t):= continuous_pi fun k=> group.continuous_curvature.comp (continuous_travel _ _)
variable (R:Toy m N)
def resolution (m:ℕ):ℝ:= 2^m*(1+ 4*sphereRate)+ m*(2^(m-1))*8
lemma res_pos:0<resolution m:=by unfold resolution; have he:=sphereRate_cost.positive; positivity
def mine (x:Slot):=resolution m*(1+notx m i j t)*‖R i (j.1,x) t‖
def minter (x:Slot)(u:Bkg (More N)):=R i (j.1,x) t (st i t u)*walkB i.1 j.1 u x j.2
def outlook (N:Side):=Form.init (N:=N) (D:=Bkg (More N)) id
lemma minit (x:Slot): Expo (outlook N).stage (sift i j t) i j (mine i j t R x) (minter i j t R x):=by
 let F:=R i (j.1,x) t; let S:=sift i j t; let w(u:Bkg (More N)):= walkB i.1 j.1 u x j.2; let a:=gear i j; let z:= notx m i j t; have hx:0≤a:= Nat.cast_nonneg _
 have ht:a≤z:=le_add_of_nonneg_right (sum_nonneg (fun _ _=>Nat.cast_nonneg _)); let d:=‖F‖; let M:=sphereRate; have hM:0<M:= sphereRate_cost.positive; have hb(u): ‖w u‖≤1:= (norm_entry (walkB i.1 j.1 u) x j.2).trans (CStarRing.norm_of_mem_unitary (matter (travel u (home N i) (shiftH (home N i) (home N j)))).property).le
 obtain ⟨p,q,e,g⟩:= sift_spec i j t; have hn :0 ≤ resolution m*(1+z):=mul_nonneg res_pos.le (by linarith); have hy v: ‖F (st i t v)‖ ≤ d*2^m:= F.le_opNorm_mul_pow_of_le (st_cap i t v)
 let f: Bkg (More N) → ℂ:= minter i j t R x; refine ⟨mul_nonneg hn (norm_nonneg _),fun _=>⟨p,q,e⟩,fun u=>?_,fun u v=>?_, (F.cont.comp (st_cont ..)).mul ((walk_cont i j).matrix_elem ..)⟩
 · unfold minter; rw [norm_mul]; apply ((mul_le_of_le_one_right (norm_nonneg _) (hb u)).trans (hy u)).trans; change d*2^m ≤ _ * d; rw [mul_comm]; apply mul_le_mul_of_nonneg_right _ (norm_nonneg _); refine le_trans ?_ (le_mul_of_one_le_right res_pos.le (le_add_of_nonneg_right (notx_zero ..))); unfold resolution; exact (le_mul_of_one_le_right (by positivity) (le_add_of_nonneg_right (mul_nonneg (by norm_num) sphereRate_cost.positive.le))).trans (le_add_of_nonneg_right (by positivity))
 let b:=st i t; let X:=invitation S u v; have hX:0≤X:= invitation.positive; unfold minter; change ‖F (b u)*w u-F (b v)*w v‖≤ _; rw [show F (b u)*w u-F (b v)*w v=(F (b u)-F (b v))*w v+F (b u)*(w u-w v) by ring]; apply (norm_add_le ..).trans
 have hl : ‖F (b u)-F (b v)‖≤ d*(m:ℝ)*2^(m-1)*(8*(1+z)*X):=by
    have he := F.norm_image_sub_le (b u) (b v); rw [Fintype.card_fin] at he; apply he.trans; exact mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (le_max_of_le_left (norm_nonneg _)) (max_le (st_cap ..) (st_cap ..)) _) (by positivity)) (st_comp i j t u v) (norm_nonneg _) (by unfold d; positivity)
 rw [norm_mul,norm_mul]; apply (add_le_add ((mul_le_of_le_one_right (norm_nonneg _) (hb v)).trans hl) (mul_le_mul (hy u) ((norm_entry (walkB i.1 j.1 u-walkB i.1 j.1 v) x j.2).trans (walk_comp i j u v (S:=S) subset_union_left)) (norm_nonneg _) (by unfold d; positivity))).trans
 -- polynomial prices
 change d*↑m*2^(m-1)*(8*(1+z)*X)+d*2^m*(M*(4*a)*X)≤ (_*(1+z)*d)*X
 have h₁ : M*(4*a)≤ (1+4*M)*(1+z):= by nlinarith only [ht,hM,hx]
 exact (add_le_add_right (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h₁ hX) (by unfold d; positivity : 0≤d *2^m)) _).trans_eq (by unfold resolution M; ring)

lemma row_paid {P:Pledge} (h:CardK N m R P.price P.rate) (o:Single N) : (∑ j:Single N, ∑ k:Trip m N×Slot, rent (P.rate/8) (sift o j k.1)* mine o j k.1 R k.2) ≤ (45*Real.exp ((1+9*(m:ℝ))*P.rate/8)*resolution m)* P.price:=by
 let a:=P.rate/8; have he:0<a:=div_pos P.pos (by norm_num); let d:=Real.exp ((1+9*(m:ℝ))*P.rate/8); let X(j t):=nick P.rate (notx m o j t)*‖R o j t‖
 have ht(j:Single N)(k:Trip m N):rent a (sift o j k)≤ d*Real.exp (P.rate* notx m o j k):=by
    unfold rent d; rw [←Real.exp_add]; exact Real.exp_monotone ((mul_le_mul_of_nonneg_left (sift_spec o j k).2.2.2 he.le).trans_eq (by unfold a; ring))
 have hp(j:Single N)(t:Trip m N)(x:Slot):rent a (sift o j t)*mine o j t R x≤ d*resolution m*X (j.1,x) t:=by
    apply (mul_le_mul_of_nonneg_right (ht ..) (minit o j t R x).positive).trans_eq; unfold X mine nick; rw [show notx m o (j.1,x) t=notx m o j t from rfl]; ring
 apply (sum_le_sum (fun j (_:j∈univ)=>sum_le_sum (fun i (_:i∈(univ: Finset (Trip m N × Slot)))=>hp j i.1 i.2))).trans; apply le_trans ?_ (mul_le_mul_of_nonneg_left (h.2.2 o) (mul_nonneg (by positivity) res_pos.le))
 have hz(j:HopK N): (∑ v:Trip m N×Slot,d*resolution m* X (j,v.2) v.1)=(d*resolution m)*∑ x:Slot,∑ t:Trip m N,X (j,x) t:=by rw [Fintype.sum_prod_type,sum_comm]; simp_rw [mul_sum]
 let c:=d*resolution m; change (∑ j: HopK N×Slot, ∑ z:Trip m N × Slot, d* resolution m* X (j.1,z.2) z.1) ≤ _; rw [Fintype.sum_prod_type]; change (∑ y:HopK N, ∑ _:Slot, ∑ z:Trip m N×Slot,d*resolution m*X (y,z.2) z.1) ≤ _; simp_rw [hz]; conv_rhs => unfold balance; rw [Fintype.sum_prod_type] -- tune
 simp only [sum_const,card_univ,slots,nsmul_eq_mul,Nat.cast_ofNat]; change (∑ j:HopK N,45*(c*∑ x:Slot,∑ t:Trip m N,X (j,x) t)) ≤ 45*d*resolution m*∑ j:HopK N,∑ x:Slot,∑ t: Trip m N,X (j,x) t; rw [←mul_sum,←mul_sum]; unfold c; exact le_of_eq (by ring)
variable (P:Pledge)
open Pledge
def cavilPrice (m:ℕ):= disperse ⟨P.rate/8,(45*Real.exp ((1+9*(m:ℝ))*P.rate/8)*resolution m)* P.price,div_pos P.pos (by norm_num),mul_pos (mul_pos (by positivity) res_pos) P.bought⟩ quota
theorem sifting (h:CardK N m R P.price P.rate) : (outlook N).Comes (cavilPrice P m) (cavil R):=by
 refine fundRows (A:=fun i j (k:Trip m N × Slot)=> sift i j k.1) (fun i j k=>minit i j k.1 R k.2) (row_paid R h) (outlook N).full Form.paid (fun i x j=>?_) -- full field inst dot?
 unfold cavil; rw [Matrix.of_apply,Matrix.sum_apply,Fintype.sum_prod_type]; apply sum_congr rfl; intro k _; rfl
lemma cavil_one (hp:0<m): cavil R 1=0:=by
 have hn : Nonempty (Fin m):= ⟨⟨0,hp⟩⟩; ext i j; rw [cavil,Matrix.of_apply,Matrix.sum_apply]; refine sum_eq_zero fun t _=>?_ ; rw [mold,Matrix.mul_apply]; exact sum_eq_zero fun k _=> mul_eq_zero.mpr (Or.inl ((R i (j.1,k) t).map_coord_zero (Classical.arbitrary _) (silt_0 ..))) -- tune
end Sifting
end YM.CF.BPress.Spin
