import YM.CF.Scroll.Harpy
set_option autoImplicit false
noncomputable section
namespace YM.CF.Scroll
open Function Filter Matrix NormedSpace Finset Fock Lat Lattice Rush Cube Next.Free Laurent Fir Bloch SU Drapes Peaks Dial Tulip
open scoped Matrix.Norms.L2Operator Matrix Topology MatrixOrder BigOperators Kronecker
attribute [local instance] opCStarAlgebra
variable {b r:Bool}{N: Side}(a:Shape)(t:ColorT b)(U:UNI SpinIdx)(h: JetS a.s b r U)(x:Bkg (More N))(j:ℕ)(hp:1≤ j)(M: Male)
def swapX {I:Type*}[DecidableEq I] (b:Bool)(A:Op I):= if b then 1-A else A
def fireX(N:Side)(K:Cover→Op SpinIdx)(U:Bkg (More N)):=dialW N K (profile U)
private def oX(k:Cover): Op SpinIdx:=if k=0 then 1 else 0
lemma oX_r : Reads oX 1 :=⟨fun i j=> (by apply summable_of_hasFiniteSupport; apply (Set.finite_singleton (0:Cover)).subset; intro l h; by_contra x; simp at x; simp [support,oX,x] at h), fun p h i j=>by unfold Laurent.read; rw [tsum_eq_single 0]; simp [oX]; intro z h; simp [oX,h]⟩ -- tune
lemma dis_c (F:Cover→Op SpinIdx)(A:Momentum→ Op SpinIdx)(h: Reads F A) : Reads (fun x=> oX x-F x) (fun x=> 1-A x):=by
 refine ⟨fun i j=> ?_,fun p g i j=>?_⟩
 · simp only [Matrix.sub_apply]; apply Summable.of_nonneg_of_le _ _ ((oX_r.sumK i j).add (h.sumK i j)); intro; exact norm_nonneg _; intro; exact norm_sub_le ..
 simp only [Laurent.read,Matrix.sub_apply,smul_sub]; let f:=fun x:Cover=>mode p x • oX x i j; let v:=fun x:Cover=>mode p x • F x i j; have he:Summable f:=by apply Summable.of_norm; unfold f; simp only [norm_smul,mode_real _ _ g.1,one_mul]; exact oX_r.sumK ..
 have hv: Summable v:=by apply Summable.of_norm; unfold v; simp only [norm_smul,mode_real _ _ g.1,one_mul]; exact h.sumK ..
 change (∑' k,(f k-v k))=_; rw [he.tsum_sub hv, show (∑' k,f k)=(1:Op SpinIdx) i j from oX_r.readK p g i j,show (∑' k,v k)=_ from h.readK p g i j]
include hp
lemma diff_b(u:Bool): tub (bent false j M.val)=fun x=>oX x-tub (bent true j M.val) x:= Reads_u _ _ _ (cBar j M.val false hp M.property) (dis_c _ _ (cBar j M.val true hp M.property))
omit hp
lemma slider_diff(F G:Cover→Op SpinIdx)(z:Cover)(i k:SpinIdx)(o:Lattice.Order): slider N z o i k (F z i k-G z i k) (profile x)= slider N z o i k (F z i k) (profile x)-slider N z o i k (G z i k) (profile x):=by
 simp only [slider,mul_sub,sub_smul,←sum_sub_distrib]; apply sum_congr rfl; intro j _; ext ⟨e,l⟩ ⟨t,m⟩; by_cases h:e=(j,i)∧ t=(j+wrap N z,k)<;>simp [panel,h]
lemma reserve_flip : dialW N oX (profile x)=1:=by
 have hp (o:Lattice.Order): tourP N oX o (profile x) = tourP N oX o 1:=by
   have ht(T:Chin N)(z:Cover)(i j:SpinIdx)(h:z≠0):slider N z o i j (oX z i j) T=0:=by simp [slider,oX,h]; apply sum_eq_zero; intro; intro; ext; unfold panel; simp
   have he(i k:SpinIdx) (n:ℕ): slider N (names n) o i k (oX (names n) i k) (profile x)=slider N (names n) o i k (oX (names n) i k) 1:=by by_cases h:names n=0; simp [h,slider,leap,Tulip.track]; exact (ht _ _ i k h).trans (ht _ _ i k h).symm
   simp only [tourP,he]
 unfold dialW; simp only [hp]; change dialW N oX 1=_; rw [dial_id N oX oX_r.sumK,cart_traded oX_r]; change plates N (fun _=>1) ⊗ₖ _ = _; rw [piles1,Matrix.one_kronecker_one]
include hp
lemma subsist : dialW N (tub (bent false j M.val)) (profile x)=1-reserveP N j M.val (profile x):=by
 let A:=tub (bent true j M.val); let H:=cBar j M.val true hp M.property; rw [diff_b j hp M false, ← reserve_flip x];
 change dialW _ _ _= _-dialW N A _; have he(o:Lattice.Order):tourP N (fun z=>oX z-A z) o (profile x)=tourP N oX o (profile x)-tourP N A o (profile x):=by
    simp only [tourP,Matrix.sub_apply,slider_diff, ←sum_sub_distrib]; apply sum_congr rfl; intro i _; apply sum_congr rfl; intro k _; rw [Summable.tsum_sub]; exact (summ_l x _ _ oX_r.sumK i k).comp_injective names.injective; exact (summ_l x _ _ H.sumK i k).comp_injective names.injective
 unfold dialW; rw [← smul_sub,← sum_sub_distrib]; congr 1; apply sum_congr rfl; intro o _; exact he _
include h
lemma art_X: sings b (prepU a U t N) (art N j M.val (profile x))=hush r (art N j M.val (profile (stir t a x))):=by
 have he:= cBar j M.val (r.xor true) hp M.property; let W:=prepU a U t N
 have hv: sings b W (reserveP N j M.val (profile x))=dialW N (tub (bent (r.xor true) j M.val)) (profile (stir t a x)):= dial_r a U t x _ _ (cBar j M.val true hp M.property).sumK (fun i=>bent_v _ _ _ _ h M.val M.property i j true hp) he.sumK
 simp only [art,pale,ice_pr]; simp only [singT,win_l,win_a,win_s,win_i,map_star,map_sub,map_add,map_one,show (twist (prepU a U t N)) (windX b (reserveP N j M.val (profile x)))= _ from hv]; cases r; rfl
 change  _= -(reserveP _ _ _ _ + star _-1); rw [show true.xor true=false from rfl, subsist _ j hp M,star_sub,star_one]; abel
omit h
lemma radiance : ∃ e:ℝ,0<e∧∃ k:ℕ,∀ N:Side,k≤N.val→∀ x:Bkg (More N),Guard x e→Safe (dome N (profile x)) ∧ ∀ M:Male,Safe (art N j M.val (profile x)):=by
 obtain ⟨e,p,w,H⟩:= (painter j hp).2; let t:=min e ((1/60:ℝ)/256); have ht:0<t:=lt_min p (by norm_num); refine ⟨t,ht,w,fun N g U h=> ⟨Broad ht (by have hv:t≤ _:=min_le_right ..; linarith) U h,fun i=> H i N g U (h.shrink (min_le_left ..))⟩⟩
omit hp
lemma fires_h {I:Type*}[Fintype I][DecidableEq I][Nonempty I](p r:Bool)(U:UNI I)(A B:Op I)(s:Safe A)(t: Safe B)(e:sings p U A=hush r B): sings p U (projector A)=swapX r (projector B):=by
 have ht : sings p U (projector A)= projector (sings p U A):=by cases p; exact projector_twist s U; change twist U (cc (projector A))=_; rw [← projector_cc s,projector_twist s.conjugated]; rfl
 rw [ht,e]; cases r; rfl; exact Mir.minusP t
include hp h
lemma funde_f(e:ℝ)(H:∀ x:Bkg (More N),Guard x e→ Safe (dome N (profile x))∧∀ M:Male,Safe (art N j M.val (profile x)))(g:Guard x e) : sings b (prepU a U t N) (funde j M N (profile x))= swapX r (funde j M N (profile (stir t a x))):=by
 let hx:= H x g; let hv:= H (stir t a x) (keepC t a x e g); unfold funde; split
 · apply fires_h _ _ _ _ _ hx.1 hv.1; rw [dome_kernel,dome_kernel,wingX, shutH _ _ _ h]; cases r; rfl; exact map_neg ..
 exact fires_h _ _ _ _ _ (hx.2 M) (hv.2 M) (art_X _ _ _ h x j hp M)
end YM.CF.Scroll
