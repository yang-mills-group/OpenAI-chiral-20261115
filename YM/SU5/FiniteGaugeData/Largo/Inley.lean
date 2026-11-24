import YM.SU5.FiniteGaugeData.Largo.Core
import YM.CF.Scroll.Pent
set_option linter.unusedSimpArgs false
set_option autoImplicit false
set_option maxHeartbeats 320000
noncomputable section
namespace YM.CF.Window.Largo
open Function Filter Lattice Metric Complex Finset Laurent Next.Free Bloch Fir Lat MeasureTheory Fock Rush
open scoped Topology BigOperators Pointwise ENNReal Matrix Matrix.Norms.L2Operator MatrixOrder InnerProductSpace ComplexOrder Kronecker
attribute [local instance] opCStarAlgebra
-- contiguous Laurent brick embeddings. Column signs EXACT; can freely cross temporal seam in transfer. Helpers for WPX Relight. X=Mxd. wind comparison. wrap Edge strips.
variable {N M : Side}{f:Cover→Op SpinIdx}{h d:ℕ}{σ C:ℝ}
local notation "ω"=> wrap
abbrev wal (N:Side)(S:Finset Cover):Finset (Mini N):= (S.image (wrap N)) ×ˢ univ
abbrev Waltz (N:Side)(S:Finset Cover):= Set.InjOn (wrap N) S
variable {S T U:Finset Cover}
abbrev sew₁ (N:Side)(v:Cover):ℂ:= fee (periods N v)
lemma sew_fee₁(x t:Cover): wind (wrap N x) t*sew₁ N x=sew₁ N (x+t):=by
 unfold wind sew₁; rw [← Scroll.dues]; apply congrArg (fee) ; apply nsmul_right_injective (M:=Cover) N.property.ne'; let v:=natural (wrap N x)+t; change N.val • _=N.val • periods N (x+t); rw [smul_add]; have hz:wrap N v= wrap N (x+t):=by unfold v; rw [map_add,map_add,nat_true]
 have he:= carrying N v; have hg:=carrying N (x+t); have hf:=carrying N x; rw [hz] at he; change N.val • periods N v + N.val • periods N x=_; unfold v at *; linear_combination (norm:=abel) he-hg+hf
namespace Waltz
set_option quotPrecheck false
variable (p:Waltz N S)(t:Waltz M S)(g:T⊆S)
abbrev Beam (S:Finset Cover):= ↑S × SpinIdx
def Born(N:Side)(S:Finset Cover)(x:Beam S):Mini N:= (wrap N x.1.val,x.2)
def inp(N:Side)(S:Finset Cover): Ruler (Mini N) (Beam S):= grip (Born N S) (fun i:Beam S=> sew₁ N i.1.val)
lemma birth_subset (p:T⊆ S)(x:Beam T): Born N T x ∈ wal N S:= mem_product.mpr ⟨mem_image_of_mem (wrap N) (p x.1.property),mem_univ _⟩
include p
lemma inject_here: Injective (Born N S):= by intro i j h; exact Prod.ext (Subtype.ext (p i.1.property j.1.property (congrArg (·.1) h))) (congrArg (·.2) h)
lemma theta_t : (inp N S)ᴴ*inp N S=1:=by apply grip_clean _ _ p.inject_here; intro i; rw [show star (sew₁ N ↑i.1)=_ from fee_real _]; exact fee_one _
lemma tendril : inp N S*(inp N S)ᴴ=cutM (wal N S):=by
 let f:= Born N S; let V:= inp N S; have hg(x:Mini N)(v:x∈wal N S):∃ i:Beam S,f i=x:=by obtain ⟨h,u,r⟩:= mem_image.mp (mem_product.mp v).1; exact ⟨(⟨h,u⟩,x.2),Prod.ext r rfl⟩
 have hz (k:Mini N)(v:k∉wal N S)(x:Beam S): k≠f x:=fun h=> v (h ▸ birth_subset (le_refl _) x)
 ext i j; rw [Matrix.mul_apply]; unfold inp; simp_rw [Matrix.conjTranspose_apply]; by_cases h:i∈ wal N S; swap; · unfold grip; have hp:=hz _ h; unfold f at hp; simp only [hp,not_false_eq_true,cutM,Matrix.diagonal_apply,Matrix.of_apply,h,zero_mul,sum_const_zero,↓reduceIte,ite_self] -- hz f not Born
 obtain ⟨l,rfl⟩:= hg i h; rw [sum_eq_single l];
 · by_cases v:j=f l; · subst j; unfold grip; simp only [Matrix.of_apply,cutM,Matrix.diagonal_apply_eq,h,show f l=Born N S l from rfl, show Born N S l ∈ wal N S from h,↓reduceIte]; rw [show star (sew₁ N ↑l.1)=sew₁ N ↑l.1 from fee_real _, show sew₁ N ↑l.1 * sew₁ N ↑l.1=1 from fee_one _]; -- simp tune
   simp [grip,f,h,Ne.symm v,v,cutM] -- orientations
 · intro b _ t; have he: f l≠Born N S b:=p.inject_here.ne (Ne.symm t); unfold grip; simp [he]
 simp
include g
lemma ink (x:Beam S): Born N S x∈ wal N T ↔ (x.1.val∈ T) := by
 constructor; · intro h; obtain ⟨v,x',e⟩:= mem_image.mp (mem_product.mp h).1; exact p (g x') x.1.property e ▸ x'
 intro h; exact mem_product.mpr ⟨mem_image_of_mem _ h,mem_univ _⟩
lemma inp_inc (U:Finset SpinIdx): cutM ((T.image (wrap N))×ˢ U)*inp N S=inp N S * cutM (univ.filter (fun x:Beam S=> x.1.val∈T ∧ x.2∈U)):=by
 ext i j; rw [compass,compass']; by_cases h:i= Born N S j; swap; · simp [inp,grip,h]
 subst i; let A:= T.image (wrap N); have he (v:Beam S): (Born N S v).1∈ A ↔ v.1.val∈ T:=by have h:= p.ink g v; simpa [wal,A,mem_product] using h
 simp only [mem_product,show ω N j.1.val∈ (T.image (wrap N)) ↔ j.1.val ∈ T from he j, Born,mem_filter,mem_univ,true_and] -- tune
omit g p
def TauP (N M:Side)(S:Finset Cover) : Ruler (Mini M) (Mini N):= inp M S*(inp N S)ᴴ
local notation "Y"=> TauP N M S
lemma spinCommT (V:Finset SpinIdx) : cutM (univ ×ˢ V)*inp N S=inp N S * cutM (univ ×ˢ V):=by ext i j; rw [compass,compass']; by_cases h:i=Born N S j ; simp [h,Born]; simp [h,inp,grip]
lemma tauSpin(U:Finset SpinIdx): cutM (univ ×ˢ U)*Y=Y*cutM (univ ×ˢ U):=by unfold TauP; rw [←Matrix.mul_assoc, spinCommT,Matrix.mul_assoc, ←cutM_adj (univ ×ˢ U), ←Matrix.conjTranspose_mul,←spinCommT]; rw [Matrix.conjTranspose_mul,cutM_adj,Matrix.mul_assoc] -- Fintype bogus
include p t
lemma tauIs : Yᴴ*Y=cutM (wal N S):=by unfold TauP; rw [Matrix.conjTranspose_mul, Matrix.mul_assoc,←Matrix.mul_assoc _ (inp M S),t.theta_t,Matrix.one_mul,Matrix.conjTranspose_conjTranspose,p.tendril]
lemma tauBudget : ‖Y‖ ≤ 1:= (Matrix.l2_opNorm_mul ..).trans (mul_le_one₀ (grip_pay _ t.theta_t) (norm_nonneg _) ((Matrix.l2_opNorm_conjTranspose ..).trans_le (grip_pay _ p.theta_t)))
include g
lemma tauCut (U:Finset SpinIdx): cutM ((T.image (wrap M)) ×ˢ U)*Y=Y*cutM ((T.image (wrap N)) ×ˢ U):=by
 unfold TauP; let X:= cutM (univ.filter fun i:Beam S=> i.1.val∈T ∧ i.2∈U); rw [←Matrix.mul_assoc, inp_inc t g U, Matrix.mul_assoc, Matrix.mul_assoc]; rw [show cutM (T.image (wrap N) ×ˢ U)=_ from (cutM_adj _).symm,←Matrix.conjTranspose_mul, inp_inc p g U, Matrix.conjTranspose_mul,cutM_adj]
omit p t
variable (p': ∀ v:Cover, v∈T→∀ i:Cover,i∈Lattice.box d→ v-i∈S)
include p'
abbrev wrist (S T:Finset Cover) : Finset (Beam S):= univ.filter fun x:Beam S=> x.1.val∈T ∧ x.2∈ (univ:Finset SpinIdx)
lemma wagonTraced {x:Cover}(z:x∈box d)(i j:Mini N)(e:j∈ wal N T)(v: wagon N f x i j ≠0): i∈ wal N S:=by
 obtain ⟨b,h,t⟩:= mem_image.mp (mem_product.mp e).1; refine mem_product.mpr ⟨?_,mem_univ _⟩; refine mem_image.mpr ⟨b-x,p' b h _ z,?_⟩; rw [map_sub,t]; rw [sub_eq_iff_eq_add]; -- exact hop
 exact Eq.symm (not_not.mp (fun h=> v (by rw [wagon_app]; exact if_neg h))) -- transparent pairs eta
lemma wagonT_pay {x:Cover}(z:x∈box d): cutM (wal N S)* wagon N f x *cutM (wal N T)= wagon N f x *cutM (wal N T):=by
 ext i j; rw [compass',compass',compass]; by_cases e:j∈ wal N T; swap; · rw [if_neg e, if_neg e]
 by_cases v:wagon N f x i j=0; simp [e,v]; have hz:=wagonTraced g p' z i j e v; rw [if_pos e,if_pos hz,if_pos e]
include p
lemma wagon_inc {x:Cover}(v:x∈Lattice.box d) (i j:Beam S):
 ((inp N S)ᴴ*wagon N f x*inp N S*cutM (wrist S T)) i j= if j.1.val∈T ∧ i.1.val=j.1.val-x then f x i.2 j.2 else 0:=by
 let b:=i.1.val; let y:= j.1.val; rw [compass']; by_cases h:y∈T; swap;
 · rw [if_neg (by simpa [wrist] using h)]; exact (if_neg (fun t=>h t.1)).symm
 let V:= Born N S; have he:ω N b+ ω N x=ω N y ↔ b=y-x:=by rw [←eq_sub_iff_add_eq,← map_sub]; exact ⟨fun t=>p i.1.property (p' _ h _ v) t,fun k=>by rw [k]⟩
 rw [if_pos (by simpa [wrist] using h), inp,on_grip,grip_off,wagon_app,show star (sew₁ N i.1.val) =_ from fee_real _];
 change sew₁ N b * (if ω N b+ _= ω N y then _ else _)*sew₁ N y=if y∈T ∧ b=y-x then f x i.2 j.2 else 0; by_cases a:b=y-x;
 · let A:= f x i.2 j.2; rw [if_pos (he.mpr a),if_pos ⟨h,a⟩]; have hj:= sew_fee₁ (N:=N) b x; rw [eq_sub_iff_add_eq.mp a] at hj; change sew₁ N b * (wind (ω N b) x * A)*sew₁ N y=A; rw [←mul_assoc, mul_comm _ (wind _ _), hj, mul_right_comm, show sew₁ N y* sew₁ N y=1 from fee_one _,one_mul]
 rw [if_neg (mt he.mp a),if_neg (fun r=>a r.2),mul_zero,zero_mul]
include t
lemma wagonEq {x:Cover}(v:x∈box d):
     wagon M f x * Y * cutM (wal N T)= Y * wagon N f x * cutM (wal N T):=by
 let U:=inp N S; let V:=inp M S; let A:=cutM (wal N T); let L:=cutM (wrist S T); let D(i):= wagon i f x; let B':= cutM (wal M T); have hy:Vᴴ*D M*V*L=Uᴴ*D N*U*L:=by ext i j; rw [p.wagon_inc g p' v i j,t.wagon_inc g p' v i j] -- tune
 have he:A*U=U* L:=inp_inc p g _; have hf: B'*V= V*L:=inp_inc t g _; have hL:A=(U*Uᴴ)*A:=by rw [p.tendril,cutM_hold,inter_eq_right.mpr]; exact product_subset_product (image_mono _ g) (le_refl _)
 have hp:Uᴴ*A=L*Uᴴ:=by nth_rw 1 [←show Aᴴ=A from cutM_adj _]; rw [←Matrix.conjTranspose_mul,he,Matrix.conjTranspose_mul,show Lᴴ=L from cutM_adj _]
 have htV:(V*Vᴴ)*(D M*V*L)=D M*V*L:=by
    rw [t.tendril, Matrix.mul_assoc _ V, ←hf,←Matrix.mul_assoc,←Matrix.mul_assoc,←Matrix.mul_assoc, wagonT_pay g p' v]; -- tune
 change D M*(V*Uᴴ)*A=(V*Uᴴ)*D N*A; calc
    _ =(D M*V*L)*Uᴴ:= by simp_rw [Matrix.mul_assoc]; rw [hp]
    _ = (V*(Uᴴ*D N*U*L))*Uᴴ:=by rw [←hy]; apply congrArg (·*Uᴴ); simp_rw [Matrix.mul_assoc] at htV ⊢; exact htV.symm; -- tune by assoc with V and D (current puzzle)
    _ = _:= by rw [hL]; simp_rw [Matrix.mul_assoc]; rw [hp] -- orientation
lemma plateHEq (V:Momentum→Op SpinIdx) :
   plateH V M d*Y*cutM (wal N T)= Y*plateH V N d*cutM (wal N T):=by
 unfold plateH; simp_rw [Matrix.sum_mul,Matrix.mul_sum,Matrix.sum_mul]; exact sum_congr rfl (fun i e=> wagonEq p t g p' e)
end Waltz
end YM.CF.Window.Largo
