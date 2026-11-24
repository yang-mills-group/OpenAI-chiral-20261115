import YM.SU5.FiniteGaugeData.Largo.Inley
set_option linter.unusedSimpArgs false
set_option autoImplicit false
set_option maxHeartbeats 320000
noncomputable section
namespace YM.CF.Window.Largo
open Function Filter Lattice Metric Complex Finset Laurent Next.Free Bloch Fir Lat MeasureTheory Fock Rush
open scoped Topology BigOperators Pointwise ENNReal Matrix Matrix.Norms.L2Operator MatrixOrder InnerProductSpace ComplexOrder Kronecker
attribute [local instance] opCStarAlgebra
variable {N M : Side}{h d l w D r k v:ℕ}{σ C:ℝ}{b:Bool}
section area
variable {I:Finset ℤ}
abbrev foyerTip(d v:ℕ): Finset Tip:= Fintype.piFinset fun _=> Ico (d:ℤ) ((v:ℤ)-d)
def portal(d v:ℕ)(I:Finset ℤ): Finset Cover:= ((foyerTip d v) ×ˢ I).image meet
abbrev LodgeP(d v r:ℕ): Finset Cover:= portal d v (Icc (-(r:ℤ)) (r:ℤ))
abbrev marginA(r:ℕ):ℕ:=2*r+1
lemma foyer_card : (foyerTip d v).card=(v-2*d)^3:=by unfold foyerTip; rw [Fintype.card_piFinset,prod_const,card_univ,show Fintype.card Tang=3 from rfl,Int.card_Ico]; congr 1; omega
lemma portal_card(d v:ℕ)(I:Finset ℤ): (portal d v I).card= (v-2*d)^3*I.card:=by unfold portal; rw [card_image_of_injective _ meet.injective, card_product,foyer_card]
lemma LodgeP_card(d v r:ℕ): (LodgeP d v r).card=(v-2*d)^3*marginA r:=by rw [LodgeP,portal_card,Int.card_Icc]; unfold marginA; congr 1; omega
lemma porter (x:Cover): x∈portal d v I↔ (∀ j:Tang,(d:ℤ) ≤ back x j ∧ back x j < (v:ℤ)-d) ∧ x 3∈ I:=by
 unfold portal
 change x ∈ Finset.image meet.toEmbedding _ ↔ _; rw [←map_eq_image, mem_map_equiv]
 simp [foyerTip,Fintype.mem_piFinset,meet] -- tune
lemma parish(x:Cover): x∈ LodgeP d v r ↔ (∀ j:Tang,(d:ℤ) ≤ back x j ∧ back x j < (v:ℤ)-d) ∧ -(r:ℤ) ≤ x 3 ∧ x 3 ≤ r:=by rw [porter]; simp
lemma Walsh (p:h+h < M.val)(u:v≤ M.val)(X:ℕ): Waltz M (LodgeP X v h):=by
 intro i x j t g; have he:=parish _|>.1 x; have hv:=parish _|>.1 t; have hk(a:Axis): ((i a:Per M)=(j a:Per M)):=congr_fun g a; funext a; have hu:Tang→ℕ:= fun i=>0; -- placeholder
 apply wrap_d _ _ (hk a); have ht(i':Tang) := he.1 i'; unfold back at ht; refine Fin.lastCases (motive:=fun a=> (i a-j a).natAbs < ↑M) ?_ ?_ a
 · change (i 3-j 3).natAbs < M.val; omega
 intro i'; have he:=ht i'; have hv:=hv.1 i'; unfold back at hv; omega
lemma LodgeP_sub(p:h≤ w)(v:k≤d): LodgeP d r h⊆ LodgeP k r w:=fun i t=> by obtain ⟨a,b,c⟩:=parish _|>.mp t; apply (parish _).mpr; exact ⟨fun i=>by specialize a i; omega,by omega,by omega⟩
lemma edgeK(i:Cover)(p:i∈LodgeP d v h): ∀ j:Cover, j∈Lattice.box d→ i-j∈LodgeP 0 v (h+d):=by
 intro j t; obtain ⟨a,b,c⟩:=parish _|>.mp p; obtain ⟨A,B⟩:=box_test.mp t; apply (parish _).mpr; refine ⟨fun i'=>?_,?_,?_⟩
 · specialize a i'; specialize A i'.castSucc; specialize B i'.castSucc; unfold back at *; rw [Pi.sub_apply]; omega
 · specialize B (3:Axis); rw [Pi.sub_apply]; omega
 specialize A (3:Axis); rw [Pi.sub_apply]; omega
lemma Lodge_time {U:Finset ℤ}: wal N (portal 0 N.val U)= clock (U.image ((↑) : ℤ→Per N)):=by
 ext i; rw [wal]; simp only [mem_product,true_and,mem_univ, and_true, mem_image,clock,mem_filter]; constructor
 · rintro ⟨x,h,r⟩; exact ⟨x 3,(porter .. |>.mp h).2,congr_fun r 3⟩
 rintro ⟨u,v,t⟩; let f:= back i.1; let V:= back (natural i.1); let x:= full V u; refine ⟨x, (porter x).mpr ⟨?_,v⟩,?_⟩
 · intro j; have hU: (V j:ℤ)<N.val:=by unfold V back natural; have he:=ZMod.val_lt (i.1 j.castSucc); omega
   rw [show back x= V from back_home ..]; refine ⟨by unfold V back natural; exact Int.natCast_nonneg _,by simpa⟩
 funext j; apply Fin.lastCases (motive:=fun a=> wrap N x a = i.1 a) _ _ j; exact t; intro j; unfold wrap; change (x j.castSucc:Per N)=_; unfold x; rw [full_before V u j]; exact congr_fun (nat_true i.1) j.castSucc
lemma Lodge_timeB : wal N (LodgeP 0 N.val h) = Aeons N h:= Lodge_time
-- Need strips at any period. C pays seats.
abbrev Legion (l D:ℕ)(b:Bool): Finset ℤ:= (range D).image (instant l b)
abbrev Opera (l D v:ℕ)(b:Bool): Finset Cover:= portal 0 v (Legion l D b)
lemma operaE(h:l+D≤r): Opera l D v b⊆ LodgeP 0 v r:=by
 intro i t; obtain ⟨x,y⟩:=porter i|>.mp t; obtain ⟨y,z,p⟩:=mem_image.mp y; have ht:=instant_pay (l:=l) (b:=b) (mem_range.mp z); exact (parish i).mpr ⟨x,by omega,by omega⟩
lemma OperaT : wal N (Opera l D N.val b)= seats N l D b:=by rw [Opera,Lodge_time]; unfold Legion seats Whist; rw [image_image]; rfl -- tune
lemma opera_card : (Opera l D v b).card=v^3*D:=by rw [Opera,portal_card]; simp [Legion,card_image_of_injective _ (floorMono _ _)]
abbrev WalP (N:Side)(S: Finset Cover)(U: Finset SpinIdx): Finset (Mini N):= S.image (wrap N) ×ˢ U
abbrev WalL(N:Side)(S:Finset Cover): Finset (Mini N):= WalP N S plusHalfᶜ
abbrev WalU(N:Side)(S:Finset Cover):Finset (Mini N):= WalP N S plusHalf
lemma pickWal(T:Finset Cover): WalL N T=wal N T ∩ scel N:=by ext; simp [WalL,scel,wal,ruddy,WalP]
lemma payWal (T:Finset Cover): WalU N T=wal N T∩ ruddy N:=by ext; simp [WalU,wal,ruddy,WalP]
lemma Wal_species : Pavilion N l D b=WalU N (Opera l D N.val b) ∧ TerraceG N l D b= WalL N (Opera l D N.val b):=by rw [pickWal,payWal,OperaT]; exact ⟨rfl,rfl⟩
lemma portal_loss (h:2*d ≤ N.val)(p:r+r<N.val) : let U:=wal N (LodgeP 0 N.val r)\ wal N (LodgeP d N.val r); U.card ≤ 6*d*(N.val^2)*marginA r*4 :=by
 intro U; let n:=N.val; let S:=LodgeP 0 N.val r; let T:=LodgeP d N.val r; let A:= n^3; let B:= (n-2*d)^3; have he(d:ℕ):(wal N (LodgeP d n r)).card=(n-2*d)^3*marginA r*4:=by rw [wal,card_product, card_image_of_injOn (Walsh p le_rfl d),LodgeP_card]; rfl
 unfold U; rw [card_sdiff_of_subset (product_subset_product (image_mono _ (LodgeP_sub le_rfl (Nat.zero_le _))) (le_refl _)), he 0, he d, Nat.mul_zero,Nat.sub_zero];
 have hy:A ≤ B+6*d*n^2:=by
    let m:= n-2*d; have hx':m≤n:=by unfold m; omega
    have hx:m+2*d=n:= Nat.sub_add_cancel h; unfold A; change n^3 ≤ m^3+_
    calc
     n^3 = m^3+(n-m)*(n^2+n*m+m^2):=by set t:=n-m with ht; have hx':t+m=n:= Nat.sub_add_cancel hx'; rw [←hx']; ring
     _ ≤ m^3+6*d*n^2:=(by rw [show n-m=2*d from (by omega)]; have h2:m^2 ≤ n^2:= pow_le_pow_left' hx' _; nlinarith only [h2,Nat.mul_le_mul_left d h2,Nat.mul_le_mul_left (d*n) hx'])
 rw [tsub_le_iff_right]; change A * _*_≤6*d*n^2*marginA r*4+ B*_ * _; refine (Nat.mul_le_mul_right 4 (Nat.mul_le_mul_right (marginA r) hy)).trans_eq ?_; ring
end area
-- Patch density criterion. force N=24*K. choice possible!. 
namespace Curtain
variable {k:ℕ}
def plank (d:ℕ)(N:Side)(i:Tang→Fin d):Stereo N:= fun j=> ↑(4*d+(i j).val)
abbrev platter (N:Side)(v:ℕ): Finset (Stereo N):= univ.image (plank v N)
variable (p:N.val=24*k)
include p
lemma plank_val (i:Tang→Fin k)(j:Tang): (plank k N i j).val=4*k+(i j).val:=by
 apply ZMod.val_natCast_of_lt; have he:=(i j).isLt; omega
lemma plank_in : Injective (plank k N):= by intro i j v; funext a; apply Fin.ext; have h:= congrArg ZMod.val (congr_fun v a); rw [plank_val p,plank_val p] at h; omega
lemma platterC : (platter N k).card=k^3:=by unfold platter; rw [card_image_of_injective _ (plank_in p),card_univ, Fintype.card_pi_const,Fintype.card_fin]
lemma platterA : Hired (platter N k):=by
 intro i v j; obtain ⟨i,o,rfl⟩:= mem_image.mp v; let f:= plank k N i j; have hu:= plank_val p i j; let z:= (2*(f.val:ℝ)+1)/(N.val:ℝ); have hn:= nPos N; have hx:z≤1/2:=by
    unfold z; rw [_root_.div_le_div_iff₀ hn (by norm_num)]; have hZ: f.val+1 ≤ 5*k := by have ht:= (i j).isLt; unfold f; omega
    have hP:(f.val:ℝ)+1 ≤ 5*k:=by exact_mod_cast hZ; -- semicolon need newline
    rw [show (N.val:ℝ)=((24*k:ℕ):ℝ) from Nat.cast_inj.mpr p]; push_cast; nlinarith only [hP,Nat.cast_nonneg (α:=ℝ) k]
 have hP:1/3≤z:=by
    unfold z; rw [_root_.div_le_div_iff₀ (by norm_num) hn]; have hQ:4*k ≤ f.val:=by unfold f; omega
    have hd: 4*(k:ℝ) ≤ f.val:=by exact_mod_cast hQ
    rw [show (N.val:ℝ)=((24*k:ℕ):ℝ) from Nat.cast_inj.mpr p]; push_cast; nlinarith
 have ha:1≤ z*Real.pi∧ z*Real.pi≤2:=⟨by nlinarith only [Real.pi_gt_three,mul_le_mul_of_nonneg_right hP Real.pi_pos.le],by nlinarith only [Real.pi_lt_four,mul_le_mul_of_nonneg_right hx Real.pi_pos.le]⟩
 rw [show badge (plank k N i) j=z*Real.pi from (by change Lat.principal f=_; rw [Lat.principal,if_pos]; rfl; change z*Real.pi≤_; linarith [Real.pi_gt_three])]; exact ha
end Curtain
end YM.CF.Window.Largo
